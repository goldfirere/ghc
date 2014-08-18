
%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

A ``lint'' pass to check for Core correctness

\begin{code}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fprof-auto #-}

module CoreLint ( lintCoreBindings, lintUnfolding, lintExpr ) where

#include "HsVersions.h"

import CoreSyn
import CoreFVs
import CoreUtils
import Bag
import Literal
import DataCon
import TysWiredIn
import TysPrim
import Var
import VarEnv
import VarSet
import Name
import Id
import PprCore
import ErrUtils
import Coercion
import SrcLoc
import Kind
import Type
import TyCoRep
import TyCon
import CoAxiom
import BasicTypes
import StaticFlags
import ListSetOps
import PrelNames
import Outputable
import FastString
import Util
import OptCoercion ( checkAxInstCo )
import Control.Monad
import MonadUtils
import Data.Maybe
import Pair
\end{code}

Note [GHC Formalism]
~~~~~~~~~~~~~~~~~~~~
This file implements the type-checking algorithm for System FC, the "official"
name of the Core language. Type safety of FC is heart of the claim that
executables produced by GHC do not have segmentation faults. Thus, it is
useful to be able to reason about System FC independently of reading the code.
To this purpose, there is a document core-spec.pdf built in docs/core-spec that
contains a formalism of the types and functions dealt with here. If you change
just about anything in this file or you change other types/functions throughout
the Core language (all signposted to this note), you should update that
formalism. See docs/core-spec/README for more info about how to do so.

Note [check vs lint]
~~~~~~~~~~~~~~~~~~~~
This file implements both a type checking algorithm and also general sanity
checking. For example, the "sanity checking" checks for TyConApp on the left
of an AppTy, which should never happen. These sanity checks don't really
affect any notion of type soundness. Yet, it is convenient to do the sanity
checks at the same time as the type checks. So, we use the following naming
convention:

- Functions that begin with 'lint'... are involved in type checking. These
  functions might also do some sanity checking.

- Functions that begin with 'check'... are *not* involved in type checking.
  They exist only for sanity checking.

Issues surrounding variable naming, shadowing, and such are considered *not*
to be part of type checking, as the formalism omits these details.

%************************************************************************
%*                                                                      *
\subsection[lintCoreBindings]{@lintCoreBindings@: Top-level interface}
%*                                                                      *
%************************************************************************

Checks that a set of core bindings is well-formed.  The PprStyle and String
just control what we print in the event of an error.  The Bool value
indicates whether we have done any specialisation yet (in which case we do
some extra checks).

We check for
        (a) type errors
        (b) Out-of-scope type variables
        (c) Out-of-scope local variables
        (d) Ill-kinded types

If we have done specialisation the we check that there are
        (a) No top-level bindings of primitive (unboxed type)

Outstanding issues:

    --
    -- Things are *not* OK if:
    --
    --  * Unsaturated type app before specialisation has been done;
    --
    --  * Oversaturated type app after specialisation (eta reduction
    --   may well be happening...);


Note [Linting type lets]
~~~~~~~~~~~~~~~~~~~~~~~~
In the desugarer, it's very very convenient to be able to say (in effect)
        let a = Type Int in <body>
That is, use a type let.   See Note [Type let] in CoreSyn.

However, when linting <body> we need to remember that a=Int, else we might
reject a correct program.  So we carry a type substitution (in this example
[a -> Int]) and apply this substitution before comparing types.  The functin
        lintInTypeWithValues :: Type -> LintM Type
returns a substituted type; that's the only reason it returns anything.

When we encounter a binder (like x::a) we must apply the substitution
to the type of the binding variable.  lintBinders does this.

For Ids, the type-substituted Id is added to the in_scope set (which
itself is part of the TCvSubst we are carrying down), and when we
find an occurrence of an Id, we fetch it from the in-scope set.

\begin{code}
lintCoreBindings :: [Var] -> CoreProgram -> (Bag MsgDoc, Bag MsgDoc)
--   Returns (warnings, errors)
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintCoreBindings local_in_scope binds
  = initL $
    addLoc TopLevelBindings        $
    addInScopeVars local_in_scope  $
    addInScopeVars binders         $
        -- Put all the top-level binders in scope at the start
        -- This is because transformation rules can bring something
        -- into use 'unexpectedly'
    do { checkL (null dups) (dupVars dups)
       ; checkL (null ext_dups) (dupExtVars ext_dups)
       ; mapM lint_bind binds }
  where
    binders = bindersOfBinds binds
    (_, dups) = removeDups compare binders

    -- dups_ext checks for names with different uniques
    -- but but the same External name M.n.  We don't
    -- allow this at top level:
    --    M.n{r3}  = ...
    --    M.n{r29} = ...
    -- because they both get the same linker symbol
    ext_dups = snd (removeDups ord_ext (map Var.varName binders))
    ord_ext n1 n2 | Just m1 <- nameModule_maybe n1
                  , Just m2 <- nameModule_maybe n2
                  = compare (m1, nameOccName n1) (m2, nameOccName n2)
                  | otherwise = LT

    -- If you edit this function, you may need to update the GHC formalism
    -- See Note [GHC Formalism]
    lint_bind (Rec prs)         = mapM_ (lintSingleBinding TopLevel Recursive) prs
    lint_bind (NonRec bndr rhs) = lintSingleBinding TopLevel NonRecursive (bndr,rhs)
\end{code}

%************************************************************************
%*                                                                      *
\subsection[lintUnfolding]{lintUnfolding}
%*                                                                      *
%************************************************************************

We use this to check all unfoldings that come in from interfaces
(it is very painful to catch errors otherwise):

\begin{code}
lintUnfolding :: SrcLoc
              -> [Var]          -- Treat these as in scope
              -> CoreExpr
              -> Maybe MsgDoc   -- Nothing => OK

lintUnfolding locn vars expr
  | isEmptyBag errs = Nothing
  | otherwise       = Just (pprMessageBag errs)
  where
    (_warns, errs) = initL (addLoc (ImportedUnfolding locn) $
                            addInScopeVars vars            $
                            lintCoreExpr expr)

lintExpr :: [Var]               -- Treat these as in scope
         -> CoreExpr
         -> Maybe MsgDoc        -- Nothing => OK

lintExpr vars expr
  | isEmptyBag errs = Nothing
  | otherwise       = Just (pprMessageBag errs)
  where
    (_warns, errs) = initL (addLoc TopLevelBindings $
                            addInScopeVars vars     $
                            lintCoreExpr expr)
\end{code}

%************************************************************************
%*                                                                      *
\subsection[lintCoreBinding]{lintCoreBinding}
%*                                                                      *
%************************************************************************

Check a core binding, returning the list of variables bound.

\begin{code}
lintSingleBinding :: TopLevelFlag -> RecFlag -> (Id, CoreExpr) -> LintM ()
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintSingleBinding top_lvl_flag rec_flag (binder,rhs)
  = addLoc (RhsOf binder) $
         -- Check the rhs
    do { ty <- lintCoreExpr rhs
       ; lintBinder binder -- Check match to RHS type
       ; binder_ty <- applySubstTy binder_ty
       ; ensureEqTys binder_ty ty (mkRhsMsg binder (ptext (sLit "RHS")) ty)

        -- Check (not isUnLiftedType) (also checks for bogus unboxed tuples)
       ; checkL (not (isUnLiftedType binder_ty)
            || (isNonRec rec_flag && exprOkForSpeculation rhs))
           (mkRhsPrimMsg binder rhs)

        -- Check that if the binder is top-level or recursive, it's not demanded
       ; checkL (not (isStrictId binder)
            || (isNonRec rec_flag && not (isTopLevel top_lvl_flag)))
           (mkStrictMsg binder)

        -- Check that if the binder is local, it is not marked as exported
       ; checkL (not (isExportedId binder) || isTopLevel top_lvl_flag)
           (mkNonTopExportedMsg binder)
        -- Check that if the binder is local, it does not have an external name
       ; checkL (not (isExternalName (Var.varName binder)) || isTopLevel top_lvl_flag)
           (mkNonTopExternalNameMsg binder)

        -- Check whether binder's specialisations contain any out-of-scope variables
       ; mapM_ (lintBndrIdInScope binder) bndr_vars

       ; when (isStrongLoopBreaker (idOccInfo binder) && isInlinePragma (idInlinePragma binder))
              (addWarnL (ptext (sLit "INLINE binder is (non-rule) loop breaker:") <+> ppr binder))
              -- Only non-rule loop breakers inhibit inlining

      -- Check whether arity and demand type are consistent (only if demand analysis
      -- already happened)
      --
      -- Note (Apr 2014): this is actually ok.  See Note [Demand analysis for trivial right-hand sides]
      --                  in DmdAnal.  After eta-expansion in CorePrep the rhs is no longer trivial.
      --       ; let dmdTy = idStrictness binder
      --       ; checkL (case dmdTy of
      --                  StrictSig dmd_ty -> idArity binder >= dmdTypeDepth dmd_ty || exprIsTrivial rhs)
      --           (mkArityMsg binder)

       ; lintIdUnfolding binder binder_ty (idUnfolding binder) }

        -- We should check the unfolding, if any, but this is tricky because
        -- the unfolding is a SimplifiableCoreExpr. Give up for now.
   where
    binder_ty                  = idType binder
    bndr_vars                  = varSetElems (idFreeVars binder)

    -- If you edit this function, you may need to update the GHC formalism
    -- See Note [GHC Formalism]
    lintBinder var | isId var  = lintAndScopeVar var $ \_ -> (return ())
                   | otherwise = return ()

lintIdUnfolding :: Id -> Type -> Unfolding -> LintM ()
lintIdUnfolding bndr bndr_ty (CoreUnfolding { uf_tmpl = rhs, uf_src = src })
  | isStableSource src
  = do { ty <- lintCoreExpr rhs
       ; ensureEqTys bndr_ty ty (mkRhsMsg bndr (ptext (sLit "unfolding")) ty) }
lintIdUnfolding  _ _ _
  = return ()       -- We could check more
\end{code}

%************************************************************************
%*                                                                      *
\subsection[lintCoreExpr]{lintCoreExpr}
%*                                                                      *
%************************************************************************

\begin{code}
type InType      = Type
type InCoercion  = Coercion
type InVar       = Var
type InTyCoVar   = Var

type OutType     = Type -- Substitution has been applied to this,
                        -- but has not been linted yet
type OutKind     = Kind

type LintedType  = Type -- Substitution applied, and type is linted
type LintedKind  = Kind

type OutCoercion    = Coercion
type OutCoercionArg = CoercionArg

lintCoreExpr :: CoreExpr -> LintM OutType
-- The returned type has the substitution from the monad
-- already applied to it:
--      lintCoreExpr e subst = exprType (subst e)
--
-- The returned "type" can be a kind, if the expression is (Type ty)

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintCoreExpr (Var var)
  = do  { checkL (not (var == oneTupleDataConId))
                 (ptext (sLit "Illegal one-tuple"))

        ; checkL (isId var && not (isCoVar var))
                 (ptext (sLit "Non term variable") <+> ppr var)

        ; checkDeadIdOcc var
        ; var' <- lookupIdInScope var
        ; let ty = idType var'
        ; applySubstTy ty }

lintCoreExpr (Lit lit)
  = return (literalType lit)

lintCoreExpr (Cast expr co)
  = do { expr_ty <- lintCoreExpr expr
-- RAE       ; checkL (not (isReflCo co))
-- RAE                (ptext (sLit "Cast by Refl in expression:") <+> ppr e)
-- RAE This check fails, because of (at least) a failure to use mkCast in Specialise.specExpr
       ; co' <- applySubstCo co
       ; (_, k2, from_ty, to_ty, r) <- lintCoercion co'
       ; lintL (classifiesTypeWithValues k2)
               (ptext (sLit "Target of cast not # or *:") <+> ppr co)
       ; lintRole co' Representational r
       ; ensureEqTys from_ty expr_ty (mkCastErr expr co' from_ty expr_ty)
       ; return to_ty }

lintCoreExpr (Tick (Breakpoint _ ids) expr)
  = do forM_ ids $ \id -> do
         checkDeadIdOcc id
         lookupIdInScope id
       lintCoreExpr expr

lintCoreExpr (Tick _other_tickish expr)
  = lintCoreExpr expr

lintCoreExpr (Let (NonRec tv (Type ty)) body)
  | isTyVar tv
  =     -- See Note [Linting type lets]
    do  { ty' <- applySubstTy ty
        ; lintAndScopeVar tv $ \ tv_kind ->
    do  { addLoc (RhsOf tv) $ do { ty_kind <- lintType ty'
                                 ; ensureEqTys tv_kind ty_kind $
                                   mkKindErrMsg tv ty }
                -- Now extend the substitution so we
                -- take advantage of it in the body
        ; extendSubstL tv ty'       $
          addLoc (BodyOfLetRec [tv]) $
          lintCoreExpr body } }

lintCoreExpr (Let (NonRec bndr rhs) body)
  | isId bndr
  = do  { lintSingleBinding NotTopLevel NonRecursive (bndr,rhs)
        ; addLoc (BodyOfLetRec [bndr])
                 (lintAndScopeBndr bndr $ \_ -> (lintCoreExpr body)) }

  | otherwise
  = failWithL (mkLetErr bndr rhs)       -- Not quite accurate

lintCoreExpr (Let (Rec pairs) body)
  = lintAndScopeVars bndrs       $ \_ ->
    do  { checkL (null dups) (dupVars dups)
        ; mapM_ (lintSingleBinding NotTopLevel Recursive) pairs
        ; addLoc (BodyOfLetRec bndrs) (lintCoreExpr body) }
  where
    bndrs = map fst pairs
    (_, dups) = removeDups compare bndrs

lintCoreExpr e@(App _ _)
    = do { fun_ty <- lintCoreExpr fun
         ; addLoc (AnExpr e) $ foldM lintCoreArg fun_ty args }
  where
    (fun, args) = collectArgs e

lintCoreExpr (Lam bndr expr)
  = addLoc (LambdaBodyOf bndr) $
    lintBinder bndr $ \ _ ->
    do { body_ty <- lintCoreExpr expr
       ; return $ mkPiType bndr body_ty }

lintCoreExpr e@(Case scrut var alt_ty alts) =
       -- Check the scrutinee
  do { scrut_ty <- lintCoreExpr scrut
     ; alt_ty   <- lintInTypeWithValues alt_ty
     ; var_ty   <- lintInTypeWithValues (varType var)

     ; case tyConAppTyCon_maybe var_ty of
         Just tycon
              | debugIsOn &&
                isAlgTyCon tycon &&
                not (isFamilyTyCon tycon || isAbstractTyCon tycon) &&
                null (tyConDataCons tycon) ->
                  pprTrace "Lint warning: case binder's type has no constructors" (ppr var <+> ppr (idType var))
                        -- This can legitimately happen for type families
                      $ return ()
         _otherwise -> return ()

     ; subst <- getTCvSubst
     ; ensureEqTys var_ty scrut_ty (mkScrutMsg var var_ty scrut_ty subst)

     ; lintAndScopeVar var $ \_ ->
       do { -- Check the alternatives
            mapM_ (lintCoreAlt scrut_ty alt_ty) alts
          ; checkCaseAlts e scrut_ty alts
          ; return alt_ty } }

-- This case can't happen; linting types in expressions gets routed through
-- lintCoreArgs
lintCoreExpr (Type ty)
  = pprPanic "lintCoreExpr" (ppr ty)

lintCoreExpr (Coercion co)
  = do { (k1, k2, ty1, ty2, role) <- lintInCo co
       ; return (mkHeteroCoercionType role k1 k2 ty1 ty2) }

\end{code}

%************************************************************************
%*                                                                      *
\subsection[lintCoreArgs]{lintCoreArgs}
%*                                                                      *
%************************************************************************

The basic version of these functions checks that the argument is a
subtype of the required type, as one would expect.

\begin{code}
lintCoreArg  :: OutType -> CoreArg -> LintM OutType
lintCoreArg fun_ty (Type arg_ty)
  = do { checkL (not (isCoercionTy arg_ty))
                (ptext (sLit "Unnecessary coercion-to-type injection:")
                  <+> ppr arg_ty)
       ; arg_ty' <- applySubstTy arg_ty
       ; lintTyApp fun_ty arg_ty' }

lintCoreArg fun_ty (Coercion arg_co)
  = do { arg_co' <- applySubstCo arg_co
       ; lintCoApp fun_ty arg_co' }

lintCoreArg fun_ty arg
  = do { lintValApp fun_ty arg }

-----------------
lintAltBinders :: OutType     -- Scrutinee type
               -> OutType     -- Constructor type
               -> [Binder]    -- Binders
               -> LintM ()
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintAltBinders scrut_ty con_ty []
  = ensureEqTys con_ty scrut_ty (mkBadPatMsg con_ty scrut_ty)
lintAltBinders scrut_ty con_ty (bndr:bndrs)
  | Just var <- binderVar_maybe bndr
  = case () of
      _ | isTyVar var ->
          do { con_ty' <- lintTyApp con_ty (mkOnlyTyVarTy var)
             ; lintAltBinders scrut_ty con_ty' bndrs }
          
        | isCoVar cv ->
          do { con_ty' <- lintCoApp con_ty (mkCoVarCo var)
             ; lintAltBinders scrut_ty con_ty' bndrs }
          
        | otherwise ->
          do { con_ty' <- lintValApp con_ty (Var var)
             ; lintAltBinders scrut_ty con_ty' bndrs }

  | not (isDependentBinder bndr)   -- anonymous binders can't be dependent!
  , Just (arg_ty, res_ty) <- splitFunTy_maybe con_ty
  = do { let ty = binderType bndr
       ; ty' <- applySubstTy ty
       ; ensureEqTys arg_ty ty' $
         mkAppMsg con_ty bndr
       ; lintAltBinders scrut_ty res_ty bndrs }

  | otherwise
  = failWithL (text "Strange binder in pattern:" $$
               nest 2 (text "Running type:" <+> ppr con_ty) $$
               nest 2 (text "Binder:" <+> ppr bndr))

-----------------
lintTyApp :: OutType -> OutType -> LintM OutType
-- Only called for applications within *expressions*
lintTyApp fun_ty arg_ty
  | Just (bndr,body_ty) <- splitPiTy_maybe fun_ty
  , isDependentBinder bndr
  , not (isRelevantBinder bndr)
  = do  { bndr_ki <- applySubstTy (binderType bndr)
        ; arg_ki <- lintType arg_ty
        ; ensureEqTys bndr_ki arg_ki $
          mkKindErrMsg bndr arg_ty
        ; return (substTyWithBinders [bndr] [arg_ty] body_ty) }

  | otherwise
  = failWithL (mkTyAppMsg fun_ty arg_ty)

-----------------
lintCoApp :: OutType -> OutCoercion -> LintM OutType
lintCoApp fun_ty arg_co
  | Just (bndr,body_ty) <- splitPiTy_maybe fun_ty
  = do { bndr_ty <- applySubstTy (binderType bndr)
       ; case coercionSig_maybe bndr_ty of
         { Nothing -> failWithL (mkCoAppMsg fun_ty (CoercionTy arg_co) Nothing)
         ; Just (_, _, exp_t1, exp_t2, exp_r) ->
    do { (_, _, act_t1, act_t2, act_r) <- lintCoercion arg_co
       ; ensureEqTys exp_t1 act_t1 (mkCoAppMsg exp_t1 act_t1 (Just CLeft))
       ; ensureEqTys exp_t2 act_t2 (mkCoAppMsg exp_t2 act_t2 (Just CRight))
       ; lintRole arg_co exp_r act_r
       ; return (substTyWithBinders [bndr] [CoercionTy arg_co] body_ty) }}}
    
  | otherwise
  = failWithL (mkCoAppMsg fun_ty (CoercionTy arg_co) Nothing)

-----------------
lintValApp :: OutType -> CoreExpr -> LintM OutType
lintValApp fun_ty arg
  | Just (bndr, body_ty) <- splitPiTy_maybe fun_ty
  = do { checkL (isRelevantBinder bndr) $
         text "Expected relevant binder; found" <+> bndr
       ; exp_arg_ty <- applySubstTy (binderType bndr)
       ; act_arg_ty <- lintExpr arg
       ; ensureEqTys exp_arg_ty act_arg_ty err1
       ; if not (isDependentBinder bndr)
         then return body_ty else
         case promoteExpr_maybe arg of
           Just ty -> do { -- belt & braces!
                           ki <- lintType ty
                         ; ensureEqTys exp_arg_ty ki (err3 ty ki)
                         ; return (substTyWithBinders [bndr] [ty] body_ty) }
           Nothing -> failWithL err4

  | otherwise
  = failWithL err2
  where
    err1       = mkAppMsg          fun_ty arg
    err2       = mkNonFunAppMsg    fun_ty arg
    err3 ty ki = mkPromotedAppMsg  fun_ty ty ki
    err4       = mkCan'tPromoteMsg arg
\end{code}

\begin{code}
checkDeadIdOcc :: Id -> LintM ()
-- Occurrences of an Id should never be dead....
-- except when we are checking a case pattern
checkDeadIdOcc id
  | isDeadOcc (idOccInfo id)
  = do { in_case <- inCasePat
       ; checkL in_case
                (ptext (sLit "Occurrence of a dead Id") <+> ppr id) }
  | otherwise
  = return ()
\end{code}


%************************************************************************
%*                                                                      *
\subsection[lintCoreAlts]{lintCoreAlts}
%*                                                                      *
%************************************************************************

\begin{code}
checkCaseAlts :: CoreExpr -> OutType -> [CoreAlt] -> LintM ()
-- a) Check that the alts are non-empty
-- b1) Check that the DEFAULT comes first, if it exists
-- b2) Check that the others are in increasing order
-- c) Check that there's a default for infinite types
-- NB: Algebraic cases are not necessarily exhaustive, because
--     the simplifer correctly eliminates case that can't
--     possibly match.

checkCaseAlts e ty alts =
  do { checkL (all non_deflt con_alts) (mkNonDefltMsg e)
     ; checkL (increasing_tag con_alts) (mkNonIncreasingAltsMsg e)

          -- For types Int#, Word# with an infinite (well, large!) number of
          -- possible values, there should usually be a DEFAULT case
          -- But (see Note [Empty case alternatives] in CoreSyn) it's ok to
          -- have *no* case alternatives.
          -- In effect, this is a kind of partial test. I suppose it's possible
          -- that we might *know* that 'x' was 1 or 2, in which case
          --   case x of { 1 -> e1; 2 -> e2 }
          -- would be fine.
     ; checkL (isJust maybe_deflt || not is_infinite_ty || null alts)
              (nonExhaustiveAltsMsg e) }
  where
    (con_alts, maybe_deflt) = findDefault alts

        -- Check that successive alternatives have increasing tags
    increasing_tag (alt1 : rest@( alt2 : _)) = alt1 `ltAlt` alt2 && increasing_tag rest
    increasing_tag _                         = True

    non_deflt (DEFAULT, _, _) = False
    non_deflt _               = True

    is_infinite_ty = case tyConAppTyCon_maybe ty of
                        Nothing    -> False
                        Just tycon -> isPrimTyCon tycon
\end{code}

\begin{code}
lintAltExpr :: CoreExpr -> OutType -> LintM ()
lintAltExpr expr ann_ty
  = do { actual_ty <- lintCoreExpr expr
       ; ensureEqTys actual_ty ann_ty (mkCaseAltMsg expr actual_ty ann_ty) }

lintCoreAlt :: OutType          -- Type of scrutinee
            -> OutType          -- Type of the alternative
            -> CoreAlt
            -> LintM ()
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintCoreAlt _ alt_ty (DEFAULT, args, rhs) =
  do { lintL (null args) (mkDefaultArgsMsg args)
     ; lintAltExpr rhs alt_ty }

lintCoreAlt scrut_ty alt_ty (LitAlt lit, args, rhs)
  | litIsLifted lit
  = failWithL integerScrutinisedMsg
  | otherwise
  = do { lintL (null args) (mkDefaultArgsMsg args)
       ; ensureEqTys lit_ty scrut_ty (mkBadPatMsg lit_ty scrut_ty)
       ; lintAltExpr rhs alt_ty }
  where
    lit_ty = literalType lit

lintCoreAlt scrut_ty alt_ty alt@(DataAlt con, args, rhs)
  | isNewTyCon (dataConTyCon con)
  = addErrL (mkNewTyDataConAltMsg scrut_ty alt)
  | Just (tycon, tycon_arg_tys) <- splitTyConApp_maybe scrut_ty
  = addLoc (CaseAlt alt) $  do
    {   -- First instantiate the universally quantified
        -- type variables of the data constructor
        -- We've already check
      lintL (tycon == dataConTyCon con) (mkBadConMsg tycon con)
    ; let con_payload_ty = applyTys (dataConRepType con) tycon_arg_tys

        -- And now bring the new binders into scope
    ; lintBinders args $ \ _ -> do
    { addLoc (CasePat alt) (lintAltBinders scrut_ty con_payload_ty args)
    ; lintAltExpr rhs alt_ty } }

  | otherwise   -- Scrut-ty is wrong shape
  = addErrL (mkBadAltMsg scrut_ty alt)
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Binders}
%*                                                                      *
%************************************************************************

\begin{code}
-- When we lint binders, we (one at a time and in order):
--  1. Lint var types or kinds
--  2. Add the binder to the in scope set
lintBinders :: [Binder] -> ([Type] -> LintM a) -> LintM a
lintBinders [] linterF = linterF []
lintBinders (bndr:bndrs) linterF
  = lintBinder bndr $ \ty ->
    lintBinders bndrs $ \tys ->
    linterF (ty:tys)

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintBinder :: Binder -> (Type -> LintM a) -> LintM a
lintBinder bndr linterF
  = do { checkBinderInvariants bndr
       ; ty <- lintInTypeWithValues (binderType bndr)
       ; addInScopeBndr bndr (linterF ty) }

lintAndScopeVars :: [Var] -> ([Type] -> LintM a) -> LintM a
lintAndScopeVars []     linterF = linterF []
lintAndScopeVars (v:vs) linterF
  = lintAndScopeVar v $ \ v_ty ->
    lintAndScopeVars vs $ \ vs_tys ->
    linterF (v_ty:vs_tys)

lintAndScopeVar :: Var -> (Type -> LintM a) -> LintM a
lintAndScopeVar v linterF
  = do { ty <- lintInTypeWithValues (varType v)
       ; addInScopeVar v (linterF ty) }

-- | Check to make sure that a binder's relevance/dependence annotation.
-- match its payload (i.e. 'TyVar' vs. 'Var').
-- See Note [Binders] in TyCoRep
checkBinderInvariants :: Binder -> LintM ()
checkBinderInvariants bndr
  = do { when (isCoercionType (binderType bndr)) $
         checkL (isDependentBinder binder && isRelevantBinder binder)
                (text "All coercion binders must be relevant and dependent." $$
                 text "This one isn't:" <+> ppr bndr)
       ; checkL (isDependentBinder bndr || isRelevantBinder bnder)
                (text "Non-dependent, irrelevant binder:" <+> ppr bndr)
         
       ; case binderVar_maybe bndr of
           Just var ->
             do { when (not $ isRelevantBinder bndr) $
                  checkL (isTyVar var)
                         (text "Expected a TyVar but found" <+> ppr var)
                ; when (isDependentBinder bndr && isId var) $
                  checkL (isDependentId var)
                         (text "Expected a dependent Id but found" <+> ppr var)
                }
           Nothing -> return () }
\end{code}


%************************************************************************
%*                                                                      *
             Types
%*                                                                      *
%************************************************************************

\begin{code}
-- | Apply the substitution to a type, and then check if it is suitable
-- for having values. Returns the subst'ed type.
lintInTypeWithValues :: InType -> LintM LintedType
-- See Note [Linting type lets]
lintInTypeWithValues ty
  = addLoc (InType ty) $
    do  { ty' <- applySubstTy ty
        ; lintTypeWithValues ty'
        ; return ty' }

-------------------
lintType :: OutType -> LintM LintedKind
-- The returned Kind has itself been linted

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintType (TyVarTy tv)
  = do { when (isId tv) $
         checkL (isDependendId tv) (mkBadTyVarMsg tv)
       ; lintTyCoVarInScope tv
       ; applySubstTy (tyVarKind tv) }
         -- We checked its kind when we added it to the envt

lintType ty@(AppTy t1 t2)
  | TyConApp {} <- t1
  = failWithL $ ptext (sLit "TyConApp to the left of AppTy:") <+> ppr ty
  | otherwise
  = do { k1 <- lintType t1
       ; k2 <- lintType t2
       ; lint_ty_app ty k1 [(t2,k2)] }

lintType ty@(TyConApp tc tys)
  | not (isUnLiftedTyCon tc) || tys `lengthIs` tyConArity tc
       -- Check that primitive types are saturated
  = do { ks <- mapM lintType tys
       ; lint_ty_app ty (tyConKind tc) (tys `zip` ks) }
  | otherwise
  = failWithL (hang (ptext (sLit "Malformed type:")) 2 (ppr ty))

-- arrows can related *unlifted* kinds, so this has to be separate from
-- a dependent forall.
lintType ty@(PiTy bndr body_ty)
  | isDependentBinder bndr
  = lintBinder bndr (\_ -> lintType body_ty)

  | otherwise
  = do { t1 <- applySubstTy (binderType bndr)
       ; k1 <- lintType t1
       ; k2 <- lintType body_ty   -- can't refer to the binder!
       ; lintArrow k1 k2 }

lintType ty@(LitTy l) = lintTyLit l >> return (typeKind ty)

lintType (CastTy ty co)
  = do { k1 <- lintType ty
       ; (k1', k2) <- lintCoercionWithValues Representational co
       ; ensureEqTys k1 k1' (mkCastErr ty co k1' k1)
       ; return k2 }

lintType (CoercionTy co)
  = do { (k1, k2, ty1, ty2, r) <- lintCoercion co
       ; return $ mkHeteroCoercionType r k1 k2 ty1 ty2 }

\end{code}


\begin{code}
-- | Check that a type is suitable for holding values. That is: the type
-- has kind * or #.
lintTypeWithValues :: OutType -> LintM ()
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintTypeWithValues ty
  = do { k <- lintType ty
       ; lintKindOfTypeWithValues k }

-- | Check that the given kind is either * or #.
lintKindOfTypeWithValues :: LintedKind -> LintM ()
lintKindOfTypeWithValues k
  = unless (classifiesTypeWithValues k)
           (addErrL (text "Expected a kind of types with values but got"
                     <+> ppr k))

-- | confirms that a type is really *
lintStar :: SDoc -> OutKind -> LintM ()
lintStar doc k
  = lintL (isStarKind k) (ptext (sLit "Non-* kind when * expected:") <+> ppr k $$
                           ptext (sLit "when checking") <+> doc)
\end{code}


\begin{code}
-- | Checks the kinds of the types on either side of an arrow. They must
-- both be * or #. Returns the kind of the arrow, which is always *.
lintArrow :: LintedKind -> LintedKind -> LintM LintedKind
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintArrow k1 k2
  = do { lintKindOfTypeWithValues k1
       ; lintKindOfTypeWithValues k2
       ; return liftedTypeKind }

-- | Like 'lintArrow', but only checks if the binder is non-dependent.
-- Returns the kinds passed in if the binder is dependent; or liftedTypeKind
-- otherwise
lintArrowBinder :: GenBinder payload -> LintedKind -> LintedKind
                -> LintM (LintedKind, LintedKind)
lintArrowBinder bndr k1 k2
  | isDependentBinder bndr
  = return (k1, k2)
  | otherwise
  = do { k <- lintArrow k1 k2
       ; return (k, k) }

lint_ty_app :: Type -> LintedKind -> [(LintedType,LintedKind)] -> LintM LintedKind
lint_ty_app ty k tys
  = lint_app (ptext (sLit "type") <+> quotes (ppr ty)) k tys

----------------
lint_co_app :: Coercion -> LintedKind -> [(LintedType,LintedKind)] -> LintM LintedKind
lint_co_app ty k tys
  = lint_app (ptext (sLit "coercion") <+> quotes (ppr ty)) k tys

----------------
lintTyLit :: TyLit -> LintM ()
lintTyLit (NumTyLit n)
  | n >= 0    = return ()
  | otherwise = failWithL msg
    where msg = ptext (sLit "Negative type literal:") <+> integer n
lintTyLit (StrTyLit _) = return ()

lint_app :: SDoc -> LintedKind -> [(LintedType,LintedKind)] -> LintM Kind
-- (lint_app d fun_kind arg_tys)
--    We have an application (f arg_ty1 .. arg_tyn),
--    where f :: fun_kind
-- Takes care of linting the OutTypes

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lint_app doc kfn kas
    = foldlM go_app kfn kas
  where
    fail_msg = vcat [ hang (ptext (sLit "Kind application error in")) 2 doc
                    , nest 2 (ptext (sLit "Function kind =") <+> ppr kfn)
                    , nest 2 (ptext (sLit "Arg kinds =") <+> ppr kas) ]

    go_app kfn ka
      | Just kfn' <- coreView kfn
      = go_app kfn' ka

    go_app (PiTy bndr body_ty) (ta, ka)
      = do { bndr_ty <- applySubstTy (binderType bndr)
           ; unless (ka `eqType` bndr_ty) (addErrL fail_msg)
           ; if isDependentBinder bndr
             then return (substTyWithBinders [bndr] [ta] body_ty)
             else return body_ty }

    go_app _ _ = failWithL fail_msg
\end{code}

%************************************************************************
%*                                                                      *
         Linting coercions
%*                                                                      *
%************************************************************************

\begin{code}
lintInCo :: InCoercion -> LintM (LintedKind, LintedKind, LintedType, LintedType, Role)
-- Check the coercion, and apply the substitution to it
-- See Note [Linting type lets]
lintInCo co
  = addLoc (InCo co) $
    do  { co' <- applySubstCo co
        ; lintCoercion co' }

-- lints a coercion, confirming that its lh kind and its rh kind are both *
-- or #; also ensures that the role is as requested
lintCoercionWithValues :: Role -> OutCoercion -> LintM (LintedType, LintedType)
lintCoercionWithValues r_exp g
  = do { (k1, k2, t1, t2, r) <- lintCoercion g
       ; lintKindOfTypeWithValues k1
       ; lintKindOfTypeWithValues k2
       ; lintRole g r_exp r
       ; return (t1, t2) }

lintCoercion :: OutCoercion -> LintM (LintedKind, LintedKind, LintedType, LintedType, Role)
-- Check the kind of a coercion term, returning the kind
-- Post-condition: the returned OutTypes are lint-free

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism]
lintCoercion co@(Refl r ty)
  = do { checkL (not $ isCoercionTy ty)
                (ptext (sLit "Refl (CoercionTy ...):") <+> ppr co)
       ; k <- lintType ty
       ; return (k, k, ty, ty, r) }

lintCoercion co@(TyConAppCo r tc cos)
  | tc `hasKey` funTyConKey
  , [TyCoArg co1,TyCoArg co2] <- cos
  = do { (k1,k'1,s1,t1,r1) <- lintCoercion co1
       ; (k2,k'2,s2,t2,r2) <- lintCoercion co2
       ; k <- lintArrow k1 k2
       ; k' <- lintArrow k'1 k'2
       ; lintRole co1 r r1
       ; lintRole co2 r r2
       ; return (k, k', mkFunTy s1 s2, mkFunTy t1 t2, r) }

  | Just {} <- synTyConDefn_maybe tc
  = failWithL (ptext (sLit "Synonym in TyConAppCo:") <+> ppr co)

  | otherwise
  = do { (k's, ks, ss, ts, rs) <- mapAndUnzip5M lintCoercionArg cos
       ; k' <- lint_co_app co (tyConKind tc) (ss `zip` k's)
       ; k <- lint_co_app co (tyConKind tc) (ts `zip` ks)
       ; _ <- zipWith3M lintRole cos (tyConRolesX r tc) rs
       ; return (k', k, mkTyConApp tc ss, mkTyConApp tc ts, r) }

lintCoercion co@(AppCo co1 co2)
  | TyConAppCo {} <- co1
  = failWithL (ptext (sLit "TyConAppCo to the left of AppCo:") <+> ppr co)
  | Refl _ (TyConApp {}) <- co1
  = failWithL (ptext (sLit "Refl (TyConApp ...) to the left of AppCo:") <+> ppr co)
  | otherwise
  = do { (k1,k2,s1,s2,r1) <- lintCoercion co1
       ; (k'1, k'2, t1, t2, r2) <- lintCoercionArg co2
       ; k3 <- lint_co_app co k1 [(t1,k'1)]
       ; k4 <- lint_co_app co k2 [(t2,k'2)]
       ; if r1 == Phantom
         then lintL (r2 == Phantom || r2 == Nominal)
                     (ptext (sLit "Second argument in AppCo cannot be R:") $$
                      ppr co)
         else lintRole co Nominal r2
       ; return (k3, k4, mkAppTy s1 t1, mkAppTy s2 t2, r1) }

----------
lintCoercion (PiCo (TyHomo bndr) co)
  = do { (k1, k2, t1, t2, r) <- lintBinder bndr $
                                lintCoercion co
       ; let tyl = mkPiTy bndr t1
             tyr = mkPiTy bndr t2
       ; k1' <- lintType tyl
       ; k2' <- lintType tyr
       ; ensureEqTys k1 k1' (mkBadForAllKindMsg CLeft co k1 k1')
       ; ensureEqTys k2 k2' (mkBadForAllKindMsg CRight co k2 k2')
       ; (k3, k4) <- lintArrowBinder bndr k1 k2
       ; return (k3, k4, tyl, tyr, r) }

lintCoercion g@(PiCo (TyHetero h pbndr m_cv) co)
  = do { let Pair bndr1 bndr2 = splitPairBinder pbndr
       ; (k3, k4, t1, t2, r) <- lintBinder bndr1 $
                                lintBinder bndr2 $
                                scope_maybe_var m_cv $
                                lintCoercion co
       ; (k1, k2) <- lintCoercionWithValues r h
       ; lintL (not (k1 `eqType` k2)) (mkBadHeteroCoMsg h g)
       ; ensureEqTys k1 (binderType bndr1) (mkBadHeteroVarMsg CLeft k1 bndr1 g)
       ; ensureEqTys k2 (binderType bndr2) (mkBadHeteroVarMsg CRight k2 bndr2 g)
       ; case (binderVar_maybe bndr1, binderVar_maybe bndr2, m_cv) of
           (Just tv1, Just tv2, Just cv) ->
             ensureEqTys (mkCoercionType Nominal
                                         (mkOnlyTyVarTy tv1)
                                         (mkOnlyTyVarTy tv2))
                         (coVarKind cv)
                         (mkBadHeteroCoVarMsg tv1 tv2 cv g)
           (_,      _,      Just cv) -> addErrL $ unexpected_co_var cv
           _                         -> return ()
       ; let tyl = mkPiTy bndr1 t1
             tyr = mkPiTy bndr2 t2
       ; k3' <- lintType tyl
       ; k4' <- lintType tyr
       ; ensureEqTys k3 k3' (mkBadForAllKindMsg CLeft co k3 k3')
       ; ensureEqTys k4 k4' (mkBadForAllKindMsg CRight co k4 k4')
       ; (k5, k6) <- lintArrowBinder pbndr k3 k4
       ; return (k5, k6, tyl, tyr, r) }
  where
    scope_binder_var bv thing_inside
      = case getBinderVar_maybe bv of
          Just v  -> lintAndScopeVar v thing_inside
          Nothing -> do { _ <- lintInTypeWithValues (binderVarType bv)
                        ; thing_inside }

    scope_maybe_var (Just v) = lintAndScopeVar v
    scope_maybe_var Nothing  = id
        

lintCoercion (PiCo (CoHomo cv) co)
  = do { whenIsJust (binderVar_maybe cv) $
         \v -> lintL (v `freeInCoercion` co) (mkFreshnessViolationMsg cv co)
       ; (k1, k2, t1, t2, r) <- lintBinder cv $ lintCoercion co
       ; let tyl = mkPiTy cv t1
       ; let tyr = mkPiTy cv t2
       ; k1' <- lintType tyl
       ; k2' <- lintType tyr
       ; ensureEqTys k1 k1' (mkBadForAllKindMsg CLeft co k1 k1')
       ; ensureEqTys k2 k2' (mkBadForAllKindMsg CRight co k2 k2')
       ; return (k1, k2, tyl, tyr, r) }

lintCoercion g@(PiCo (CoHetero h pbndr) co)
  = do { let Pair bndr1 bndr2 = splitPairBinder pbndr
       ; whenIsJust (binderVar_maybe bndr1) $
         \cv1 -> lintL (cv1 `freeInCoercion` co) (mkFreshnessViolationMsg cv1 co)
       ; whenIsJust (binderVar_maybe bndr2) $
         \cv2 -> lintL (cv2 `freeInCoercion` co) (mkFreshnessViolationMsg cv2 co)
       ; (k1, k2, t1, t2, r) <- lintBinders [bndr1, bndr2] $ lintCoercion co
       ; (phi1, phi2) <- lintCoercionWithValues r h
       ; lintL (not (phi1 `eqType` phi2)) (mkBadHeteroCoMsg h g)
       ; ensureEqTys phi1 (binderType bndr1) (mkBadHeteroVarMsg CLeft phi1 bndr1 g)
       ; ensureEqTys phi2 (binderType bndr2) (mkBadHeteroVarMsg CRight phi2 bndr2 g)
       ; let tyl = mkPiTy bndr1 t1
       ; let tyr = mkPiTy bndr2 t2
       ; k1' <- lintType tyl
       ; k2' <- lintType tyr
       ; ensureEqTys k1 k1' (mkBadForAllKindMsg CLeft co k1 k1')
       ; ensureEqTys k2 k2' (mkBadForAllKindMsg CRight co k2 k2')
       ; return (k1, k2, tyl, tyr, r) }

lintCoercion (CoVarCo cv)
  | not (isCoVar cv)
  = failWithL (hang (ptext (sLit "Bad CoVarCo:") <+> ppr cv)
                  2 (ptext (sLit "With offending type:") <+> ppr (varType cv)))
  | otherwise
  = do { lintTyCoVarInScope cv
       ; cv' <- lookupIdInScope cv 
       ; return $ coVarKindsTypesRole cv' }

lintCoercion co@(PhantomCo h ty1 ty2)
  = do { (k1, k2) <- lintCoercionWithValues Representational h
       ; k1' <- lintType ty1
       ; k2' <- lintType ty2
       ; ensureEqTys k1 k1' (mkBadPhantomCoMsg CLeft  co)
       ; ensureEqTys k2 k2' (mkBadPhantomCoMsg CRight co)
       ; return (k1, k2, ty1, ty2, Phantom) }

lintCoercion (UnsafeCo r ty1 ty2)
  = do { k1 <- lintType ty1
       ; k2 <- lintType ty2
       ; return (k1, k2, ty1, ty2, r) }

lintCoercion (SymCo co) 
  = do { (k1, k2, ty1, ty2, r) <- lintCoercion co
       ; return (k2, k1, ty2, ty1, r) }

lintCoercion co@(TransCo co1 co2)
  = do { (k1a, _k1b, ty1a, ty1b, r1) <- lintCoercion co1
       ; (_k2a, k2b, ty2a, ty2b, r2) <- lintCoercion co2
       ; lintL (ty1b `eqType` ty2a)
               (hang (ptext (sLit "Trans coercion mis-match:") <+> ppr co)
                   2 (vcat [ppr ty1a, ppr ty1b, ppr ty2a, ppr ty2b]))
       ; lintRole co r1 r2
       ; return (k1a, k2b, ty1a, ty2b, r1) }

lintCoercion the_co@(NthCo n co)
  = do { (_, _, s, t, r) <- lintCoercion co
       ; case (splitPiTy_maybe s, splitPiTy_maybe t) of
         { (Just (bndr_s, _ty_s), Just (bndr_t, _ty_t))
             |  n == 0
             -> return (ks, kt, ts, tt, r)
             where
               ts = binderType bndr_s
               tt = binderType bndr_t
               ks = typeKind ts
               kt = typeKind tt
               
         ; _ -> case (splitTyConApp_maybe s, splitTyConApp_maybe t) of
         { (Just (tc_s, tys_s), Just (tc_t, tys_t))
             | tc_s == tc_t
             , tys_s `equalLength` tys_t
             , n < length tys_s
             -> do { lintL (not (isCoercionTy ts)) (mkNthIsCoMsg CLeft the_co)
                   ; lintL (not (isCoercionTy tt)) (mkNthIsCoMsg CRight the_co)
                   ; return (ks, kt, ts, tt, tr) }
             where
               ts = getNth tys_s n
               tt = getNth tys_t n
               tr = nthRole r tc_s n
               ks = typeKind ts
               kt = typeKind tt

         ; _ -> failWithL (hang (ptext (sLit "Bad getNth:"))
                              2 (ppr the_co $$ ppr s $$ ppr t)) }}}

lintCoercion the_co@(LRCo lr co)
  = do { (_,_,s,t,r) <- lintCoercion co
       ; lintRole co Nominal r
       ; case (splitAppTy_maybe s, splitAppTy_maybe t) of
           (Just s_pr, Just t_pr) 
             -> do { lintL (not (isCoercionTy s_pick)) (mkNthIsCoMsg CLeft the_co)
                   ; lintL (not (isCoercionTy t_pick)) (mkNthIsCoMsg CRight the_co)
                   ; return (ks_pick, kt_pick, s_pick, t_pick, Nominal) }
             where
               s_pick  = pickLR lr s_pr
               t_pick  = pickLR lr t_pr
               ks_pick = typeKind s_pick
               kt_pick = typeKind t_pick

           _ -> failWithL (hang (ptext (sLit "Bad LRCo:"))
                              2 (ppr the_co $$ ppr s $$ ppr t)) }

lintCoercion (InstCo co arg)
  = do { (k3, k4, t1',t2', r) <- lintCoercion co
       ; (k1',k2',s1,s2, r') <- lintCoercionArg arg
       ; lintRole arg Nominal r'
       ; case (splitPiTy_maybe t1', splitPiTy_maybe t2') of
          (Just (bndr1,t1), Just (bndr2,t2))
            | isDependentBinder bndr1
            , isDependentBinder bndr2
            , k1' `eqType` binderType bndr1
            , k2' `eqType` binderType bndr2
            -> return (k3, k4,
                       substTyWithBinders [bndr1] [s1] t1, 
                       substTyWithBinders [bndr2] [s2] t2, r) 
            | otherwise
            -> failWithL (ptext (sLit "Kind mis-match in inst coercion"))
          _ -> failWithL (ptext (sLit "Bad argument of inst")) }

lintCoercion co@(AxiomInstCo con ind cos)
  = do { unless (0 <= ind && ind < brListLength (coAxiomBranches con))
                (bad_ax (ptext (sLit "index out of range")))
       ; let CoAxBranch { cab_tvs   = ktvs
                        , cab_roles = roles
                        , cab_lhs   = lhs
                        , cab_rhs   = rhs } = coAxiomNthBranch con ind
       ; unless (equalLength ktvs cos) (bad_ax (ptext (sLit "lengths")))
       ; subst <- getTCvSubst
       ; let empty_subst = zapTCvSubst subst
       ; (subst_l, subst_r) <- foldlM check_ki
                                      (empty_subst, empty_subst)
                                      (zip3 ktvs roles cos)
       ; let lhs' = substTys subst_l lhs
             rhs' = substTy subst_r rhs
       ; case checkAxInstCo co of
           Just bad_branch -> bad_ax $ ptext (sLit "inconsistent with") <+> (pprCoAxBranch (coAxiomTyCon con) bad_branch)
           Nothing -> return ()
       ; let s2 = mkTyConApp (coAxiomTyCon con) lhs'
       ; return (typeKind s2, typeKind rhs', s2, rhs', coAxiomRole con) }
  where
    bad_ax what = addErrL (hang (ptext (sLit "Bad axiom application") <+> parens what)
                        2 (ppr co))

    check_ki (subst_l, subst_r) (ktv, role, arg)
      = do { (k', k'', s', t', r) <- lintCoercionArg arg
           ; lintRole arg role r
           ; let ktv_kind_l = substTy subst_l (tyVarKind ktv)
                 ktv_kind_r = substTy subst_r (tyVarKind ktv)
           ; unless (k' `eqType` ktv_kind_l) 
                    (bad_ax (ptext (sLit "check_ki1") <+> vcat [ ppr co, ppr k', ppr ktv, ppr ktv_kind_l ] ))
           ; unless (k'' `eqType` ktv_kind_r)
                    (bad_ax (ptext (sLit "check_ki2") <+> vcat [ ppr co, ppr k'', ppr ktv, ppr ktv_kind_r ] ))
           ; return (extendTCvSubst subst_l ktv s', 
                     extendTCvSubst subst_r ktv t') }

lintCoercion (CoherenceCo co1 co2)
  = do { (_, k2, t1, t2, r) <- lintCoercion co1
       ; let lhsty = mkCastTy t1 co2
       ; k1' <- lintType lhsty
       ; return (k1', k2, lhsty, t2, r) }

lintCoercion (KindCo co)
  = do { (k1, k2, _, _, _) <- lintCoercion co
       ; return (liftedTypeKind, liftedTypeKind, k1, k2, Representational) }

lintCoercion (SubCo co')
  = do { (k1,k2,s,t,r) <- lintCoercion co'
       ; lintRole co' Nominal r
       ; return (k1,k2,s,t,Representational) }

lintCoercion this@(AxiomRuleCo co ts cs)
  = do _ks <- mapM lintType ts
       eqs <- mapM lintCoercion cs

       let tyNum = length ts

       case compare (coaxrTypeArity co) tyNum of
         EQ -> return ()
         LT -> err "Too many type arguments"
                    [ text "expected" <+> int (coaxrTypeArity co)
                    , text "provided" <+> int tyNum ]
         GT -> err "Not enough type arguments"
                    [ text "expected" <+> int (coaxrTypeArity co)
                          , text "provided" <+> int tyNum ]
       lintRoles 0 (coaxrAsmpRoles co) eqs

       case coaxrProves co ts [ Pair l r | (_,_,l,r,_) <- eqs ] of
         Nothing -> err "Malformed use of AxiomRuleCo" [ ppr this ]
         Just (Pair l r) ->
           do kL <- lintType l
              kR <- lintType r
              return (kL, kR, l, r, coaxrRole co)
  where
  err m xs  = failWithL $
                hang (text m) 2 $ vcat (text "Rule:" <+> ppr (coaxrName co) : xs)

  lintRoles n (e : es) ((_,_,_,_,r) : rs)
    | e == r    = lintRoles (n+1) es rs
    | otherwise = err "Argument roles mismatch"
                      [ text "In argument:" <+> int (n+1)
                      , text "Expected:" <+> ppr e
                      , text "Found:" <+> ppr r ]
  lintRoles _ [] []  = return ()
  lintRoles n [] rs  = err "Too many coercion arguments"
                          [ text "Expected:" <+> int n
                          , text "Provided:" <+> int (n + length rs) ]

  lintRoles n es []  = err "Not enough coercion arguments"
                          [ text "Expected:" <+> int (n + length es)
                          , text "Provided:" <+> int n ]

----------
lintCoercionArg :: OutCoercionArg
                -> LintM (LintedKind, LintedKind, LintedType, LintedType, Role)
lintCoercionArg (TyCoArg co) = lintCoercion co
lintCoercionArg (CoCoArg r co1 co2)
  = do { phi1 <- lintCoercion co1
       ; phi2 <- lintCoercion co2
       ; return ( phi_to_ty phi1, phi_to_ty phi2
                , CoercionTy co1, CoercionTy co2, r) }
  where phi_to_ty (a,b,c,d,e) = mkHeteroCoercionType e a b c d
\end{code}

Note [FreeIn...]
~~~~~~~~~~~~~~~~~~~~~
The proof of consistency of the type system depends on a freeness condition
in the premises of PiCo (CoHetero ...). This condition states that the coercion
variables quantified over do not appear in the erased form of coercion
in the quantification. See http://www.cis.upenn.edu/~sweirich/papers/nokinds-extended.pdf

\begin{code}

freeInCoercion :: CoVar -> Coercion -> Bool
freeInCoercion v (Refl _ t)                = freeInType v t
freeInCoercion v (TyConAppCo _ _ args)     = all (freeInCoercionArg v) args
freeInCoercion v (AppCo g w)               = (freeInCoercion v g) &&
                                             (freeInCoercionArg v w)
freeInCoercion v (PiCo (TyHomo a) g)       = (freeInBinder v a) &&
                                             (freeInCoercion v g)
freeInCoercion v (PiCo (TyHetero h pbndr m_c) g)
  = let Pair ty1 ty2 = binderVarType <$> binderPayload pbndr in
    (freeInCoercion v h) &&
    (freeInType v ty1) && (freeInType v ty2) &&
    case m_c of
      Just c  -> freeInCoVar v c $ freeInCoercion v g
      Nothing -> freeInCoercion v g
freeInCoercion v (PiCo (CoHomo c) g)       = freeInCoBinder v c $ freeInCoercion v g
freeInCoercion v (PiCo (CoHetero h pbndr) g)
  = let Pair bndr1 bndr2 = splitPairBinder pbndr in
    (freeInCoercion v h) &&
    (freeInCoBinder v bndr1 $ freeInCoBinder v bndr2 $ freeInCoercion v g)
freeInCoercion v (CoVarCo c)               = freeInCoVar v c True
freeInCoercion v (AxiomInstCo _ _ args)    = all (freeInCoercionArg v) args
freeInCoercion v (PhantomCo h t1 t2)       = freeInCoercion v h && freeInType v t1 && freeInType v t2
freeInCoercion v (UnsafeCo _ t1 t2)        = (freeInType v t1) && (freeInType v t2)
freeInCoercion v (SymCo g)                 = freeInCoercion v g
freeInCoercion v (TransCo g1 g2)           = (freeInCoercion v g1) && (freeInCoercion v g2)
freeInCoercion v (NthCo _ g)               = freeInCoercion v g
freeInCoercion v (LRCo _ g)                = freeInCoercion v g
freeInCoercion v (InstCo g w)              = (freeInCoercion v g) && (freeInCoercionArg v w)
freeInCoercion v (CoherenceCo g _)         = freeInCoercion v g
freeInCoercion v (KindCo g)                = freeInCoercion v g
freeInCoercion v (SubCo g)                 = freeInCoercion v g
freeInCoercion v (AxiomRuleCo _ ts cs)     = all (freeInType v) ts && all (freeInCoercion v) cs

freeInType :: CoVar -> Type -> Bool
freeInType v (TyVarTy tv)       = freeInTyVar v tv
freeInType v (AppTy t1 t2)      = (freeInType v t1) && (freeInType v t2)
freeInType v (TyConApp _ args)  = all (freeInType v) args
freeInType v (PiTy bndr ty)     = (freeInBinder v bndr) && (freeInType v ty)
freeInType _ (LitTy {})         = True
freeInType v (CastTy t _)       = freeInType v t
freeInType _ (CoercionTy _)     = True

freeInTyVar :: CoVar -> TyVar -> Bool
freeInTyVar v tv = freeInType v (tyVarKind tv)

freeInBinder :: CoVar -> Binder -> Bool
freeInBinder v bndr = freeInType v (binderType bndr)

-- Third parameter is a continuation
freeInCoVar :: CoVar -> CoVar -> Bool -> Bool
freeInCoVar v c cont = freeInType v (varType c) && (v == c || cont)

freeInCoBinder :: CoVar -> Binder -> Bool -> Bool
freeInCoBinder v c cont
  = freeInType v (binderType c) && (v `isBoundBy` v || cont)

freeInCoercionArg :: CoVar -> CoercionArg -> Bool
freeInCoercionArg v (TyCoArg g)   = freeInCoercion v g
freeInCoercionArg _ (CoCoArg _ _ _) = True

\end{code}

%************************************************************************
%*                                                                      *
\subsection[lint-monad]{The Lint monad}
%*                                                                      *
%************************************************************************

\begin{code}

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism]
newtype LintM a =
   LintM { unLintM ::
            [LintLocInfo] ->         -- Locations
            TCvSubst ->              -- Current type substitution; its
                                     -- InScopeSet tracks all in-scope vars
            WarnsAndErrs ->           -- Error and warning messages so far
            (Maybe a, WarnsAndErrs) } -- Result and messages (if any)

type WarnsAndErrs = (Bag MsgDoc, Bag MsgDoc)

{-      Note [Type substitution]
        ~~~~~~~~~~~~~~~~~~~~~~~~
Why do we need a type substitution?  Consider
        /\(a:*). \(x:a). /\(a:*). id a x
This is ill typed, because (renaming variables) it is really
        /\(a:*). \(x:a). /\(b:*). id b x
Hence, when checking an application, we can't naively compare x's type
(at its binding site) with its expected type (at a use site).  So we
rename type binders as we go, maintaining a substitution.

The same substitution also supports let-type, current expressed as
        (/\(a:*). body) ty
Here we substitute 'ty' for 'a' in 'body', on the fly.

Because of the existence of this substitution, we must be careful
never to call varType (or idType or tyVarKind) without applying the
subst directly afterwards. The types stored in variables will be wrong
otherwise.

-}

instance Functor LintM where
      fmap = liftM

instance Applicative LintM where
      pure = return
      (<*>) = ap

instance Monad LintM where
  return x = LintM (\ _   _     errs -> (Just x, errs))
  fail err = failWithL (text err)
  m >>= k  = LintM (\ loc subst errs ->
                       let (res, errs') = unLintM m loc subst errs in
                         case res of
                           Just r -> unLintM (k r) loc subst errs'
                           Nothing -> (Nothing, errs'))

data LintLocInfo
  = RhsOf Id            -- The variable bound
  | LambdaBodyOf Id     -- The lambda-binder
  | BodyOfLetRec [Id]   -- One of the binders
  | CaseAlt CoreAlt     -- Case alternative
  | CasePat CoreAlt     -- The *pattern* of the case alternative
  | AnExpr CoreExpr     -- Some expression
  | ImportedUnfolding SrcLoc -- Some imported unfolding (ToDo: say which)
  | TopLevelBindings
  | InType Type         -- Inside a type
  | InCo   Coercion     -- Inside a coercion
\end{code}


\begin{code}
initL :: LintM a -> WarnsAndErrs    -- Errors and warnings
initL m
  = case unLintM m [] emptyTCvSubst (emptyBag, emptyBag) of
      (_, errs) -> errs
\end{code}

\begin{code}
checkL :: Bool -> MsgDoc -> LintM ()
checkL True  _   = return ()
checkL False msg = failWithL msg

-- like checkL, but relevant to type checking
lintL :: Bool -> MsgDoc -> LintM ()
lintL = checkL

failWithL :: MsgDoc -> LintM a
failWithL msg = LintM $ \ loc subst (warns,errs) ->
                (Nothing, (warns, addMsg subst errs msg loc))

addErrL :: MsgDoc -> LintM ()
addErrL msg = LintM $ \ loc subst (warns,errs) ->
              (Just (), (warns, addMsg subst errs msg loc))

addWarnL :: MsgDoc -> LintM ()
addWarnL msg = LintM $ \ loc subst (warns,errs) ->
              (Just (), (addMsg subst warns msg loc, errs))

addMsg :: TCvSubst ->  Bag MsgDoc -> MsgDoc -> [LintLocInfo] -> Bag MsgDoc
addMsg subst msgs msg locs
  = ASSERT( notNull locs )
    msgs `snocBag` mk_msg msg
  where
   (loc, cxt1) = dumpLoc (head locs)
   cxts        = [snd (dumpLoc loc) | loc <- locs]
   context     | opt_PprStyle_Debug = vcat (reverse cxts) $$ cxt1 $$
                                      ptext (sLit "Substitution:") <+> ppr subst
               | otherwise          = cxt1

   mk_msg msg = mkLocMessage SevWarning (mkSrcSpan loc loc) (context $$ msg)

addLoc :: LintLocInfo -> LintM a -> LintM a
addLoc extra_loc m =
  LintM (\ loc subst errs -> unLintM m (extra_loc:loc) subst errs)

inCasePat :: LintM Bool         -- A slight hack; see the unique call site
inCasePat = LintM $ \ loc _ errs -> (Just (is_case_pat loc), errs)
  where
    is_case_pat (CasePat {} : _) = True
    is_case_pat _other           = False

addInScopeVars :: [Var] -> LintM a -> LintM a
addInScopeVars vars m
  = LintM (\ loc subst errs ->
           unLintM m loc (extendTCvInScopeList subst vars) errs)

addInScopeVar :: [Var] -> LintM a -> LintM a
addInScopeVar var m
  = LintM (\ loc subst errs ->
           unLintM m loc (extendTCvInScope subst var) errs)

addInScopeBndr :: Binder -> LintM a -> LintM a
addInScopeBndr bndr m
  | Just var <- binderVar_maybe bndr
  = addInScopeVar var m
  | otherwise   -- anonymous
  = m

updateTCvSubst :: TCvSubst -> LintM a -> LintM a
updateTCvSubst subst' m =
  LintM (\ loc _ in_scope errs -> unLintM m loc subst' in_scope errs)

getTCvSubst :: LintM TCvSubst
getTCvSubst = LintM (\ _ subst _ errs -> (Just subst, errs))

applySubstTy :: InType -> LintM OutType
applySubstTy ty = do { subst <- getTCvSubst; return (substTy subst ty) }

applySubstCo :: InCoercion -> LintM OutCoercion
applySubstCo co = do { subst <- getTCvSubst; return (substCo subst co) }

extendSubstL :: TyVar -> Type -> LintM a -> LintM a
extendSubstL tv ty m
  = LintM (\ loc subst in_scope errs ->
           unLintM m loc (extendTCvSubst subst tv ty) in_scope errs)

lookupIdInScope :: Id -> LintM Id
lookupIdInScope id
  | not (mustHaveLocalBinding id)
  = return id   -- An imported Id
  | otherwise
  = do  { subst <- getTCvSubst
        ; case lookupTCvInScope subst id of
                Just v  -> return v
                Nothing -> do { addErrL out_of_scope
                              ; return id } }
  where
    out_of_scope = pprBndr LetBind id <+> ptext (sLit "is out of scope")


oneTupleDataConId :: Id -- Should not happen
oneTupleDataConId = dataConWorkId (tupleCon BoxedTuple 1)

lintBndrIdInScope :: Var -> Var -> LintM ()
lintBndrIdInScope binder id
  = lintInScope msg id
    where
     msg = ptext (sLit "is out of scope inside info for") <+>
           ppr binder

lintTyCoVarInScope :: Var -> LintM ()
lintTyCoVarInScope v = lintInScope (ptext (sLit "is out of scope")) v

lintInScope :: SDoc -> Var -> LintM ()
lintInScope loc_msg var =
 do { subst <- getTCvSubst
    ; lintL (not (mustHaveLocalBinding var) || (var `isInScope` subst))
             (hsep [pprBndr LetBind var, loc_msg]) }

ensureEqTys :: OutType -> OutType -> MsgDoc -> LintM ()
-- check ty2 equals ty1
-- Assumes ty1,ty2 are have alrady had the substitution applied
ensureEqTys ty1 ty2 msg = lintL (ty1 `eqType` ty2) msg

lintRole :: Outputable thing
          => thing     -- where the role appeared
          -> Role      -- expected
          -> Role      -- actual
          -> LintM ()
lintRole co r1 r2
  = lintL (r1 == r2)
          (ptext (sLit "Role incompatibility: expected") <+> ppr r1 <> comma <+>
           ptext (sLit "got") <+> ppr r2 $$
           ptext (sLit "in") <+> ppr co)

\end{code}

%************************************************************************
%*                                                                      *
\subsection{Error messages}
%*                                                                      *
%************************************************************************

\begin{code}
dumpLoc :: LintLocInfo -> (SrcLoc, SDoc)

dumpLoc (RhsOf v)
  = (getSrcLoc v, brackets (ptext (sLit "RHS of") <+> pp_binders [v]))

dumpLoc (LambdaBodyOf b)
  = (getSrcLoc b, brackets (ptext (sLit "in body of lambda with binder") <+> pp_binder b))

dumpLoc (BodyOfLetRec [])
  = (noSrcLoc, brackets (ptext (sLit "In body of a letrec with no binders")))

dumpLoc (BodyOfLetRec bs@(_:_))
  = ( getSrcLoc (head bs), brackets (ptext (sLit "in body of letrec with binders") <+> pp_binders bs))

dumpLoc (AnExpr e)
  = (noSrcLoc, text "In the expression:" <+> ppr e)

dumpLoc (CaseAlt (con, args, _))
  = (noSrcLoc, text "In a case alternative:" <+> parens (ppr con <+> pp_binders args))

dumpLoc (CasePat (con, args, _))
  = (noSrcLoc, text "In the pattern of a case alternative:" <+> parens (ppr con <+> pp_binders args))

dumpLoc (ImportedUnfolding locn)
  = (locn, brackets (ptext (sLit "in an imported unfolding")))
dumpLoc TopLevelBindings
  = (noSrcLoc, empty)
dumpLoc (InType ty)
  = (noSrcLoc, text "In the type" <+> quotes (ppr ty))
dumpLoc (InCo co)
  = (noSrcLoc, text "In the coercion" <+> quotes (ppr co))

pp_binders :: [Var] -> SDoc
pp_binders bs = sep (punctuate comma (map pp_binder bs))

pp_binder :: Var -> SDoc
pp_binder b | isId b    = hsep [ppr b, dcolon, ppr (idType b)]
            | otherwise = hsep [ppr b, dcolon, ppr (tyVarKind b)]
\end{code}

\begin{code}
------------------------------------------------------
--      Messages for case expressions

mkDefaultArgsMsg :: [Var] -> MsgDoc
mkDefaultArgsMsg args
  = hang (text "DEFAULT case with binders")
         4 (ppr args)

mkCaseAltMsg :: CoreExpr -> Type -> Type -> MsgDoc
mkCaseAltMsg e ty1 ty2
  = hang (text "Type of case alternatives not the same as the annotation on case:")
         4 (vcat [ppr ty1, ppr ty2, ppr e])

mkScrutMsg :: Id -> Type -> Type -> TCvSubst -> MsgDoc
mkScrutMsg var var_ty scrut_ty subst
  = vcat [text "Result binder in case doesn't match scrutinee:" <+> ppr var,
          text "Result binder type:" <+> ppr var_ty,--(idType var),
          text "Scrutinee type:" <+> ppr scrut_ty,
     hsep [ptext (sLit "Current TCv subst"), ppr subst]]

mkNonDefltMsg, mkNonIncreasingAltsMsg :: CoreExpr -> MsgDoc
mkNonDefltMsg e
  = hang (text "Case expression with DEFAULT not at the beginnning") 4 (ppr e)
mkNonIncreasingAltsMsg e
  = hang (text "Case expression with badly-ordered alternatives") 4 (ppr e)

nonExhaustiveAltsMsg :: CoreExpr -> MsgDoc
nonExhaustiveAltsMsg e
  = hang (text "Case expression with non-exhaustive alternatives") 4 (ppr e)

mkBadConMsg :: TyCon -> DataCon -> MsgDoc
mkBadConMsg tycon datacon
  = vcat [
        text "In a case alternative, data constructor isn't in scrutinee type:",
        text "Scrutinee type constructor:" <+> ppr tycon,
        text "Data con:" <+> ppr datacon
    ]

mkBadPatMsg :: Type -> Type -> MsgDoc
mkBadPatMsg con_result_ty scrut_ty
  = vcat [
        text "In a case alternative, pattern result type doesn't match scrutinee type:",
        text "Pattern result type:" <+> ppr con_result_ty,
        text "Scrutinee type:" <+> ppr scrut_ty
    ]

integerScrutinisedMsg :: MsgDoc
integerScrutinisedMsg
  = text "In a LitAlt, the literal is lifted (probably Integer)"

mkBadAltMsg :: Type -> CoreAlt -> MsgDoc
mkBadAltMsg scrut_ty alt
  = vcat [ text "Data alternative when scrutinee is not a tycon application",
           text "Scrutinee type:" <+> ppr scrut_ty,
           text "Alternative:" <+> pprCoreAlt alt ]

mkNewTyDataConAltMsg :: Type -> CoreAlt -> MsgDoc
mkNewTyDataConAltMsg scrut_ty alt
  = vcat [ text "Data alternative for newtype datacon",
           text "Scrutinee type:" <+> ppr scrut_ty,
           text "Alternative:" <+> pprCoreAlt alt ]


------------------------------------------------------
--      Other error messages

mkAppMsg :: Outputable arg => Type -> arg -> MsgDoc
mkAppMsg fun_ty arg
  = vcat [ptext (sLit "Argument value doesn't match argument type:"),
              hang (ptext (sLit "Fun type:")) 4 (ppr fun_ty),
              hang (ptext (sLit "Arg:")) 4 (ppr arg)]

mkNonFunAppMsg :: Type -> Type -> CoreExpr -> MsgDoc
mkNonFunAppMsg fun_ty arg_ty arg
  = vcat [ptext (sLit "Non-function type in function position"),
              hang (ptext (sLit "Fun type:")) 4 (ppr fun_ty),
              hang (ptext (sLit "Arg type:")) 4 (ppr arg_ty),
              hang (ptext (sLit "Arg:")) 4 (ppr arg)]

mkPromotedAppMsg :: Type -> Type -> Kind -> MsgDoc
mkPromotedAppMsg fun_ty arg arg_ki
  = vcat [ text "Promoted expression's kind doesn't match argument type:"
         , hang (text "Fun type:") 4 (ppr fun_ty)
         , hang (text "Arg:") 4 (ppr arg)
         , hang (text "Arg kind:") 4 (ppr arg_ki) ]

mkCan'tPromoteMsg :: CoreExpr -> MsgDoc
mkCan'tPromoteMsg expr
  = hang (text "Cannot promoted an expression used in a dependent context:")
       4 (ppr expr)

mkLetErr :: TyVar -> CoreExpr -> MsgDoc
mkLetErr bndr rhs
  = vcat [ptext (sLit "Bad `let' binding:"),
          hang (ptext (sLit "Variable:"))
                 4 (ppr bndr <+> dcolon <+> ppr (varType bndr)),
          hang (ptext (sLit "Rhs:"))
                 4 (ppr rhs)]

mkTyAppMsg :: Type -> Type -> MsgDoc
mkTyAppMsg ty arg_ty
  = vcat [text "Illegal type application:",
              hang (ptext (sLit "Exp type:"))
                 4 (ppr ty <+> dcolon <+> ppr (typeKind ty)),
              hang (ptext (sLit "Arg type:"))
                 4 (ppr arg_ty <+> dcolon <+> ppr (typeKind arg_ty))]

mkCoAppMsg :: Type -> Type -> Maybe LeftOrRight -> MsgDoc
mkCoAppMsg t1 t2 m_lr
  = vcat [text "Illegal coercion application:",
              hang (ptext (sLit "Exp") <+> typename <> colon)
                 4 (ppr t1 <+> dcolon <+> ppr (typeKind t1)),
              hang (ptext (sLit "Arg") <+> typename <> colon)
                 4 (ppr t2 <+> dcolon <+> ppr (typeKind t2))]
  where
    typename | Just CLeft <- m_lr  = ptext (sLit "left-hand type")
             | Just CRight <- m_lr = ptext (sLit "right-hand type")
             | otherwise           = empty

mkRhsMsg :: Id -> SDoc -> Type -> MsgDoc
mkRhsMsg binder what ty
  = vcat
    [hsep [ptext (sLit "The type of this binder doesn't match the type of its") <+> what <> colon,
            ppr binder],
     hsep [ptext (sLit "Binder's type:"), ppr (idType binder)],
     hsep [ptext (sLit "Rhs type:"), ppr ty]]

mkRhsPrimMsg :: Id -> CoreExpr -> MsgDoc
mkRhsPrimMsg binder _rhs
  = vcat [hsep [ptext (sLit "The type of this binder is primitive:"),
                     ppr binder],
              hsep [ptext (sLit "Binder's type:"), ppr (idType binder)]
             ]

mkStrictMsg :: Id -> MsgDoc
mkStrictMsg binder
  = vcat [hsep [ptext (sLit "Recursive or top-level binder has strict demand info:"),
                     ppr binder],
              hsep [ptext (sLit "Binder's demand info:"), ppr (idDemandInfo binder)]
             ]

mkNonTopExportedMsg :: Id -> MsgDoc
mkNonTopExportedMsg binder
  = hsep [ptext (sLit "Non-top-level binder is marked as exported:"), ppr binder]

mkNonTopExternalNameMsg :: Id -> MsgDoc
mkNonTopExternalNameMsg binder
  = hsep [ptext (sLit "Non-top-level binder has an external name:"), ppr binder]

mkKindErrMsg :: TyVar -> Type -> MsgDoc
mkKindErrMsg tyvar arg_ty
  = vcat [ptext (sLit "Kinds don't match in type application:"),
          hang (ptext (sLit "Type variable:"))
                 4 (ppr tyvar <+> dcolon <+> ppr (tyVarKind tyvar)),
          hang (ptext (sLit "Arg type:"))
                 4 (ppr arg_ty <+> dcolon <+> ppr (typeKind arg_ty))]

{- Not needed now
mkArityMsg :: Id -> MsgDoc
mkArityMsg binder
  = vcat [hsep [ptext (sLit "Demand type has"),
                ppr (dmdTypeDepth dmd_ty),
                ptext (sLit "arguments, rhs has"),
                ppr (idArity binder),
                ptext (sLit "arguments,"),
                ppr binder],
              hsep [ptext (sLit "Binder's strictness signature:"), ppr dmd_ty]

         ]
           where (StrictSig dmd_ty) = idStrictness binder
-}
mkCastErr :: Outputable casted => casted -> Coercion -> Type -> Type -> MsgDoc
mkCastErr expr co from_ty expr_ty
  = vcat [ptext (sLit "From-type of Cast differs from type of enclosed expression"),
          ptext (sLit "From-type:") <+> ppr from_ty,
          ptext (sLit "Type of enclosed expr:") <+> ppr expr_ty,
          ptext (sLit "Actual enclosed expr:") <+> ppr expr,
          ptext (sLit "Coercion used in cast:") <+> ppr co
         ]

mkBadHeteroCoMsg :: Coercion -> Coercion -> MsgDoc
mkBadHeteroCoMsg h g
  = hang (ptext (sLit "Heterogeneous quantified coercion has a reflexive kind:"))
       2 (vcat [ptext (sLit "Kind coercion:") <+> ppr h,
                ptext (sLit "Overall coercion:") <+> ppr g])

mkBadHeteroVarMsg :: LeftOrRight -> Type -> TyCoVar -> Coercion -> MsgDoc
mkBadHeteroVarMsg lr k tv g
  = hang (ptext (sLit "Kind mismatch in") <+> pprLeftOrRight lr <+>
                ptext (sLit "side of hetero quantification:"))
       2 (vcat [ptext (sLit "Var:") <+> ppr tv,
                ptext (sLit "Expected kind:") <+> ppr k,
                ptext (sLit "In coercion:") <+> ppr g])

mkBadHeteroCoVarMsg :: TyVar -> TyVar -> CoVar -> Coercion -> MsgDoc
mkBadHeteroCoVarMsg tv1 tv2 cv g
  = hang (ptext (sLit "Coercion variable mismatch in TyHetero quantification:"))
       2 (vcat [ptext (sLit "TyVars:") <+> ppr tv1 <> comma <+> ppr tv2,
                ptext (sLit "CoVar:") <+> ppr cv,
                ptext (sLit "In coercion:") <+> ppr g])
        
mkFreshnessViolationMsg :: CoVar -> Coercion -> MsgDoc
mkFreshnessViolationMsg cv co
  = hang (ptext (sLit "CoVar") <+> (ppr cv) <+>
          ptext (sLit "appears in the erased form of the following coercion:"))
       2 (ppr co)

mkNthIsCoMsg :: LeftOrRight -> Coercion -> MsgDoc
mkNthIsCoMsg lr co
  = ptext (sLit "Coercion") <+> (ppr co) <+>
    ptext (sLit "yields a coercion on the") <+> pprLeftOrRight lr <+>
    ptext (sLit "side")

mkBadForAllKindMsg :: LeftOrRight -> Coercion -> Kind -> Kind -> SDoc
mkBadForAllKindMsg lr co co_kind ty_kind
  = (ptext (sLit "Kind mismatch on the") <+> pprLeftOrRight lr <+>
      ptext (sLit "side of the coercion") <+> ppr co)  $$
    (ptext (sLit "Coercion kind:") <+> ppr co_kind) $$
    (ptext (sLit "Forall type kind:") <+> ppr ty_kind)

mkBadPhantomCoMsg :: LeftOrRight -> Coercion -> SDoc
mkBadPhantomCoMsg lr co
  = text "Kind mismatch on the" <+> pprLeftOrRight lr <+>
    text "side of a phantom coercion:" <+> ppr co

mkBadTyVarMsg :: TyCoVar -> SDoc
mkBadTyVarMsg tv
  = ptext (sLit "Non-dependent Id used in TyVarTy:")
      <+> ppr tv <+> dcolon <+> ppr (varType tv)

pprLeftOrRight :: LeftOrRight -> MsgDoc
pprLeftOrRight CLeft  = ptext (sLit "left")
pprLeftOrRight CRight = ptext (sLit "right")

dupVars :: [[Var]] -> MsgDoc
dupVars vars
  = hang (ptext (sLit "Duplicate variables brought into scope"))
       2 (ppr vars)

dupExtVars :: [[Name]] -> MsgDoc
dupExtVars vars
  = hang (ptext (sLit "Duplicate top-level variables with the same qualified name"))
       2 (ppr vars)
\end{code}

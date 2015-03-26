{-# LANGUAGE CPP #-}

module TcCanonical( 
     canonicalize,
     unifyDerived,

     StopOrContinue(..), stopWith, continueWith
  ) where

#include "HsVersions.h"

import TcRnTypes
import TcType
import Type
import TcFlatten
import TcSMonad
import TcEvidence
import Class
import TyCon
import TyCoRep   -- cleverly decomposes types, good for completeness checking
import Coercion
import FamInstEnv ( FamInstEnvs )
import FamInst ( tcTopNormaliseNewTypeTF_maybe )
import Var
import DataCon ( dataConName )
import Name( isSystemName, nameOccName )
import OccName( OccName )
import Outputable
import Control.Monad
import DynFlags( DynFlags )
import VarSet
import RdrName

import Pair
import Util
import MonadUtils ( zipWith3M, zipWith3M_ )
import Data.List  ( zip4 )
import BasicTypes
import Data.Maybe ( isJust )
import FastString

{-
************************************************************************
*                                                                      *
*                      The Canonicaliser                               *
*                                                                      *
************************************************************************

Note [Canonicalization]
~~~~~~~~~~~~~~~~~~~~~~~

Canonicalization converts a simple constraint to a canonical form. It is
unary (i.e. treats individual constraints one at a time), does not do
any zonking, but lives in TcS monad because it needs to create fresh
variables (for flattening) and consult the inerts (for efficiency).

The execution plan for canonicalization is the following:

  1) Decomposition of equalities happens as necessary until we reach a
     variable or type family in one side. There is no decomposition step
     for other forms of constraints.

  2) If, when we decompose, we discover a variable on the head then we
     look at inert_eqs from the current inert for a substitution for this
     variable and contine decomposing. Hence we lazily apply the inert
     substitution if it is needed.

  3) If no more decomposition is possible, we deeply apply the substitution
     from the inert_eqs and continue with flattening.

  4) During flattening, we examine whether we have already flattened some
     function application by looking at all the CTyFunEqs with the same
     function in the inert set. The reason for deeply applying the inert
     substitution at step (3) is to maximise our chances of matching an
     already flattened family application in the inert.

The net result is that a constraint coming out of the canonicalization
phase cannot be rewritten any further from the inerts (but maybe /it/ can
rewrite an inert or still interact with an inert in a further phase in the
simplifier.

Note [Caching for canonicals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our plan with pre-canonicalization is to be able to solve a constraint
really fast from existing bindings in TcEvBinds. So one may think that
the condition (isCNonCanonical) is not necessary.  However consider
the following setup:

InertSet = { [W] d1 : Num t }
WorkList = { [W] d2 : Num t, [W] c : t ~ Int}

Now, we prioritize equalities, but in our concrete example
(should_run/mc17.hs) the first (d2) constraint is dealt with first,
because (t ~ Int) is an equality that only later appears in the
worklist since it is pulled out from a nested implication
constraint. So, let's examine what happens:

   - We encounter work item (d2 : Num t)

   - Nothing is yet in EvBinds, so we reach the interaction with inerts
     and set:
              d2 := d1
    and we discard d2 from the worklist. The inert set remains unaffected.

   - Now the equation ([W] c : t ~ Int) is encountered and kicks-out
     (d1 : Num t) from the inerts.  Then that equation gets
     spontaneously solved, perhaps. We end up with:
        InertSet : { [G] c : t ~ Int }
        WorkList : { [W] d1 : Num t}

   - Now we examine (d1), we observe that there is a binding for (Num
     t) in the evidence binds and we set:
             d1 := d2
     and end up in a loop!

Now, the constraints that get kicked out from the inert set are always
Canonical, so by restricting the use of the pre-canonicalizer to
NonCanonical constraints we eliminate this danger. Moreover, for
canonical constraints we already have good caching mechanisms
(effectively the interaction solver) and we are interested in reducing
things like superclasses of the same non-canonical constraint being
generated hence I don't expect us to lose a lot by introducing the
(isCNonCanonical) restriction.

A similar situation can arise in TcSimplify, at the end of the
solve_wanteds function, where constraints from the inert set are
returned as new work -- our substCt ensures however that if they are
not rewritten by subst, they remain canonical and hence we will not
attempt to solve them from the EvBinds. If on the other hand they did
get rewritten and are now non-canonical they will still not match the
EvBinds, so we are again good.
-}

-- Top-level canonicalization
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

canonicalize :: Ct -> TcS (StopOrContinue Ct)
canonicalize ct@(CNonCanonical { cc_ev = ev })
  = do { traceTcS "canonicalize (non-canonical)" (ppr ct)
       ; {-# SCC "canEvVar" #-}
         canEvNC ev }

canonicalize (CDictCan { cc_ev = ev
                       , cc_class  = cls
                       , cc_tyargs = xis })
  = {-# SCC "canClass" #-}
    canClass ev cls xis -- Do not add any superclasses
canonicalize (CTyEqCan { cc_ev = ev
                       , cc_tyvar  = tv
                       , cc_rhs    = xi
                       , cc_eq_rel = eq_rel })
  = {-# SCC "canEqLeafTyVarEq" #-}
    canEqTyVar ev eq_rel NotSwapped tv xi xi

canonicalize (CFunEqCan { cc_ev = ev
                        , cc_fun    = fn
                        , cc_tyargs = xis1
                        , cc_fsk    = fsk })
  = {-# SCC "canEqLeafFunEq" #-}
    canCFunEqCan ev fn xis1 fsk

canonicalize (CIrredEvCan { cc_ev = ev })
  = canIrred ev
canonicalize (CHoleCan { cc_ev = ev, cc_occ = occ, cc_hole = hole })
  = canHole ev occ hole

canEvNC :: CtEvidence -> TcS (StopOrContinue Ct)
-- Called only for non-canonical EvVars
canEvNC ev
  = case classifyPredType (ctEvPred ev) of
      ClassPred cls tys     -> do traceTcS "canEvNC:cls" (ppr cls <+> ppr tys)
                                  canClassNC ev cls tys
      EqPred eq_rel ty1 ty2 -> do traceTcS "canEvNC:eq" (ppr ty1 $$ ppr ty2)
                                  canEqNC    ev eq_rel ty1 ty2
      TuplePred tys         -> do traceTcS "canEvNC:tup" (ppr tys)
                                  canTuple   ev tys
      IrredPred {}          -> do traceTcS "canEvNC:irred" (ppr (ctEvPred ev))
                                  canIrred   ev
{-
************************************************************************
*                                                                      *
*                      Tuple Canonicalization
*                                                                      *
************************************************************************
-}

canTuple :: CtEvidence -> [PredType] -> TcS (StopOrContinue Ct)
canTuple ev tys
  = do { traceTcS "can_pred" (text "TuplePred!")
       ; let xcomp = EvTupleMk
             xdecomp x = zipWith (\_ i -> EvTupleSel x i) tys [0..]
       ; xCtEvidence ev (XEvTerm tys xcomp xdecomp)
       ; stopWith ev "Decomposed tuple constraint" }

{-
************************************************************************
*                                                                      *
*                      Class Canonicalization
*                                                                      *
************************************************************************
-}

canClass, canClassNC
   :: CtEvidence
   -> Class -> [Type] -> TcS (StopOrContinue Ct)
-- Precondition: EvVar is class evidence

-- The canClassNC version is used on non-canonical constraints
-- and adds superclasses.  The plain canClass version is used
-- for already-canonical class constraints (but which might have
-- been subsituted or somthing), and hence do not need superclasses

canClassNC ev cls tys
  = canClass ev cls tys
    `andWhenContinue` emitSuperclasses

canClass ev cls tys
  =   -- all classes do *nominal* matching
    ASSERT2( ctEvRole ev == Nominal, ppr ev $$ ppr cls $$ ppr tys )
    do { (xis, cos) <- flattenMany FM_FlattenAll ev (repeat Nominal) tys
       ; let co = mkTcTyConAppCo Nominal (classTyCon cls) cos
             xi = mkClassPred cls xis
             mk_ct new_ev = CDictCan { cc_ev = new_ev
                                     , cc_tyargs = xis, cc_class = cls }
       ; mb <- rewriteEvidence ev xi co
       ; traceTcS "canClass" (vcat [ ppr ev
                                   , ppr xi, ppr mb ])
       ; return (fmap mk_ct mb) }

emitSuperclasses :: Ct -> TcS (StopOrContinue Ct)
emitSuperclasses ct@(CDictCan { cc_ev = ev , cc_tyargs = xis_new, cc_class = cls })
            -- Add superclasses of this one here, See Note [Adding superclasses].
            -- But only if we are not simplifying the LHS of a rule.
 = do { newSCWorkFromFlavored ev cls xis_new
      -- Arguably we should "seq" the coercions if they are derived,
      -- as we do below for emit_kind_constraint, to allow errors in
      -- superclasses to be executed if deferred to runtime!
      ; continueWith ct }
emitSuperclasses _ = panic "emit_superclasses of non-class!"

{-
Note [Adding superclasses]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Since dictionaries are canonicalized only once in their lifetime, the
place to add their superclasses is canonicalisation (The alternative
would be to do it during constraint solving, but we'd have to be
extremely careful to not repeatedly introduced the same superclass in
our worklist). Here is what we do:

For Givens:
       We add all their superclasses as Givens.

For Wanteds:
       Generally speaking we want to be able to add superclasses of
       wanteds for two reasons:

       (1) Oportunities for improvement. Example:
                  class (a ~ b) => C a b
           Wanted constraint is: C alpha beta
           We'd like to simply have C alpha alpha. Similar
           situations arise in relation to functional dependencies.

       (2) To have minimal constraints to quantify over:
           For instance, if our wanted constraint is (Eq a, Ord a)
           we'd only like to quantify over Ord a.

       To deal with (1) above we only add the superclasses of wanteds
       which may lead to improvement, that is: equality superclasses or
       superclasses with functional dependencies.

       We deal with (2) completely independently in TcSimplify. See
       Note [Minimize by SuperClasses] in TcSimplify.


       Moreover, in all cases the extra improvement constraints are
       Derived. Derived constraints have an identity (for now), but
       we don't do anything with their evidence. For instance they
       are never used to rewrite other constraints.

       See also [New Wanted Superclass Work] in TcInteract.


For Deriveds:
       We do nothing.

Here's an example that demonstrates why we chose to NOT add
superclasses during simplification: [Comes from ticket #4497]

   class Num (RealOf t) => Normed t
   type family RealOf x

Assume the generated wanted constraint is:
   RealOf e ~ e, Normed e
If we were to be adding the superclasses during simplification we'd get:
   Num uf, Normed e, RealOf e ~ e, RealOf e ~ uf
==>
   e ~ uf, Num uf, Normed e, RealOf e ~ e
==> [Spontaneous solve]
   Num uf, Normed uf, RealOf uf ~ uf

While looks exactly like our original constraint. If we add the superclass again we'd loop.
By adding superclasses definitely only once, during canonicalisation, this situation can't
happen.
-}

newSCWorkFromFlavored :: CtEvidence -> Class -> [Xi] -> TcS ()
-- Returns superclasses, see Note [Adding superclasses]
newSCWorkFromFlavored flavor cls xis
  | isDerived flavor
  = return ()  -- Deriveds don't yield more superclasses because we will
               -- add them transitively in the case of wanteds.

  | isGiven flavor
  = do { let sc_theta = immSuperClasses cls xis
             xev_decomp x = zipWith (\_ i -> EvSuperClass x i) sc_theta [0..]
             xev = XEvTerm { ev_preds  =  sc_theta
                           , ev_comp   = panic "Can't compose for given!"
                           , ev_decomp = xev_decomp }
       ; xCtEvidence flavor xev }

  | isEmptyVarSet (tyCoVarsOfTypes xis)
  = return () -- Wanteds with no variables yield no deriveds.
              -- See Note [Improvement from Ground Wanteds]

  | otherwise -- Wanted case, just add those SC that can lead to improvement.
  = do { let sc_rec_theta = transSuperClasses cls xis
             impr_theta   = filter is_improvement_pty sc_rec_theta
             loc          = ctEvLoc flavor
       ; traceTcS "newSCWork/Derived" $ text "impr_theta =" <+> ppr impr_theta
       ; mapM_ (emitNewDerived loc) impr_theta }

is_improvement_pty :: PredType -> Bool
-- Either it's an equality, or has some functional dependency
is_improvement_pty ty = go (classifyPredType ty)
  where
    go (EqPred NomEq t1 t2) = not (t1 `tcEqType` t2)
    go (EqPred ReprEq _ _)  = False
    go (ClassPred cls _tys) = not $ null fundeps
                            where (_,fundeps) = classTvsFds cls
    go (TuplePred ts)       = any is_improvement_pty ts
    go (IrredPred {})       = True -- Might have equalities after reduction?

{-
************************************************************************
*                                                                      *
*                      Irreducibles canonicalization
*                                                                      *
************************************************************************
-}

canIrred :: CtEvidence -> TcS (StopOrContinue Ct)
-- Precondition: ty not a tuple and no other evidence form
canIrred old_ev
  = do { let old_ty = ctEvPred old_ev
       ; traceTcS "can_pred" (text "IrredPred = " <+> ppr old_ty)
       ; (xi,co) <- flatten FM_FlattenAll old_ev old_ty -- co :: xi ~ old_ty
       ; rewriteEvidence old_ev xi co `andWhenContinue` \ new_ev ->
    do { -- Re-classify, in case flattening has improved its shape
       ; case classifyPredType (ctEvPred new_ev) of
           ClassPred cls tys     -> canClassNC new_ev cls tys
           TuplePred tys         -> canTuple   new_ev tys
           EqPred eq_rel ty1 ty2 -> canEqNC new_ev eq_rel ty1 ty2
           _                     -> continueWith $
                                    CIrredEvCan { cc_ev = new_ev } } }

canHole :: CtEvidence -> OccName -> HoleSort -> TcS (StopOrContinue Ct)
canHole ev occ hole_sort
  = do { let ty = ctEvPred ev
       ; (xi,co) <- flatten FM_SubstOnly ev ty -- co :: xi ~ ty
       ; rewriteEvidence ev xi co `andWhenContinue` \ new_ev ->
    do { emitInsoluble (CHoleCan { cc_ev = new_ev
                                 , cc_occ = occ
                                 , cc_hole = hole_sort })
       ; stopWith new_ev "Emit insoluble hole" } }

{-
************************************************************************
*                                                                      *
*        Equalities
*                                                                      *
************************************************************************
-}

canEqNC :: CtEvidence -> EqRel -> Type -> Type -> TcS (StopOrContinue Ct)
canEqNC ev eq_rel ty1 ty2
  = can_eq_nc ev eq_rel ty1 ty1 ty2 ty2

can_eq_nc
   :: CtEvidence
   -> EqRel
   -> Type -> Type    -- LHS, after and before type-synonym expansion, resp
   -> Type -> Type    -- RHS, after and before type-synonym expansion, resp
   -> TcS (StopOrContinue Ct)
can_eq_nc ev eq_rel ty1 ps_ty1 ty2 ps_ty2
  = do { traceTcS "can_eq_nc" $
         vcat [ ppr ev, ppr eq_rel, ppr ty1, ppr ps_ty1, ppr ty2, ppr ps_ty2 ]
       ; rdr_env <- getGlobalRdrEnvTcS
       ; fam_insts <- getFamInstEnvs
       ; can_eq_nc' rdr_env fam_insts ev eq_rel ty1 ps_ty1 ty2 ps_ty2 }

can_eq_nc'
   :: GlobalRdrEnv   -- needed to see which newtypes are in scope
   -> FamInstEnvs    -- needed to unwrap data instances
   -> CtEvidence
   -> EqRel
   -> Type -> Type    -- LHS, after and before type-synonym expansion, resp
   -> Type -> Type    -- RHS, after and before type-synonym expansion, resp
   -> TcS (StopOrContinue Ct)

-- Expand synonyms first; see Note [Type synonyms and canonicalization]
can_eq_nc' _rdr_env _envs ev eq_rel ty1 ps_ty1 ty2 ps_ty2
  | Just ty1' <- tcView ty1 = can_eq_nc ev eq_rel ty1' ps_ty1 ty2  ps_ty2
  | Just ty2' <- tcView ty2 = can_eq_nc ev eq_rel ty1  ps_ty1 ty2' ps_ty2

-- Type family on LHS or RHS take priority over tyvars,
-- so that  tv ~ F ty gets flattened
-- Otherwise  F a ~ F a  might not get solved!
can_eq_nc' _rdr_env _envs ev eq_rel (TyConApp fn1 tys1) _ ty2 ps_ty2
  | isTypeFamilyTyCon fn1
  = can_eq_fam_nc ev eq_rel NotSwapped fn1 tys1 ty2 ps_ty2
can_eq_nc' _rdr_env _envs ev eq_rel ty1 ps_ty1 (TyConApp fn2 tys2) _
  | isTypeFamilyTyCon fn2
  = can_eq_fam_nc ev eq_rel IsSwapped fn2 tys2 ty1 ps_ty1

-- When working with ReprEq, unwrap newtypes next.
-- Otherwise, a ~ Id a wouldn't get solved
can_eq_nc' rdr_env envs ev ReprEq ty1 _ ty2 ps_ty2
  | Just (co, ty1') <- tcTopNormaliseNewTypeTF_maybe envs rdr_env ty1
  = can_eq_newtype_nc rdr_env ev NotSwapped co ty1 ty1' ty2 ps_ty2
can_eq_nc' rdr_env envs ev ReprEq ty1 ps_ty1 ty2 _
  | Just (co, ty2') <- tcTopNormaliseNewTypeTF_maybe envs rdr_env ty2
  = can_eq_newtype_nc rdr_env ev IsSwapped  co ty2 ty2' ty1 ps_ty1

-- First, get rid of casts
can_eq_nc' _rdr_env _envs ev eq_rel (CastTy ty1 co1) _ ty2 ps_ty2
  = canEqCast ev eq_rel NotSwapped ty1 co1 ty2 ps_ty2
can_eq_nc' _rdr_env _envs ev eq_rel ty1 ps_ty1 (CastTy ty2 co2) _
  = canEqCast ev eq_rel IsSwapped ty2 co2 ty1 ps_ty1

-- Type variable on LHS or RHS are next
can_eq_nc' _rdr_env _envs ev eq_rel (TyVarTy tv1) _ ty2 ps_ty2
  = canEqTyVar ev eq_rel NotSwapped tv1 ty2 ps_ty2
can_eq_nc' _rdr_env _envs ev eq_rel ty1 ps_ty1 (TyVarTy tv2) _
  = canEqTyVar ev eq_rel IsSwapped tv2 ty1 ps_ty1

----------------------
-- Otherwise try to decompose
----------------------

-- Literals
can_eq_nc' _rdr_env _envs ev eq_rel ty1@(LitTy l1) _ (LitTy l2) _
 | l1 == l2
  = do { when (isWanted ev) $
         setEvBind (ctev_evar ev)
                   (EvCoercion $ mkTcReflCo (eqRelRole eq_rel) ty1)
                   (ctev_loc ev)
       ; stopWith ev "Equal LitTy" }

-- Decomposable type constructor applications
-- Synonyms and type functions (which are not decomposable)
-- have already been dealt with
can_eq_nc' _rdr_env _envs ev eq_rel (TyConApp tc1 tys1) _ (TyConApp tc2 tys2) _
  | isDecomposableTyCon tc1
  , isDecomposableTyCon tc2
  = canDecomposableTyConApp ev eq_rel tc1 tys1 tc2 tys2

can_eq_nc' _rdr_env _envs ev _eq_rel (TyConApp tc1 _)      ps_ty1
                                     (ForAllTy (Anon _) _) ps_ty2
  | isDecomposableTyCon tc1
      -- The guard is important
      -- e.g.  (x -> y) ~ (F x y) where F has arity 1
      --       should not fail, but get the app/app case
  = canEqHardFailure ev ps_ty1 ps_ty2

can_eq_nc' _rdr_env _envs ev eq_rel (ForAllTy (Anon s1) t1) _
                                    (ForAllTy (Anon s2) t2) _
  = do { canDecomposableTyConAppOK ev eq_rel funTyCon [s1,t1] [s2,t2]
       ; stopWith ev "Decomposed FunTyCon" }

can_eq_nc' _rdr_env _envs ev _eq_rel (ForAllTy (Anon _) _) ps_ty1
                                     (TyConApp tc2 _)      ps_ty2
  | isDecomposableTyCon tc2
  = canEqHardFailure ev ps_ty1 ps_ty2

can_eq_nc' _rdr_env _envs ev eq_rel s1@(ForAllTy (Named {}) _) _
                                    s2@(ForAllTy (Named {}) _) _
 | CtWanted { ctev_loc = loc, ctev_evar = orig_ev } <- ev
 = do { let (bndrs1,body1) = tcSplitNamedForAllTysB s1
            (bndrs2,body2) = tcSplitNamedForAllTysB s2
      ; if not (equalLength bndrs1 bndrs2)
           || not (map binderVisibility bndrs1 == map binderVisibility bndrs2)
        then canEqHardFailure ev s1 s2
        else
          do { traceTcS "Creating implication for polytype equality" $ ppr ev
             ; ev_term <- deferTcSForAllEq (eqRelRole eq_rel) loc
                                           (bndrs1,body1) (bndrs2,body2)
             ; setEvBind orig_ev ev_term loc
             ; stopWith ev "Deferred polytype equality" } }
 | otherwise
 = do { traceTcS "Ommitting decomposition of given polytype equality" $
        pprEq s1 s2    -- See Note [Do not decompose given polytype equalities]
      ; stopWith ev "Discard given polytype equality" }

can_eq_nc' _rdr_env _envs ev eq_rel (AppTy {}) ps_ty1 _ ps_ty2
  | isGiven ev = try_decompose_app ev eq_rel ps_ty1 ps_ty2
  | otherwise  = can_eq_wanted_app ev eq_rel ps_ty1 ps_ty2
can_eq_nc' _rdr_env _envs ev eq_rel _ ps_ty1 (AppTy {}) ps_ty2
  | isGiven ev = try_decompose_app ev eq_rel ps_ty1 ps_ty2
  | otherwise  = can_eq_wanted_app ev eq_rel ps_ty1 ps_ty2

-- Everything else is a definite type error, eg LitTy ~ TyConApp
can_eq_nc' _rdr_env _envs ev _eq_rel _ ps_ty1 _ ps_ty2
  = do { traceTcS "can_eq_nc' catch-all case" (ppr ps_ty1 $$ ppr ps_ty2)
       ; canEqHardFailure ev ps_ty1 ps_ty2 }

------------
can_eq_fam_nc :: CtEvidence -> EqRel -> SwapFlag
              -> TyCon -> [TcType]
              -> TcType -> TcType
              -> TcS (StopOrContinue Ct)
-- Canonicalise a non-canonical equality of form (F tys ~ ty)
--   or the swapped version thereof
-- Flatten both sides and go round again
can_eq_fam_nc ev eq_rel swapped fn tys rhs ps_rhs
  = do { (xi_lhs, co_lhs) <- flattenFamApp FM_FlattenAll ev fn tys
       ; rewriteEqEvidence ev swapped xi_lhs rhs co_lhs
                           (mkTcReflCo (eqRelRole eq_rel) rhs)
         `andWhenContinue` \ new_ev ->
         can_eq_nc new_ev eq_rel xi_lhs xi_lhs rhs ps_rhs }

{-
Note [Eager reflexivity check]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have

  newtype X = MkX (Int -> X)

and

  [W] X ~R X

Naively, we would start unwrapping X and end up in a loop. Instead,
we do this eager reflexivity check. This is necessary only for representational
equality because the flattener technology deals with the similar case
(recursive type families) for nominal equality.

As an alternative, suppose we also have

  newtype Y = MkY (Int -> Y)

and now wish to prove

  [W] X ~R Y

This new Wanted will loop, expanding out the newtypes ever deeper looking
for a solid match or a solid discrepancy. Indeed, there is something
appropriate to this looping, because X and Y *do* have the same representation,
in the limit -- they're both (Fix ((->) Int)). However, no finitely-sized
coercion will ever witness it. This loop won't actually cause GHC to hang,
though, because of the stack-blowing check in can_eq_newtype_nc, along
with the fact that rewriteEqEvidence bumps the stack depth.

Note [AppTy reflexivity check]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider trying to prove (f a) ~R (f a). The AppTys in there can't
be decomposed, because representational equality isn't congruent with respect
to AppTy. So, when canonicalising the equality above, we get stuck and
would normally produce a CIrredEvCan. However, we really do want to
be able to solve (f a) ~R (f a). So, in the representational case only,
we do a reflexivity check.

(This would be sound in the nominal case, but unnecessary, and I [Richard
E.] am worried that it would slow down the common case.)
-}

------------------------
-- | We're able to unwrap a newtype. Update the bits accordingly.
can_eq_newtype_nc :: GlobalRdrEnv
                  -> CtEvidence           -- ^ :: ty1 ~ ty2
                  -> SwapFlag
                  -> TcCoercion           -- ^ :: ty1 ~ ty1'
                  -> TcType               -- ^ ty1
                  -> TcType               -- ^ ty1'
                  -> TcType               -- ^ ty2
                  -> TcType               -- ^ ty2, with type synonyms
                  -> TcS (StopOrContinue Ct)
can_eq_newtype_nc rdr_env ev swapped co ty1 ty1' ty2 ps_ty2
  = do { traceTcS "can_eq_newtype_nc" $
         vcat [ ppr ev, ppr swapped, ppr co, ppr ty1', ppr ty2 ]

         -- check for blowing our stack:
         -- See Note [Eager reflexivity check] for an example of
         -- when this is necessary
       ; dflags <- getDynFlags
       ; if isJust $ subGoalDepthExceeded (maxSubGoalDepth dflags)
                                          (ctLocDepth (ctEvLoc ev))
         then do { emitInsoluble (mkNonCanonical ev)
                 ; stopWith ev "unwrapping newtypes blew stack" }
         else do
       { if ty1 `eqType` ty2   -- See Note [Eager reflexivity check]
         then canEqReflexive ev ReprEq ty1
         else do
       { markDataConsAsUsed rdr_env (tyConAppTyCon ty1)
           -- we have actually used the newtype constructor here, so
           -- make sure we don't warn about importing it!

       ; rewriteEqEvidence ev swapped ty1' ps_ty2
                           (mkTcSymCo co) (mkTcReflCo Representational ps_ty2)
         `andWhenContinue` \ new_ev ->
         can_eq_nc new_ev ReprEq ty1' ty1' ty2 ps_ty2 }}}

-- | Mark all the datacons of the given 'TyCon' as used in this module,
-- avoiding "redundant import" warnings.
markDataConsAsUsed :: GlobalRdrEnv -> TyCon -> TcS ()
markDataConsAsUsed rdr_env tc = addUsedRdrNamesTcS
  [ mkRdrQual (is_as (is_decl imp_spec)) occ
  | dc <- tyConDataCons tc
  , let dc_name = dataConName dc
        occ  = nameOccName dc_name
  , gre : _               <- return $ lookupGRE_Name rdr_env dc_name
  , Imported (imp_spec:_) <- return $ gre_prov gre ]

-------------------------------------------------
can_eq_wanted_app :: CtEvidence -> EqRel -> TcType -> TcType
                  -> TcS (StopOrContinue Ct)
-- One or the other is an App; neither is a type variable
-- See Note [Canonicalising type applications]
can_eq_wanted_app ev eq_rel ty1 ty2
  = do { (xi1, co1) <- flatten FM_FlattenAll ev ty1
       ; (xi2, co2) <- flatten FM_FlattenAll ev ty2
        ; rewriteEqEvidence ev NotSwapped xi1 xi2 co1 co2
          `andWhenContinue` \ new_ev ->
          try_decompose_app new_ev eq_rel xi1 xi2 }

try_decompose_app :: CtEvidence -> EqRel
                  -> TcType -> TcType -> TcS (StopOrContinue Ct)
-- Preconditions: neither is a type variable
--                so can't turn it into an application if it
--                   doesn't look like one already
-- See Note [Canonicalising type applications]
try_decompose_app ev NomEq  ty1 ty2
  = try_decompose_nom_app ev ty1 ty2

try_decompose_app ev ReprEq ty1 ty2
  | ty1 `eqType` ty2   -- See Note [AppTy reflexivity check]
  = canEqReflexive ev ReprEq ty1

  | otherwise
  = canEqFailure ev ReprEq ty1 ty2

try_decompose_nom_app :: CtEvidence
                      -> TcType -> TcType -> TcS (StopOrContinue Ct)
-- Preconditions: like try_decompose_app, but also
--                ev has a nominal role
-- See Note [Canonicalising type applications]
try_decompose_nom_app ev ty1 ty2
   | AppTy s1 t1  <- ty1
   = case tcSplitAppTy_maybe ty2 of
       Nothing      -> canEqHardFailure ev ty1 ty2
       Just (s2,t2) -> do_decompose s1 t1 s2 t2

   | AppTy s2 t2 <- ty2
   = case tcSplitAppTy_maybe ty1 of
       Nothing      -> canEqHardFailure ev ty1 ty2
       Just (s1,t1) -> do_decompose s1 t1 s2 t2

   | otherwise  -- Neither is an AppTy
   = canEqNC ev NomEq ty1 ty2
   where
     -- do_decompose is like xCtEvidence, but recurses
     -- to try_decompose_nom_app to decompose a chain of AppTys
     do_decompose s1 t1 s2 t2
       | CtDerived { ctev_loc = loc } <- ev
       = do { unifyDeriveds loc [Nominal, Nominal] [s1, t1] [s2, t2]
            ; stopWith ev "Decomposed [D] AppTy" }
       | CtWanted { ctev_evar = evar, ctev_loc = loc } <- ev
       = do { let kind_loc = mkKindLoc t1 t2 loc
            ; co_s <- unifyWantedLikeEv ev loc      Nominal s1  s2
            ; co_h <- unifyWantedLikeEv ev kind_loc Nominal t1k t2k
            ; co_t <- unifyWantedLikeEv ev loc      Nominal t1  t2
            ; let co = mkTcAppCo co_s co_h co_t
            ; setEvBind evar (EvCoercion co) loc
            ; stopWith ev "Decomposed [W] AppTy" }
       | CtGiven { ctev_evtm = ev_tm, ctev_loc = loc } <- ev
       = do { let co   = evTermCoercion ev_tm
                  co_s = mkTcLRCo CLeft  co
                  co_h = mkTcKindAppCo   co
                  co_t = mkTcLRCo CRight co
            ; evar_s <- newGivenEvVar loc ( mkTcEqPredLikeEv ev s1  s2
                                          , EvCoercion co_s )
            ; evar_h <- newGivenEvVar loc ( mkTcEqPredLikeEv ev t1k t2k
                                          , EvCoercion co_h )
            ; evar_t <- newGivenEvVar loc ( mkTcEqPredLikeEv ev t1  t2
                                          , EvCoercion co_t )
            ; emitWorkNC [evar_h, evar_t]
            ; canEqNC evar_s NomEq s1 s2 }
       | otherwise  -- Can't happen
       = error "try_decompose_app"
       where
         t1k = typeKind t1
         t2k = typeKind t2

-----------------------
-- | Break apart an equality over a casted type
canEqCast :: CtEvidence
          -> EqRel
          -> SwapFlag
          -> TcType -> Coercion   -- LHS (res. RHS), the casted type
          -> TcType -> TcType     -- RHS (res. LHS), both normal and pretty
          -> TcS (StopOrContinue Ct)
canEqCast ev eq_rel swapped ty1 co1 _ty2 ps_ty2
  = do { let xpreds                = [unSwap swapped (mkTcEqPredLikeEv ev)
                                                     ty1 ps_ty2]

             -- uncasted_evt :: ty1 ~ ty2; result :: (ty1 |> co) ~ ty2
             xcomp ~[uncasted_evt] = EvCoercion $
                                     mk_coherence_co swapped
                                                     (evTermCoercion uncasted_evt)
                                                     co1
             xdecomp casted_evt    = case swapped of
               NotSwapped -> [EvCoercion $
                              mkTcCoherenceRightCo (mkTcReflCo role ty1) co1
                              `mkTcTransCo` (evTermCoercion casted_evt)]
               IsSwapped  -> [EvCoercion $
                              evTermCoercion casted_evt `mkTcTransCo`
                              mkTcCoherenceLeftCo (mkTcReflCo role ty1) co1]
             xev = XEvTerm xpreds xcomp xdecomp
       ; xCtEvidence ev xev
       ; stopWith ev "Decomposed Cast" }
  where
    mk_coherence_co NotSwapped = mkTcCoherenceLeftCo
    mk_coherence_co IsSwapped  = mkTcCoherenceRightCo

    role = eqRelRole eq_rel

------------------------
canDecomposableTyConApp :: CtEvidence -> EqRel
                        -> TyCon -> [TcType]
                        -> TyCon -> [TcType]
                        -> TcS (StopOrContinue Ct)
-- See Note [Decomposing TyConApps]
canDecomposableTyConApp ev eq_rel tc1 tys1 tc2 tys2
  | tc1 /= tc2 || length tys1 /= length tys2
    -- Fail straight away for better error messages
  = let eq_failure
          | isDataFamilyTyCon tc1 || isDataFamilyTyCon tc2
                -- See Note [Use canEqFailure in canDecomposableTyConApp]
          = canEqFailure ev eq_rel
          | otherwise
          = canEqHardFailure ev in
    eq_failure (mkTyConApp tc1 tys1) (mkTyConApp tc2 tys2)

  | otherwise
  = do { traceTcS "canDecomposableTyConApp"
                  (ppr ev $$ ppr eq_rel $$ ppr tc1 $$ ppr tys1 $$ ppr tys2)
       ; canDecomposableTyConAppOK ev eq_rel tc1 tys1 tys2
       ; stopWith ev "Decomposed TyConApp" }

{-
Note [Use canEqFailure in canDecomposableTyConApp]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We must use canEqFailure, not canEqHardFailure here, because there is
the possibility of success if working with a representational equality.
Here is the case:

  type family TF a where TF Char = Bool
  data family DF a
  newtype instance DF Bool = MkDF Int

Suppose we are canonicalising (Int ~R DF (T a)), where we don't yet
know `a`. This is *not* a hard failure, because we might soon learn
that `a` is, in fact, Char, and then the equality succeeds.
-}

canDecomposableTyConAppOK :: CtEvidence -> EqRel
                          -> TyCon -> [TcType] -> [TcType]
                          -> TcS ()
-- Precondition: tys1 and tys2 are the same length, hence "OK"
canDecomposableTyConAppOK ev eq_rel tc tys1 tys2
  = case ev of
     CtDerived { ctev_loc = loc }
        -> unifyDeriveds loc tc_roles tys1 tys2

     CtWanted { ctev_evar = evar, ctev_loc = loc }
        -> do { cos <- zipWith3M (unifyWantedLikeEv ev loc) tc_roles tys1 tys2
              ; setEvBind evar (EvCoercion (mkTcTyConAppCo role tc cos)) loc }

     CtGiven { ctev_evtm = ev_tm, ctev_loc = loc }
        -> do { let ev_co = evTermCoercion ev_tm
              ; given_evs <- newGivenEvVars loc $
                             [ ( mkTcEqPredBR boxity r ty1 ty2
                               , EvCoercion (mkTcNthCo i ev_co) )
                             | (r, ty1, ty2, i) <- zip4 tc_roles tys1 tys2 [0..]
                             , r /= Phantom
                             , not (isCoercionTy ty1) && not (isCoercionTy ty2) ]
              ; emitWorkNC given_evs }
  where
    boxity   = getEqPredBoxity (ctEvPred ev)
    role     = eqRelRole eq_rel
    tc_roles = tyConRolesX role tc

-- | Call when canonicalizing an equality fails, but if the equality is
-- representational, there is some hope for the future.
-- Examples in Note [Flatten irreducible representational equalities]
canEqFailure :: CtEvidence -> EqRel
             -> TcType -> TcType -> TcS (StopOrContinue Ct)
canEqFailure ev ReprEq ty1 ty2
  = do { -- See Note [Flatten irreducible representational equalities]
         (xi1, co1) <- flatten FM_FlattenAll ev ty1
       ; (xi2, co2) <- flatten FM_FlattenAll ev ty2
       ; traceTcS "canEqFailure with ReprEq" $
         vcat [ ppr ev, ppr ty1, ppr ty2, ppr xi1, ppr xi2 ]
       ; if xi1 `eqType` ty1 && xi2 `eqType` ty2
         then continueWith (CIrredEvCan { cc_ev = ev })  -- co1/2 must be refl
         else rewriteEqEvidence ev NotSwapped xi1 xi2 co1 co2
              `andWhenContinue` \ new_ev ->
              can_eq_nc new_ev ReprEq xi1 xi1 xi2 xi2 }
canEqFailure ev NomEq ty1 ty2 = canEqHardFailure ev ty1 ty2

-- | Call when canonicalizing an equality fails with utterly no hope.
canEqHardFailure :: CtEvidence
                 -> TcType -> TcType -> TcS (StopOrContinue Ct)
-- See Note [Make sure that insolubles are fully rewritten]
canEqHardFailure ev ty1 ty2
  = do { (s1, co1) <- flatten FM_SubstOnly ev ty1
       ; (s2, co2) <- flatten FM_SubstOnly ev ty2
       ; rewriteEqEvidence ev NotSwapped s1 s2 co1 co2
         `andWhenContinue` \ new_ev ->
    do { emitInsoluble (mkNonCanonical new_ev)
       ; stopWith new_ev "Definitely not equal" }}

{-
Note [Flatten irreducible representational equalities]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we can't make any progress with a representational equality, but
we haven't given up all hope, we must flatten before producing the
CIrredEvCan. There are two reasons to do this:

  * See case in Note [Use canEqFailure in canDecomposableTyConApp].
    Flattening here can expose that we know enough information to unwrap
    a newtype.

  * This case, which was encountered in the testsuite (T9117_3):

      work item: [W] c1: f a ~R g a
      inert set: [G] c2: g ~R f

    In can_eq_app, we try to flatten the LHS of c1. This causes no effect,
    because `f` cannot be rewritten. So, we go to can_eq_flat_app. Without
    flattening the RHS, the reflexivity check fails, and we give up. However,
    flattening the RHS rewrites `g` to `f`, the reflexivity check succeeds,
    and we go on to glory.

Note [Decomposing TyConApps]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we see (T s1 t1 ~ T s2 t2), then we can just decompose to
  (s1 ~ s2, t1 ~ t2)
and push those back into the work list.  But if
  s1 = K k1    s2 = K k2
then we will jus decomopose s1~s2, and it might be better to
do so on the spot.  An important special case is where s1=s2,
and we get just Refl.

So canDecomposableTyCon is a fast-path decomposition that uses
unifyWanted etc to short-cut that work.

Note [Canonicalising type applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given (s1 t1) ~ ty2, how should we proceed?
The simple things is to see if ty2 is of form (s2 t2), and
decompose.  By this time s1 and s2 can't be saturated type
function applications, because those have been dealt with
by an earlier equation in can_eq_nc, so it is always sound to
decompose.

However, over-eager decomposition gives bad error messages
for things like
   a b ~ Maybe c
   e f ~ p -> q
Suppose (in the first example) we already know a~Array.  Then if we
decompose the application eagerly, yielding
   a ~ Maybe
   b ~ c
we get an error        "Can't match Array ~ Maybe",
but we'd prefer to get "Can't match Array b ~ Maybe c".

So instead can_eq_wanted_app flattens the LHS and RHS before using
try_decompose_app to decompose it.

Note [Make sure that insolubles are fully rewritten]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When an equality fails, we still want to rewrite the equality
all the way down, so that it accurately reflects
 (a) the mutable reference substitution in force at start of solving
 (b) any ty-binds in force at this point in solving
See Note [Kick out insolubles] in TcInteract.
And if we don't do this there is a bad danger that
TcSimplify.applyTyVarDefaulting will find a variable
that has in fact been substituted.

Note [Do not decompose Given polytype equalities]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider [G] (forall a. t1 ~ forall a. t2).  Can we decompose this?
No -- what would the evidence look like?  So instead we simply discard
this given evidence.


Note [Combining insoluble constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As this point we have an insoluble constraint, like Int~Bool.

 * If it is Wanted, delete it from the cache, so that subsequent
   Int~Bool constraints give rise to separate error messages

 * But if it is Derived, DO NOT delete from cache.  A class constraint
   may get kicked out of the inert set, and then have its functional
   dependency Derived constraints generated a second time. In that
   case we don't want to get two (or more) error messages by
   generating two (or more) insoluble fundep constraints from the same
   class constraint.

Note [No top-level newtypes on RHS of representational equalities]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we're in this situation:

 work item:  [W] c1 : a ~R b
     inert:  [G] c2 : b ~R Id a

where
  newtype Id a = Id a

Further, suppose flattening `a` doesn't do anything. Then, we'll flatten the
RHS of c1 and have a new [W] c3 : a ~R Id a. If we just blindly proceed, we'll
fail in canEqTyVar2 with an occurs-check. What we really need to do is to
unwrap the `Id a` in the RHS. This is exactly analogous to the requirement for
no top-level type families on the RHS of a nominal equality. The only
annoyance is that the flattener doesn't do this work for us when flattening
the RHS, so we have to catch this case here and then go back to the beginning
of can_eq_nc. We know that this can't loop forever because we require that
flattening the RHS actually made progress. (If it didn't, then we really
*should* fail with an occurs-check!)

-}

canCFunEqCan :: CtEvidence
             -> TyCon -> [TcType]   -- LHS
             -> TcTyVar             -- RHS
             -> TcS (StopOrContinue Ct)
-- ^ Canonicalise a CFunEqCan.  We know that
--     the arg types are already flat,
-- and the RHS is a fsk, which we must *not* substitute.
-- So just substitute in the LHS
canCFunEqCan ev fn tys fsk
  = do { (tys', cos) <- flattenMany FM_FlattenAll ev (repeat Nominal) tys
                        -- cos :: tys' ~ tys
       ; let lhs_co  = mkTcTyConAppCo Nominal fn cos
                        -- :: F tys' ~ F tys
             new_lhs = mkTyConApp fn tys'
             fsk_ty  = mkOnlyTyVarTy fsk
       ; rewriteEqEvidence ev NotSwapped new_lhs fsk_ty
                           lhs_co (mkTcNomReflCo fsk_ty)
         `andWhenContinue` \ ev' ->
    do { extendFlatCache fn tys' (ctEvCoercion ev', fsk_ty, ctEvFlavour ev')
       ; continueWith (CFunEqCan { cc_ev = ev', cc_fun = fn
                                 , cc_tyargs = tys', cc_fsk = fsk }) } }

---------------------
canEqTyVar :: CtEvidence -> EqRel -> SwapFlag
           -> TcTyVar
           -> TcType -> TcType
           -> TcS (StopOrContinue Ct)
-- A TyVar on LHS, but so far un-zonked
canEqTyVar ev eq_rel swapped tv1 ty2 ps_ty2              -- ev :: tv ~ s2
  = do { traceTcS "canEqTyVar" (ppr tv1 $$ ppr ty2 $$ ppr swapped)
       ; let fmode = mkFlattenEnv FM_FlattenAll ev  -- the FM_ param is ignored
       ; mb_yes <- flattenTyVarOuter fmode tv1
       ; case mb_yes of
         { FTRFollowed ty1 co1 -> -- co1 :: ty1 ~ tv1
             do { traceTcS "canEqTyVar2"
                           (vcat [ ppr tv1, ppr ty2, ppr swapped
                                 , ppr ty1 , ppUnless (isDerived ev) (ppr co1)])
                ; rewriteEqEvidence ev swapped ty1 ps_ty2
                                    (mkTcCoercion co1)
                                    (mkTcReflCo (eqRelRole eq_rel) ps_ty2)
                  `andWhenContinue` \ new_ev ->
                  can_eq_nc new_ev eq_rel ty1 ty1 ty2 ps_ty2 }

         ; FTRCasted tv1' kind_co ->
    do { -- FM_Avoid commented out: see Note [Lazy flattening] in TcFlatten
         -- let fmode = FE { fe_ev = ev, fe_mode = FM_Avoid tv1' True }
         -- Flatten the RHS less vigorously, to avoid gratuitous flattening
         -- True <=> xi2 should not itself be a type-function application
       ; (xi2, co2) <- flatten FM_FlattenAll ev ps_ty2 -- co2 :: xi2 ~ ps_ty2
                      -- Use ps_ty2 to preserve type synonyms if poss
       ; traceTcS "canEqTyVar flat LHS"
           (vcat [ ppr tv1', ppr kind_co, ppr (coercionKind kind_co)
                 , ppr ty2, ppr swapped, ppr xi2 ])
       ; dflags <- getDynFlags 
       ; case eq_rel of
      -- See Note [No top-level newtypes on RHS of representational equalities]
           ReprEq
             | Just (tc2, _) <- tcSplitTyConApp_maybe xi2
             , isNewTyCon tc2
             , not (ps_ty2 `eqType` xi2)
             -> do { let ty1  = mkOnlyTyVarTy tv1'
                         kco  = mkSymCo kind_co
                         xi1  = ty1 `mkCastTy` kco
                         role = eqRelRole eq_rel
                         co1  = mkTcReflCo role ty1 `mkTcCoherenceLeftCo` kco
                   ; traceTcS "canEqTyVar exposed newtype"
                       (vcat [ ppr tv1', ppr ps_ty2, ppr xi2, ppr tc2 ])
                   ; rewriteEqEvidence ev swapped xi1 xi2
                                       co1 co2
                     `andWhenContinue` \ new_ev ->
                     can_eq_nc new_ev eq_rel xi1 xi1 xi2 xi2 }
           _ -> canEqTyVar2 dflags ev eq_rel swapped tv1' kind_co xi2 co2 } } }

canEqTyVar2 :: DynFlags
            -> CtEvidence   -- olhs ~ orhs (or, if swapped, orhs ~ olhs)
            -> EqRel
            -> SwapFlag
            -> TcTyVar      -- olhs
            -> Coercion     -- :: kind nrhs ~R kind olhs
            -> TcType       -- nrhs
            -> TcCoercion   -- nrhs ~ orhs
            -> TcS (StopOrContinue Ct)
-- LHS is an inert type variable,
-- and RHS is fully rewritten, but with type synonyms
-- preserved as much as possible

canEqTyVar2 dflags ev eq_rel swapped tv1 kco xi2 co2
  | Just (tv2, kco2) <- getCastedTyVar_maybe xi2
        -- kco2 :: kind tv2 ~R kind xi2
  = do { traceTcS "canEqTyVarTyVar from canEqTyVar2" (ppr tv1 $$ ppr tv2)
       ; canEqTyVarTyVar ev eq_rel swapped tv1 tv2 (kco2 `mkTransCo` kco)
                         (co2 `mkTcCoherenceLeftCo` mkSymCo kco2) }

  | OC_OK xi2' <- occurCheckExpand dflags tv1 casted_xi2  -- No occurs check
  = rewriteEqEvidence ev swapped xi1 xi2' co1 casted_co2
                -- Ensure that the new goal has enough type synonyms
                -- expanded by the occurCheckExpand; hence using xi2' here
                -- See Note [occurCheckExpand]
    `andWhenContinue` \ new_ev ->
    homogeniseRhsKind new_ev eq_rel xi1 xi2' $ \new_new_ev xi2'' ->
    CTyEqCan { cc_ev = new_new_ev, cc_tyvar = tv1
             , cc_rhs = xi2'', cc_eq_rel = eq_rel }

  | otherwise  -- Occurs check error
  = do { traceTcS "canEqTyVar2 occurs check error" (ppr tv1 $$ ppr casted_xi2)
       ; rewriteEqEvidence ev swapped xi1 casted_xi2 co1 casted_co2
         `andWhenContinue` \ new_ev ->
          case eq_rel of
            NomEq  -> do { emitInsoluble (mkNonCanonical new_ev)
              -- If we have a ~ [a], it is not canonical, and in particular
              -- we don't want to rewrite existing inerts with it, otherwise
              -- we'd risk divergence in the constraint solver
                         ; stopWith new_ev "Occurs check" }

              -- A representational equality with an occurs-check problem isn't
              -- insoluble! For example:
              --   a ~R b a
              -- We might learn that b is the newtype Id.
              -- But, the occurs-check certainly prevents the equality from being
              -- canonical, and we might loop if we were to use it in rewriting.
            ReprEq -> do { traceTcS "Occurs-check in representational equality"
                              (ppr xi1 $$ ppr casted_xi2)
                         ; continueWith (CIrredEvCan { cc_ev = new_ev }) } }
  where
    xi1 = mkOnlyTyVarTy tv1
    co1 = mkTcReflCo (eqRelRole eq_rel) xi1

    casted_xi2 = xi2 `mkCastTy` kco
    casted_co2 = co2 `mkTcCoherenceLeftCo` kco

canEqTyVarTyVar :: CtEvidence           -- tv1 ~ orhs (or orhs ~ tv1, if swapped)
                -> EqRel
                -> SwapFlag
                -> TcTyVar -> TcTyVar   -- tv2, tv2
                -> Coercion             -- :: kind tv2 ~R kind tv1
                -> TcCoercion           -- tv2 ~ orhs
                -> TcS (StopOrContinue Ct)
-- Both LHS and RHS rewrote to a type variable,
-- If swapped = NotSwapped, then
--     rw_orhs = tv1, rw_olhs = orhs
--     rw_nlhs = tv2, rw_nrhs = xi1
-- See Note [Canonical orientation for tyvar/tyvar equality constraints]
canEqTyVarTyVar ev eq_rel swapped tv1 tv2 kco co2
  | tv1 == tv2
  = do { when (isWanted ev) $
         ASSERT( tcCoercionRole co2 == eqRelRole eq_rel )
         ASSERT( isReflCo kco )
         setEvBind (ctev_evar ev) (EvCoercion (maybeSym swapped co2)) (ctev_loc ev)
       ; stopWith ev "Equal tyvars" }

    -- See Note [Orient equalities with flatten-meta-vars on the left] in TcFlatten
  | isFmvTyVar tv1  = no_swap
  | isFmvTyVar tv2  = do_swap

  | swap_over       = do_swap
  | otherwise       = no_swap
  where
    xi1 = mkOnlyTyVarTy tv1
    xi2 = mkOnlyTyVarTy tv2
    co1 = mkTcReflCo (eqRelRole eq_rel) xi1

    no_swap = canon_eq swapped            tv1 xi1 xi2 kco           co1 co2
    do_swap = canon_eq (flipSwap swapped) tv2 xi2 xi1 (mkSymCo kco) co2 co1

    canon_eq swapped tv1 xi1 xi2 kco co1 co2
        -- ev  : tv1 ~ orhs  (not swapped) or   orhs ~ tv1   (swapped)
        -- kco : kind tv1 ~ kind xi2
        -- co1 : xi1 ~ tv1
        -- co2 : xi2 ~ tv2
      = do { traceTcS "canEqTyVarTyVar"
               (vcat [ ppr swapped
                     , ppr tv1 <+> dcolon <+> ppr (tyVarKind tv1)
                     , ppr xi1 <+> dcolon <+> ppr (typeKind xi1)
                     , ppr xi2 <+> dcolon <+> ppr (typeKind xi2)
                     , ppr kco <+> dcolon <+> ppr (coercionKind kco)
                     , ppr co1 <+> dcolon <+> ppr (tcCoercionKind co1)
                     , ppr co2 <+> dcolon <+> ppr (tcCoercionKind co2) ])
           ; rewriteEqEvidence ev swapped xi1 casted_xi2
                                          co1 casted_co2
             `andWhenContinue` \ new_ev ->
             homogeniseRhsKind new_ev eq_rel xi1 casted_xi2 $ \new_new_ev xi2' ->
             CTyEqCan { cc_ev = new_new_ev, cc_tyvar = tv1
                      , cc_rhs = xi2', cc_eq_rel = eq_rel } }
      where
        casted_xi2 = xi2 `mkCastTy` kco
        casted_co2 = co2 `mkTcCoherenceLeftCo` kco

    swap_over
      -- If tv1 is touchable, swap only if tv2 is also
      -- touchable and it's strictly better to update the latter
      -- But see Note [Avoid unnecessary swaps]
      | Just lvl1 <- metaTyVarTcLevel_maybe tv1
      = case metaTyVarTcLevel_maybe tv2 of
          Nothing   -> False
          Just lvl2 | lvl2 `strictlyDeeperThan` lvl1 -> True
                    | lvl1 `strictlyDeeperThan` lvl2 -> False
                    | otherwise                      -> nicer_to_update_tv2

      -- So tv1 is not a meta tyvar
      -- If only one is a meta tyvar, put it on the left
      -- This is not because it'll be solved; but because
      -- the floating step looks for meta tyvars on the left
      | isMetaTyVar tv2 = True

      -- So neither is a meta tyvar

      -- If only one is a flatten tyvar, put it on the left
      -- See Note [Eliminate flat-skols]
      | not (isFlattenTyVar tv1), isFlattenTyVar tv2 = True

      | otherwise = False

    nicer_to_update_tv2
      =  (isSigTyVar tv1                 && not (isSigTyVar tv2))
      || (isSystemName (Var.varName tv2) && not (isSystemName (Var.varName tv1)))

-- | Solve a reflexive equality constraint
canEqReflexive :: CtEvidence    -- ty ~ ty
               -> EqRel
               -> TcType        -- ty
               -> TcS (StopOrContinue Ct)   -- always Stop
canEqReflexive ev eq_rel ty
  = do { when (isWanted ev) $
         setEvBind (ctev_evar ev)
                   (EvCoercion $ mkTcReflCo (eqRelRole eq_rel) ty)
                   (ctev_loc ev)
       ; stopWith ev "Solved by reflexivity" }

-- See Note [Equalities with incompatible kinds]
homogeniseRhsKind :: CtEvidence -- ^ the evidence to homogenise
                  -> EqRel
                  -> TcType              -- ^ original LHS
                  -> Xi                  -- ^ original RHS
                  -> (CtEvidence -> Xi -> Ct)
                           -- ^ how to build the homogenised constraint;
                           -- the 'Xi' is the new RHS
                  -> TcS (StopOrContinue Ct)
homogeniseRhsKind ev eq_rel lhs rhs build_ct
  | k1 `eqType` k2
  = continueWith (build_ct ev rhs)

  | CtGiven { ctev_evtm = tm } <- ev
    -- tm :: (lhs :: k1) ~ (rhs :: k2)
  = do { kind_ev_id <- newBoundEvVarId kind_pty
                                       (EvCoercion $
                                        mkTcKindCo $ evTermCoercion tm)
           -- kind_ev_id :: (k1 :: *) ~# (k2 :: *)
       ; let kind_ev = CtGiven { ctev_pred = kind_pty
                               , ctev_evtm = EvId kind_ev_id
                               , ctev_loc  = kind_loc }
             homo_co = mkSymCo $ mkCoVarCo kind_ev_id
             rhs'    = mkCastTy rhs homo_co
       ; traceTcS "Hetero equality gives rise to given kind equality"
           (ppr kind_ev_id <+> dcolon <+> ppr kind_pty)
       ; emitWorkNC [kind_ev]
       ; type_ev <- newGivenEvVar loc
                      ( mkTcEqPredLikeEv ev lhs rhs'
                      , EvCoercion $
                        mkTcCoherenceRightCo (evTermCoercion tm) homo_co )
          -- type_ev :: (lhs :: k1) ~ ((rhs |> sym kind_ev_id) :: k1)
       ; continueWith (build_ct type_ev rhs') }

  | CtWanted { ctev_evar = evar } <- ev
    -- evar :: (lhs :: k1) ~ (rhs :: k2)
  = do { mb_kind_ev <- newWantedEvVar kind_loc kind_pty
             -- kind_ev :: (k1 :: *) ~ (k2 :: *)
       ; traceTcS "Hetero equality gives rise to wanted kind equality"
           (ppr (getEvTerm mb_kind_ev))
       ; emitWorkNC $ freshGoals [mb_kind_ev]
       ; let kind_evt = getEvTerm mb_kind_ev
       ; kind_co <- dirtyTcCoToCo (evTermCoercion kind_evt)
       ; let homo_co   = mkSymCo kind_co
           -- homo_co :: k2 ~ k1
             rhs'      = mkCastTy rhs homo_co
             homo_pred = mkTcEqPredLikeEv ev lhs rhs'
       ; mb_type_ev <- newWantedEvVar loc homo_pred
          -- type_ev :: (lhs :: k1) ~ (rhs |> sym kind_ev :: k1)
       ; let type_evt = getEvTerm mb_type_ev
       ; setEvBind evar
                   (EvCoercion $
                    (evTermCoercion type_evt) `mkTcTransCo`
                    (mkTcReflCo (eqRelRole eq_rel) rhs
                     `mkTcCoherenceLeftCo` homo_co))
                   loc
          -- evar := type_ev ; <rhs> |> homo_co :: (lhs :: k1) ~ (rhs :: k2)
       ; case mb_type_ev of
           Fresh  type_ev -> continueWith (build_ct type_ev rhs')
           Cached _       -> stopWith ev  "cached homogenized equality" }

  | otherwise   -- CtDerived {} <- ev
  = do { emitNewDerived kind_loc kind_pty
       ; continueWith (CIrredEvCan { cc_ev = ev }) }
           -- we don't have a name for the kind-level CtDerived,
           -- so we can't homogenise. Oh well.
  where
    k1 = typeKind lhs
    k2 = typeKind rhs

    kind_pty = mkHeteroReprPrimEqPred liftedTypeKind liftedTypeKind k1 k2
    kind_loc = mkKindLoc lhs rhs loc

    loc = ctev_loc ev

{-
Note [Canonical orientation for tyvar/tyvar equality constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we have a ~ b where both 'a' and 'b' are TcTyVars, which way
round should be oriented in the CTyEqCan?  The rules, implemented by
canEqTyVarTyVar, are these

 * If either is a flatten-meta-variables, it goes on the left.

 * If one is a strict sub-kind of the other e.g.
       (alpha::?) ~ (beta::*)
   orient them so RHS is a subkind of LHS.  That way we will replace
   'a' with 'b', correctly narrowing the kind.
   This establishes the subkind invariant of CTyEqCan.

 * Put a meta-tyvar on the left if possible
       alpha[3] ~ r

 * If both are meta-tyvars, put the more touchable one (deepest level
   number) on the left, so there is the best chance of unifying it
        alpha[3] ~ beta[2]

 * If both are meta-tyvars and both at the same level, put a SigTv
   on the right if possible
        alpha[2] ~ beta[2](sig-tv)
   That way, when we unify alpha := beta, we don't lose the SigTv flag.

 * Put a meta-tv with a System Name on the left if possible so it
   gets eliminated (improves error messages)

 * If one is a flatten-skolem, put it on the left so that it is
   substituted out  Note [Elminate flat-skols]
        fsk ~ a

Note [Avoid unnecessary swaps]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we swap without actually improving matters, we can get an infnite loop.
Consider
    work item:  a ~ b
   inert item:  b ~ c
We canonicalise the work-time to (a ~ c).  If we then swap it before
aeding to the inert set, we'll add (c ~ a), and therefore kick out the
inert guy, so we get
   new work item:  b ~ c
   inert item:     c ~ a
And now the cycle just repeats

Note [Eliminate flat-skols]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have  [G] Num (F [a])
then we flatten to
     [G] Num fsk
     [G] F [a] ~ fsk
where fsk is a flatten-skolem (FlatSkol). Suppose we have
      type instance F [a] = a
then we'll reduce the second constraint to
     [G] a ~ fsk
and then replace all uses of 'a' with fsk.  That's bad because
in error messages intead of saying 'a' we'll say (F [a]).  In all
places, including those where the programmer wrote 'a' in the first
place.  Very confusing!  See Trac #7862.

Solution: re-orient a~fsk to fsk~a, so that we preferentially eliminate
the fsk.

Note [Equalities with incompatible kinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
canEqLeaf is about to make a CTyEqCan or CFunEqCan; but both have the
invariant that LHS and RHS satisfy the kind invariants for CTyEqCan,
CFunEqCan.  What if we try to unify two things with incompatible
kinds?

eg    a ~ b  where a::*, b::*->*
or    a ~ b  where a::*, b::k, k is a kind variable

The CTyEqCan compatKind invariant is important.  If we make a CTyEqCan
for a~b, then we might well *substitute* 'b' for 'a', and that might make
a well-kinded type ill-kinded; and that is bad (eg typeKind can crash, see
Trac #7696).

So instead for these ill-kinded equalities we homogenise the RHS of the
equality, emitting new constraints as necessary.

Note [Type synonyms and canonicalization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We treat type synonym applications as xi types, that is, they do not
count as type function applications.  However, we do need to be a bit
careful with type synonyms: like type functions they may not be
generative or injective.  However, unlike type functions, they are
parametric, so there is no problem in expanding them whenever we see
them, since we do not need to know anything about their arguments in
order to expand them; this is what justifies not having to treat them
as specially as type function applications.  The thing that causes
some subtleties is that we prefer to leave type synonym applications
*unexpanded* whenever possible, in order to generate better error
messages.

If we encounter an equality constraint with type synonym applications
on both sides, or a type synonym application on one side and some sort
of type application on the other, we simply must expand out the type
synonyms in order to continue decomposing the equality constraint into
primitive equality constraints.  For example, suppose we have

  type F a = [Int]

and we encounter the equality

  F a ~ [b]

In order to continue we must expand F a into [Int], giving us the
equality

  [Int] ~ [b]

which we can then decompose into the more primitive equality
constraint

  Int ~ b.

However, if we encounter an equality constraint with a type synonym
application on one side and a variable on the other side, we should
NOT (necessarily) expand the type synonym, since for the purpose of
good error messages we want to leave type synonyms unexpanded as much
as possible.  Hence the ps_ty1, ps_ty2 argument passed to canEqTyVar.


Note [occurCheckExpand]
~~~~~~~~~~~~~~~~~~~~~~~
There is a subtle point with type synonyms and the occurs check that
takes place for equality constraints of the form tv ~ xi.  As an
example, suppose we have

  type F a = Int

and we come across the equality constraint

  a ~ F a

This should not actually fail the occurs check, since expanding out
the type synonym results in the legitimate equality constraint a ~
Int.  We must actually do this expansion, because unifying a with F a
will lead the type checker into infinite loops later.  Put another
way, canonical equality constraints should never *syntactically*
contain the LHS variable in the RHS type.  However, we don't always
need to expand type synonyms when doing an occurs check; for example,
the constraint

  a ~ F b

is obviously fine no matter what F expands to. And in this case we
would rather unify a with F b (rather than F b's expansion) in order
to get better error messages later.

So, when doing an occurs check with a type synonym application on the
RHS, we use some heuristics to find an expansion of the RHS which does
not contain the variable from the LHS.  In particular, given

  a ~ F t1 ... tn

we first try expanding each of the ti to types which no longer contain
a.  If this turns out to be impossible, we next try expanding F
itself, and so on.  See Note [Occurs check expansion] in TcType
-}

{-
************************************************************************
*                                                                      *
                  Evidence transformation
*                                                                      *
************************************************************************
-}

{-
Note [xCtEvidence]
~~~~~~~~~~~~~~~~~~
A call might look like this:

    xCtEvidence ev evidence-transformer

  ev is Given   => use ev_decomp to create new Givens for ev_preds,
                   and return them

  ev is Wanted  => create new wanteds for ev_preds,
                   use ev_comp to bind ev,
                   return fresh wanteds (ie ones not cached in inert_cans or solved)

  ev is Derived => create new deriveds for ev_preds
                      (unless cached in inert_cans or solved)

Note: The [CtEvidence] returned is a subset of the subgoal-preds passed in
      Ones that are already cached are not returned

Example
    ev : Tree a b ~ Tree c d
    xCtEvidence ev [a~c, b~d] (XEvTerm { ev_comp = \[c1 c2]. <Tree> c1 c2
                                       , ev_decomp = \c. [nth 1 c, nth 2 c] })
              (\fresh-goals.  stuff)

Note [Bind new Givens immediately]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For Givens we make new EvVars and bind them immediately. We don't worry
about caching, but we don't expect complicated calculations among Givens.
It is important to bind each given:
      class (a~b) => C a b where ....
      f :: C a b => ....
Then in f's Givens we have g:(C a b) and the superclass sc(g,0):a~b.
But that superclass selector can't (yet) appear in a coercion
(see evTermCoercion), so the easy thing is to bind it to an Id.

See Note [Coercion evidence terms] in TcEvidence.
-}

-- See Note [xCtEvidence]
xCtEvidence :: CtEvidence            -- Original evidence
            -> XEvTerm               -- Instructions about how to manipulate evidence
            -> TcS ()

xCtEvidence (CtWanted { ctev_evar = evar, ctev_loc = loc })
            (XEvTerm { ev_preds = ptys, ev_comp = comp_fn })
  = do { new_mb_evars <- mapM (newWantedEvVar loc) ptys
       ; setEvBind evar (comp_fn (map getEvTerm new_mb_evars)) loc
       ; emitWorkNC (freshGoals new_mb_evars) }
         -- Note the "NC": these are fresh goals, not necessarily canonical

xCtEvidence (CtGiven { ctev_evtm = tm, ctev_loc = loc })
            (XEvTerm { ev_preds = ptys, ev_decomp = decomp_fn })
  = ASSERT( equalLength ptys (decomp_fn tm) )
    do { given_evs <- newGivenEvVars loc (ptys `zip` decomp_fn tm)
       ; emitWorkNC given_evs }

xCtEvidence (CtDerived { ctev_loc = loc })
            (XEvTerm { ev_preds = ptys })
  = mapM_ (emitNewDerived loc) ptys

-----------------------------
data StopOrContinue a
  = ContinueWith a    -- The constraint was not solved, although it may have
                      --   been rewritten

  | Stop CtEvidence   -- The (rewritten) constraint was solved
         SDoc         -- Tells how it was solved
                      -- Any new sub-goals have been put on the work list

instance Functor StopOrContinue where
  fmap f (ContinueWith x) = ContinueWith (f x)
  fmap _ (Stop ev s)      = Stop ev s

instance Outputable a => Outputable (StopOrContinue a) where
  ppr (Stop ev s)      = ptext (sLit "Stop") <> parens s <+> ppr ev
  ppr (ContinueWith w) = ptext (sLit "ContinueWith") <+> ppr w

continueWith :: a -> TcS (StopOrContinue a)
continueWith = return . ContinueWith

stopWith :: CtEvidence -> String -> TcS (StopOrContinue a)
stopWith ev s = return (Stop ev (text s))

andWhenContinue :: TcS (StopOrContinue a)
                -> (a -> TcS (StopOrContinue b))
                -> TcS (StopOrContinue b)
andWhenContinue tcs1 tcs2
  = do { r <- tcs1
       ; case r of
           Stop ev s       -> return (Stop ev s)
           ContinueWith ct -> tcs2 ct }
infixr 0 `andWhenContinue`    -- allow chaining with ($)

rewriteEvidence :: CtEvidence   -- old evidence
                -> TcPredType   -- new predicate
                -> TcCoercion   -- Of type :: new predicate ~ <type of old evidence>
                -> TcS (StopOrContinue CtEvidence)
-- Returns Just new_ev iff either (i)  'co' is reflexivity
--                             or (ii) 'co' is not reflexivity, and 'new_pred' not cached
-- In either case, there is nothing new to do with new_ev
{-
     rewriteEvidence old_ev new_pred co
Main purpose: create new evidence for new_pred;
              unless new_pred is cached already
* Returns a new_ev : new_pred, with same wanted/given/derived flag as old_ev
* If old_ev was wanted, create a binding for old_ev, in terms of new_ev
* If old_ev was given, AND not cached, create a binding for new_ev, in terms of old_ev
* Returns Nothing if new_ev is already cached

        Old evidence    New predicate is               Return new evidence
        flavour                                        of same flavor
        -------------------------------------------------------------------
        Wanted          Already solved or in inert     Nothing
        or Derived      Not                            Just new_evidence

        Given           Already in inert               Nothing
                        Not                            Just new_evidence

Note [Rewriting with Refl]
~~~~~~~~~~~~~~~~~~~~~~~~~~
If the coercion is just reflexivity then you may re-use the same
variable.  But be careful!  Although the coercion is Refl, new_pred
may reflect the result of unification alpha := ty, so new_pred might
not _look_ the same as old_pred, and it's vital to proceed from now on
using new_pred.

The flattener preserves type synonyms, so they should appear in new_pred
as well as in old_pred; that is important for good error messages.
 -}


rewriteEvidence old_ev@(CtDerived { ctev_loc = loc }) new_pred _co
  = -- If derived, don't even look at the coercion.
    -- This is very important, DO NOT re-order the equations for
    -- rewriteEvidence to put the isTcReflCo test first!
    -- Why?  Because for *Derived* constraints, c, the coercion, which
    -- was produced by flattening, may contain suspended calls to
    -- (ctEvTerm c), which fails for Derived constraints.
    -- (Getting this wrong caused Trac #7384.)
    do { mb_ev <- newDerived loc new_pred
       ; case mb_ev of
           Just new_ev -> continueWith new_ev
           Nothing     -> stopWith old_ev "Cached derived" }

rewriteEvidence old_ev new_pred co
  | isTcReflCo co -- See Note [Rewriting with Refl]
  = return (ContinueWith (old_ev { ctev_pred = new_pred }))

rewriteEvidence ev@(CtGiven { ctev_evtm = old_tm , ctev_loc = loc }) new_pred co
  = do { new_ev <- newGivenEvVar loc (new_pred, new_tm)  -- See Note [Bind new Givens immediately]
       ; return (ContinueWith new_ev) }
  where
    -- mkEvCast optimises ReflCo
    new_tm = mkEvCast old_tm (tcDowngradeRole Representational
                                              (ctEvRole ev)
                                              (mkTcSymCo co))  

rewriteEvidence ev@(CtWanted { ctev_evar = evar, ctev_loc = loc }) new_pred co
  = do { mb_new_ev <- newWantedEvVar loc new_pred
       ; MASSERT( tcCoercionRole co == ctEvRole ev )
       ; setEvBind evar
                   (mkEvCast (getEvTerm mb_new_ev)
                             (tcDowngradeRole Representational (ctEvRole ev) co))
                   loc
       ; case mb_new_ev of
            Fresh  new_ev -> continueWith new_ev
            Cached _      -> stopWith ev "Cached wanted" }


rewriteEqEvidence :: CtEvidence         -- Old evidence :: olhs ~ orhs (not swapped)
                                        --              or orhs ~ olhs (swapped)
                  -> SwapFlag
                  -> TcType -> TcType   -- New predicate  nlhs ~ nrhs
                                        -- Should be zonked, because we use typeKind on nlhs/nrhs
                  -> TcCoercion         -- lhs_co, of type :: nlhs ~ olhs
                  -> TcCoercion         -- rhs_co, of type :: nrhs ~ orhs
                  -> TcS (StopOrContinue CtEvidence)  -- Of type nlhs ~ nrhs
-- For (rewriteEqEvidence (Given g olhs orhs) False nlhs nrhs lhs_co rhs_co)
-- we generate
-- If not swapped
--      g1 : nlhs ~ nrhs = lhs_co ; g ; sym rhs_co
-- If 'swapped'
--      g1 : nlhs ~ nrhs = lhs_co ; Sym g ; sym rhs_co
--
-- For (Wanted w) we do the dual thing.
-- New  w1 : nlhs ~ nrhs
-- If not swapped
--      w : olhs ~ orhs = sym lhs_co ; w1 ; rhs_co
-- If swapped
--      w : orhs ~ olhs = sym rhs_co ; sym w1 ; lhs_co
--
-- It's all a form of rewwriteEvidence, specialised for equalities
rewriteEqEvidence old_ev swapped nlhs nrhs lhs_co rhs_co
  | CtDerived {} <- old_ev
  = do { mb <- newDerived loc' new_pred
       ; case mb of
           Just new_ev -> continueWith new_ev
           Nothing     -> stopWith old_ev "Cached derived" }

  | NotSwapped <- swapped
  , isTcReflCo lhs_co      -- See Note [Rewriting with Refl]
  , isTcReflCo rhs_co
  = return (ContinueWith (old_ev { ctev_pred = new_pred }))

  | CtGiven { ctev_evtm = old_tm } <- old_ev
  = do { let new_tm = EvCoercion (lhs_co
                                  `mkTcTransCo` maybeSym swapped (evTermCoercion old_tm)
                                  `mkTcTransCo` mkTcSymCo rhs_co)
       ; new_ev <- newGivenEvVar loc' (new_pred, new_tm)
                   -- See Note [Bind new Givens immediately]
       ; return (ContinueWith new_ev) }

  | CtWanted { ctev_evar = evar } <- old_ev
  = do { new_evar <- newWantedEvVarNC loc' new_pred
       ; let co = maybeSym swapped $
                  mkTcSymCo lhs_co
                  `mkTcTransCo` ctEvCoercion new_evar
                  `mkTcTransCo` rhs_co
       ; setEvBind evar (EvCoercion co) loc
       ; traceTcS "rewriteEqEvidence" (vcat [ppr old_ev, ppr nlhs, ppr nrhs, ppr co])
       ; return (ContinueWith new_evar) }

  | otherwise
  = panic "rewriteEvidence"
  where
    new_pred = mkTcEqPredLikeEv old_ev nlhs nrhs

      -- equality is like a type class. Bumping the depth is necessary because
      -- of recursive newtypes, where "reducing" a newtype can actually make
      -- it bigger. See Note [Eager reflexivity check] in TcCanonical before
      -- considering changing this behavior.
    loc      = ctEvLoc old_ev
    loc'     = bumpCtLocDepth CountConstraints loc

{- Note [unifyWanted and unifyDerived]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When decomposing equalities we often create new wanted constraints for
(s ~ t).  But what if s=t?  Then it'd be faster to return Refl right away.
Similar remarks apply for Derived.

Rather than making an equality test (which traverses the structure of the
type, perhaps fruitlessly, unifyWanted traverses the common structure, and
bales out when it finds a difference by creating a new Wanted constraint.
But where it succeeds in finding common structure, it just builds a coercion
to reflect it.
-}

unifyWantedLikeEv :: CtEvidence -> CtLoc -> Role
                  -> TcType -> TcType -> TcS TcCoercion
-- Return coercion witnessing the equality of the two types,
-- emitting new work equalities where necessary to achieve that
-- Very good short-cut when the two types are equal, or nearly so
-- See Note [unifyWanted and unifyDerived]
-- The returned coercion's role matches the input parameter
-- The boxity of any produced Wanteds matches the CtEvidence parameter
unifyWantedLikeEv ev loc Phantom ty1 ty2
  = do { kind_co <- unifyWantedLikeEv ev loc Representational
                                      (typeKind ty1) (typeKind ty2)
       ; return (mkTcPhantomCo kind_co ty1 ty2) }
    
unifyWantedLikeEv ev loc role orig_ty1 orig_ty2
  = go orig_ty1 orig_ty2
  where
    go ty1 ty2 | Just ty1' <- tcView ty1 = go ty1' ty2
    go ty1 ty2 | Just ty2' <- tcView ty2 = go ty1 ty2'

    go (ForAllTy (Anon s1) t1) (ForAllTy (Anon s2) t2)
      = do { co_s <- unifyWantedLikeEv ev loc role s1 s2
           ; co_t <- unifyWantedLikeEv ev loc role t1 t2
           ; return (mkTcTyConAppCo role funTyCon [co_s,co_t]) }
    go (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      | tc1 == tc2, isDecomposableTyCon tc1, tys1 `equalLength` tys2
      , (not (isNewTyCon tc1) && not (isDataFamilyTyCon tc1)) || role == Nominal
         -- don't look under newtypes!
      = do { cos <- zipWith3M (unifyWantedLikeEv ev loc)
                              (tyConRolesX role tc1) tys1 tys2
           ; return (mkTcTyConAppCo role tc1 cos) }
    go (TyVarTy tv) ty2
      = do { mb_ty <- isFilledMetaTyVar_maybe tv
           ; case mb_ty of
                Just ty1' -> go ty1' ty2
                Nothing   -> bale_out }
    go ty1 (TyVarTy tv)
      = do { mb_ty <- isFilledMetaTyVar_maybe tv
           ; case mb_ty of
                Just ty2' -> go ty1 ty2'
                Nothing   -> bale_out }
        
    go ty1@(CoercionTy {}) (CoercionTy {})
      = return (mkTcReflCo role ty1) -- we just don't care about coercions!
        
    go _ _ = bale_out

    bale_out = do { ev <- newWantedEvVarNC loc (mkTcEqPredBR boxity role
                                                  orig_ty1 orig_ty2)
                  ; emitWorkNC [ev]
                  ; return (ctEvCoercion ev) }

    boxity = getEqPredBoxity (ctEvPred ev)

unifyDeriveds :: CtLoc -> [Role] -> [TcType] -> [TcType] -> TcS ()
-- See Note [unifyWanted and unifyDerived]
unifyDeriveds loc roles tys1 tys2 = zipWith3M_ (unify_derived loc) roles tys1 tys2

unifyDerived :: CtLoc -> Role -> Pair TcType -> TcS ()
-- See Note [unifyWanted and unifyDerived]
unifyDerived loc role (Pair ty1 ty2) = unify_derived loc role ty1 ty2

unify_derived :: CtLoc -> Role -> TcType -> TcType -> TcS ()
-- Create new Derived and put it in the work list
-- Should do nothing if the two types are equal
-- See Note [unifyWanted and unifyDerived]
unify_derived _   Phantom _        _        = return ()
unify_derived loc role    orig_ty1 orig_ty2
  = go orig_ty1 orig_ty2
  where
    go ty1 ty2 | Just ty1' <- tcView ty1 = go ty1' ty2
    go ty1 ty2 | Just ty2' <- tcView ty2 = go ty1 ty2'

    go (ForAllTy (Anon s1) t1) (ForAllTy (Anon s2) t2)
      = do { unify_derived loc role s1 s2
           ; unify_derived loc role t1 t2 }
    go (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      | tc1 == tc2, isDecomposableTyCon tc1, tys1 `equalLength` tys2
      , (not (isNewTyCon tc1) && not (isDataFamilyTyCon tc1)) || role == Nominal
      = unifyDeriveds loc (tyConRolesX role tc1) tys1 tys2
    go (TyVarTy tv) ty2
      = do { mb_ty <- isFilledMetaTyVar_maybe tv
           ; case mb_ty of
                Just ty1' -> go ty1' ty2
                Nothing   -> bale_out }
    go ty1 (TyVarTy tv)
      = do { mb_ty <- isFilledMetaTyVar_maybe tv
           ; case mb_ty of
                Just ty2' -> go ty1 ty2'
                Nothing   -> bale_out }
    go _ _ = bale_out

     -- no point in having *unboxed* deriveds.
    bale_out = emitNewDerived loc (mkTcEqPredBR Boxed role orig_ty1 orig_ty2)

maybeSym :: SwapFlag -> TcCoercion -> TcCoercion
maybeSym IsSwapped  co = mkTcSymCo co
maybeSym NotSwapped co = co

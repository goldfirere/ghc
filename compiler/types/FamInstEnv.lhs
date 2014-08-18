%
% (c) The University of Glasgow 2006
%

FamInstEnv: Type checked family instance declarations

\begin{code}
{-# LANGUAGE CPP, GADTs #-}

module FamInstEnv (
        FamInst(..), FamFlavor(..), famInstAxiom, famInstTyCon, famInstRHS,
        famInstsRepTyCons, famInstRepTyCon_maybe, dataFamInstRepTyCon,
        pprFamInst, pprFamInsts,
        mkImportedFamInst,

        FamInstEnvs, FamInstEnv, emptyFamInstEnv, emptyFamInstEnvs,
        extendFamInstEnv, deleteFromFamInstEnv, extendFamInstEnvList,
        identicalFamInst, famInstEnvElts, familyInstances, orphNamesOfFamInst,

        -- * CoAxioms
        mkCoAxBranch, mkBranchedCoAxiom, mkUnbranchedCoAxiom, mkSingleCoAxiom,
        computeAxiomIncomps,

        FamInstMatch(..),
        lookupFamInstEnv, lookupFamInstEnvConflicts,

        isDominatedBy,

        -- Normalisation
        instNewTyConTF_maybe, chooseBranch, topNormaliseType, topNormaliseType_maybe,
        normaliseType, normaliseTcApp,

        -- Flattening
        flattenTys
    ) where

#include "HsVersions.h"

import InstEnv
import Unify
import Type
import TcType ( orphNamesOfTypes )
import TyCoRep
import TyCon
import Coercion
import CoAxiom
import VarSet
import VarEnv
import Module( isInteractiveModule )
import Name
import PrelNames ( eqPrimTyConKey )
import UniqFM
import Outputable
import Maybes
import TrieMap
import Unique
import Util
import Var
import Pair
import SrcLoc
import NameSet
import FastString
\end{code}

%************************************************************************
%*                                                                      *
          Type checked family instance heads
%*                                                                      *
%************************************************************************

Note [FamInsts and CoAxioms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* CoAxioms and FamInsts are just like
  DFunIds  and ClsInsts

* A CoAxiom is a System-FC thing: it can relate any two types

* A FamInst is a Haskell source-language thing, corresponding
  to a type/data family instance declaration.
    - The FamInst contains a CoAxiom, which is the evidence
      for the instance

    - The LHS of the CoAxiom is always of form F ty1 .. tyn
      where F is a type family

\begin{code}
data FamInst  -- See Note [FamInsts and CoAxioms]
  = FamInst { fi_axiom  :: CoAxiom Unbranched  -- The new coercion axiom introduced
                                               -- by this family instance
            , fi_flavor :: FamFlavor

            -- Everything below here is a redundant,
            -- cached version of the two things above
            -- except that the TyVars are freshened
            , fi_fam   :: Name          -- Family name

                -- Used for "rough matching"; same idea as for class instances
                -- See Note [Rough-match field] in InstEnv
            , fi_tcs   :: [Maybe Name]  -- Top of type args
                -- INVARIANT: fi_tcs = roughMatchTcs fi_tys

                -- Used for "proper matching"; ditto
            , fi_tvs    :: [TyVar]      -- Template tyvars for full match
                                 -- Like ClsInsts, these variables are always
                                 -- fresh. See Note [Template tyvars are fresh]
                                 -- in InstEnv

            , fi_tys    :: [Type]       --   and its arg types
                -- INVARIANT: fi_tvs = coAxiomTyVars fi_axiom

            , fi_rhs    :: Type         --   the RHS, with its freshened vars
            }

data FamFlavor
  = SynFamilyInst         -- A synonym family
  | DataFamilyInst TyCon  -- A data family, with its representation TyCon
\end{code}


\begin{code}
-- Obtain the axiom of a family instance
famInstAxiom :: FamInst -> CoAxiom Unbranched
famInstAxiom = fi_axiom

-- Split the left-hand side of the FamInst
famInstSplitLHS :: FamInst -> (TyCon, [Type])
famInstSplitLHS (FamInst { fi_axiom = axiom, fi_tys = lhs })
  = (coAxiomTyCon axiom, lhs)

-- Get the RHS of the FamInst
famInstRHS :: FamInst -> Type
famInstRHS = fi_rhs

-- Get the family TyCon of the FamInst
famInstTyCon :: FamInst -> TyCon
famInstTyCon = coAxiomTyCon . famInstAxiom

-- Return the representation TyCons introduced by data family instances, if any
famInstsRepTyCons :: [FamInst] -> [TyCon]
famInstsRepTyCons fis = [tc | FamInst { fi_flavor = DataFamilyInst tc } <- fis]

-- Extracts the TyCon for this *data* (or newtype) instance
famInstRepTyCon_maybe :: FamInst -> Maybe TyCon
famInstRepTyCon_maybe fi
  = case fi_flavor fi of
       DataFamilyInst tycon -> Just tycon
       SynFamilyInst        -> Nothing

dataFamInstRepTyCon :: FamInst -> TyCon
dataFamInstRepTyCon fi
  = case fi_flavor fi of
       DataFamilyInst tycon -> tycon
       SynFamilyInst        -> pprPanic "dataFamInstRepTyCon" (ppr fi)
\end{code}

%************************************************************************
%*                                                                      *
        Pretty printing
%*                                                                      *
%************************************************************************

\begin{code}
instance NamedThing FamInst where
   getName = coAxiomName . fi_axiom

instance Outputable FamInst where
   ppr = pprFamInst

-- Prints the FamInst as a family instance declaration
-- NB: FamInstEnv.pprFamInst is used only for internal, debug printing
--     See pprTyThing.pprFamInst for printing for the user
pprFamInst :: FamInst -> SDoc
pprFamInst famInst
  = hang (pprFamInstHdr famInst)
       2 (vcat [ ifPprDebug (ptext (sLit "Coercion axiom:") <+> ppr ax)
               , ifPprDebug (ptext (sLit "RHS:") <+> ppr (famInstRHS famInst)) ])
  where
    ax = fi_axiom famInst

pprFamInstHdr :: FamInst -> SDoc
pprFamInstHdr fi@(FamInst {fi_flavor = flavor})
  = pprTyConSort <+> pp_instance <+> pp_head
  where
    -- For *associated* types, say "type T Int = blah"
    -- For *top level* type instances, say "type instance T Int = blah"
    pp_instance
      | isTyConAssoc fam_tc = empty
      | otherwise           = ptext (sLit "instance")

    (fam_tc, etad_lhs_tys) = famInstSplitLHS fi
    vanilla_pp_head = pprTypeApp fam_tc etad_lhs_tys

    pp_head | DataFamilyInst rep_tc <- flavor
            , isAlgTyCon rep_tc
            , let extra_tvs = dropList etad_lhs_tys (tyConTyVars rep_tc)
            , not (null extra_tvs)
            = getPprStyle $ \ sty ->
              if debugStyle sty
              then vanilla_pp_head   -- With -dppr-debug just show it as-is
              else pprTypeApp fam_tc (etad_lhs_tys ++ mkOnlyTyVarTys extra_tvs)
                     -- Without -dppr-debug, eta-expand
                     -- See Trac #8674
                     -- (This is probably over the top now that we use this
                     --  only for internal debug printing; PprTyThing.pprFamInst
                     --  is used for user-level printing.)
            | otherwise
            = vanilla_pp_head

    pprTyConSort = case flavor of
                     SynFamilyInst        -> ptext (sLit "type")
                     DataFamilyInst tycon
                       | isDataTyCon     tycon -> ptext (sLit "data")
                       | isNewTyCon      tycon -> ptext (sLit "newtype")
                       | isAbstractTyCon tycon -> ptext (sLit "data")
                       | otherwise             -> ptext (sLit "WEIRD") <+> ppr tycon

pprFamInsts :: [FamInst] -> SDoc
pprFamInsts finsts = vcat (map pprFamInst finsts)
\end{code}

Note [Lazy axiom match]
~~~~~~~~~~~~~~~~~~~~~~~
It is Vitally Important that mkImportedFamInst is *lazy* in its axiom
parameter. The axiom is loaded lazily, via a forkM, in TcIface. Sometime
later, mkImportedFamInst is called using that axiom. However, the axiom
may itself depend on entities which are not yet loaded as of the time
of the mkImportedFamInst. Thus, if mkImportedFamInst eagerly looks at the
axiom, a dependency loop spontaneously appears and GHC hangs. The solution
is simply for mkImportedFamInst never, ever to look inside of the axiom
until everything else is good and ready to do so. We can assume that this
readiness has been achieved when some other code pulls on the axiom in the
FamInst. Thus, we pattern match on the axiom lazily (in the where clause,
not in the parameter list) and we assert the consistency of names there
also.

\begin{code}
-- Make a family instance representation from the information found in an
-- interface file.  In particular, we get the rough match info from the iface
-- (instead of computing it here).
mkImportedFamInst :: Name               -- Name of the family
                  -> [Maybe Name]       -- Rough match info
                  -> CoAxiom Unbranched -- Axiom introduced
                  -> FamInst            -- Resulting family instance
mkImportedFamInst fam mb_tcs axiom
  = FamInst {
      fi_fam    = fam,
      fi_tcs    = mb_tcs,
      fi_tvs    = tvs,
      fi_tys    = tys,
      fi_rhs    = rhs,
      fi_axiom  = axiom,
      fi_flavor = flavor }
  where
     -- See Note [Lazy axiom match]
     ~(CoAxiom { co_ax_branches =
       ~(FirstBranch ~(CoAxBranch { cab_lhs = tys
                                  , cab_tvs = tvs
                                  , cab_rhs = rhs })) }) = axiom

         -- Derive the flavor for an imported FamInst rather disgustingly
         -- Maybe we should store it in the IfaceFamInst?
     flavor = case splitTyConApp_maybe rhs of
                Just (tc, _)
                  | Just ax' <- tyConFamilyCoercion_maybe tc
                  , ax' == axiom
                  -> DataFamilyInst tc
                _ -> SynFamilyInst
\end{code}

%************************************************************************
%*                                                                      *
                FamInstEnv
%*                                                                      *
%************************************************************************

Note [FamInstEnv]
~~~~~~~~~~~~~~~~~
A FamInstEnv maps a family name to the list of known instances for that family.

The same FamInstEnv includes both 'data family' and 'type family' instances.
Type families are reduced during type inference, but not data families;
the user explains when to use a data family instance by using contructors
and pattern matching.

Neverthless it is still useful to have data families in the FamInstEnv:

 - For finding overlaps and conflicts

 - For finding the representation type...see FamInstEnv.topNormaliseType
   and its call site in Simplify

 - In standalone deriving instance Eq (T [Int]) we need to find the
   representation type for T [Int]

Note [Varying number of patterns for data family axioms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For data families, the number of patterns may vary between instances.
For example
   data family T a b
   data instance T Int a = T1 a | T2
   data instance T Bool [a] = T3 a

Then we get a data type for each instance, and an axiom:
   data TInt a = T1 a | T2
   data TBoolList a = T3 a

   axiom ax7   :: T Int ~ TInt   -- Eta-reduced
   axiom ax8 a :: T Bool [a] ~ TBoolList a

These two axioms for T, one with one pattern, one with two.  The reason
for this eta-reduction is decribed in TcInstDcls
   Note [Eta reduction for data family axioms]

\begin{code}
type FamInstEnv = UniqFM FamilyInstEnv  -- Maps a family to its instances
     -- See Note [FamInstEnv]

type FamInstEnvs = (FamInstEnv, FamInstEnv)
     -- External package inst-env, Home-package inst-env

newtype FamilyInstEnv
  = FamIE [FamInst]     -- The instances for a particular family, in any order

instance Outputable FamilyInstEnv where
  ppr (FamIE fs) = ptext (sLit "FamIE") <+> vcat (map ppr fs)

-- INVARIANTS:
--  * The fs_tvs are distinct in each FamInst
--      of a range value of the map (so we can safely unify them)

emptyFamInstEnvs :: (FamInstEnv, FamInstEnv)
emptyFamInstEnvs = (emptyFamInstEnv, emptyFamInstEnv)

emptyFamInstEnv :: FamInstEnv
emptyFamInstEnv = emptyUFM

famInstEnvElts :: FamInstEnv -> [FamInst]
famInstEnvElts fi = [elt | FamIE elts <- eltsUFM fi, elt <- elts]

familyInstances :: (FamInstEnv, FamInstEnv) -> TyCon -> [FamInst]
familyInstances (pkg_fie, home_fie) fam
  = get home_fie ++ get pkg_fie
  where
    get env = case lookupUFM env fam of
                Just (FamIE insts) -> insts
                Nothing                      -> []

-- | Collects the names of the concrete types and type constructors that
-- make up the LHS of a type family instance, including the family
-- name itself.
--
-- For instance, given `type family Foo a b`:
-- `type instance Foo (F (G (H a))) b = ...` would yield [Foo,F,G,H]
--
-- Used in the implementation of ":info" in GHCi.
orphNamesOfFamInst :: FamInst -> NameSet
orphNamesOfFamInst fam_inst
  = orphNamesOfTypes (concat (brListMap cab_lhs (coAxiomBranches axiom)))
    `addOneToNameSet` getName (coAxiomTyCon axiom)
  where
    axiom = fi_axiom fam_inst

extendFamInstEnvList :: FamInstEnv -> [FamInst] -> FamInstEnv
extendFamInstEnvList inst_env fis = foldl extendFamInstEnv inst_env fis

extendFamInstEnv :: FamInstEnv -> FamInst -> FamInstEnv
extendFamInstEnv inst_env ins_item@(FamInst {fi_fam = cls_nm})
  = addToUFM_C add inst_env cls_nm (FamIE [ins_item])
  where
    add (FamIE items) _ = FamIE (ins_item:items)

deleteFromFamInstEnv :: FamInstEnv -> FamInst -> FamInstEnv
-- Used only for overriding in GHCi
deleteFromFamInstEnv inst_env fam_inst@(FamInst {fi_fam = fam_nm})
 = adjustUFM adjust inst_env fam_nm
 where
   adjust :: FamilyInstEnv -> FamilyInstEnv
   adjust (FamIE items)
     = FamIE (filterOut (identicalFamInst fam_inst) items)

identicalFamInst :: FamInst -> FamInst -> Bool
-- Same LHS, *and* both instances are on the interactive command line
-- Used for overriding in GHCi
identicalFamInst (FamInst { fi_axiom = ax1 }) (FamInst { fi_axiom = ax2 })
  =  isInteractiveModule (nameModule (coAxiomName ax1))
  && isInteractiveModule (nameModule (coAxiomName ax2))
  && coAxiomTyCon ax1 == coAxiomTyCon ax2
  && brListLength brs1 == brListLength brs2
  && and (brListZipWith identical_ax_branch brs1 brs2)
  where brs1 = coAxiomBranches ax1
        brs2 = coAxiomBranches ax2
        identical_ax_branch br1 br2
          = length tvs1 == length tvs2
            && length lhs1 == length lhs2
            && and (zipWith (eqTypeX rn_env) lhs1 lhs2)
          where
            tvs1 = coAxBranchTyCoVars br1
            tvs2 = coAxBranchTyCoVars br2
            lhs1 = coAxBranchLHS br1
            lhs2 = coAxBranchLHS br2
            rn_env = rnBndrs2 (mkRnEnv2 emptyInScopeSet) tvs1 tvs2
\end{code}

%************************************************************************
%*                                                                      *
                Compatibility
%*                                                                      *
%************************************************************************

Note [Apartness]
~~~~~~~~~~~~~~~~
In dealing with closed type families, we must be able to check that one type
will never reduce to another. This check is called /apartness/. The check
is always between a target (which may be an arbitrary type) and a pattern.
Here is how we do it:

apart(target, pattern) = not (unify(flatten(target), pattern))

where flatten (implemented in flattenTys, below) converts all type-family
applications into fresh variables. (See Note [Flattening].)

Note [Compatibility]
~~~~~~~~~~~~~~~~~~~~
Two patterns are /compatible/ if either of the following conditions hold:
1) The patterns are apart.
2) The patterns unify with a substitution S, and their right hand sides
equal under that substitution.

For open type families, only compatible instances are allowed. For closed
type families, the story is slightly more complicated. Consider the following:

type family F a where
  F Int = Bool
  F a   = Int

g :: Show a => a -> F a
g x = length (show x)

Should that type-check? No. We need to allow for the possibility that 'a'
might be Int and therefore 'F a' should be Bool. We can simplify 'F a' to Int
only when we can be sure that 'a' is not Int.

To achieve this, after finding a possible match within the equations, we have to
go back to all previous equations and check that, under the
substitution induced by the match, other branches are surely apart. (See
Note [Apartness].) This is similar to what happens with class
instance selection, when we need to guarantee that there is only a match and
no unifiers. The exact algorithm is different here because the the
potentially-overlapping group is closed.

As another example, consider this:

type family G x
type instance where
  G Int = Bool
  G a   = Double

type family H y
-- no instances

Now, we want to simplify (G (H Char)). We can't, because (H Char) might later
simplify to be Int. So, (G (H Char)) is stuck, for now.

While everything above is quite sound, it isn't as expressive as we'd like.
Consider this:

type family J a where
  J Int = Int
  J a   = a

Can we simplify (J b) to b? Sure we can. Yes, the first equation matches if
b is instantiated with Int, but the RHSs coincide there, so it's all OK.

So, the rule is this: when looking up a branch in a closed type family, we
find a branch that matches the target, but then we make sure that the target
is apart from every previous *incompatible* branch. We don't check the
branches that are compatible with the matching branch, because they are either
irrelevant (clause 1 of compatible) or benign (clause 2 of compatible).

\begin{code}

-- See Note [Compatibility]
compatibleBranches :: CoAxBranch -> CoAxBranch -> Bool
compatibleBranches (CoAxBranch { cab_lhs = lhs1, cab_rhs = rhs1 })
                   (CoAxBranch { cab_lhs = lhs2, cab_rhs = rhs2 })
  = case tcUnifyTysFG instanceBindFun lhs1 lhs2 of
      SurelyApart -> True
      Unifiable subst
        | Type.substTy subst rhs1 `eqType` Type.substTy subst rhs2
        -> True
      _ -> False

-- takes a CoAxiom with unknown branch incompatibilities and computes
-- the compatibilities
-- See Note [Storing compatibility] in CoAxiom
computeAxiomIncomps :: CoAxiom br -> CoAxiom br
computeAxiomIncomps ax@(CoAxiom { co_ax_branches = branches })
  = ax { co_ax_branches = go [] branches }
  where
    go :: [CoAxBranch] -> BranchList CoAxBranch br -> BranchList CoAxBranch br
    go prev_branches (FirstBranch br)
      = FirstBranch (br { cab_incomps = mk_incomps br prev_branches })
    go prev_branches (NextBranch br tail)
      = let br' = br { cab_incomps = mk_incomps br prev_branches } in
        NextBranch br' (go (br' : prev_branches) tail)

    mk_incomps :: CoAxBranch -> [CoAxBranch] -> [CoAxBranch]
    mk_incomps br = filter (not . compatibleBranches br)

\end{code}

%************************************************************************
%*                                                                      *
           Constructing axioms
    These functions are here because tidyType / tcUnifyTysFG
    are not available in CoAxiom
%*                                                                      *
%************************************************************************

Note [Tidy axioms when we build them]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We print out axioms and don't want to print stuff like
    F k k a b = ...
Instead we must tidy those kind variables.  See Trac #7524.

\begin{code}
-- all axiom roles are Nominal, as this is only used with type families
mkCoAxBranch :: [TyCoVar] -- original, possibly stale, tyvars
             -> [Type]    -- LHS patterns
             -> Type      -- RHS
             -> SrcSpan
             -> CoAxBranch
mkCoAxBranch tvs lhs rhs loc
  = CoAxBranch { cab_tvs     = tvs1
               , cab_lhs     = tidyTypes env lhs
               , cab_roles   = map (const Nominal) tvs1
               , cab_rhs     = tidyType  env rhs
               , cab_loc     = loc
               , cab_incomps = placeHolderIncomps }
  where
    (env, tvs1) = tidyTyCoVarBndrs emptyTidyEnv tvs
    -- See Note [Tidy axioms when we build them]

-- all of the following code is here to avoid mutual dependencies with
-- Coercion
mkBranchedCoAxiom :: Name -> TyCon -> [CoAxBranch] -> CoAxiom Branched
mkBranchedCoAxiom ax_name fam_tc branches
  = computeAxiomIncomps $
    CoAxiom { co_ax_unique   = nameUnique ax_name
            , co_ax_name     = ax_name
            , co_ax_tc       = fam_tc
            , co_ax_role     = Nominal
            , co_ax_implicit = False
            , co_ax_branches = toBranchList branches }

mkUnbranchedCoAxiom :: Name -> TyCon -> CoAxBranch -> CoAxiom Unbranched
mkUnbranchedCoAxiom ax_name fam_tc branch
  = CoAxiom { co_ax_unique   = nameUnique ax_name
            , co_ax_name     = ax_name
            , co_ax_tc       = fam_tc
            , co_ax_role     = Nominal
            , co_ax_implicit = False
            , co_ax_branches = FirstBranch (branch { cab_incomps = [] }) }

mkSingleCoAxiom :: Name -> [TyVar] -> TyCon -> [Type] -> Type -> CoAxiom Unbranched
mkSingleCoAxiom ax_name tvs fam_tc lhs_tys rhs_ty
  = CoAxiom { co_ax_unique   = nameUnique ax_name
            , co_ax_name     = ax_name
            , co_ax_tc       = fam_tc
            , co_ax_role     = Nominal
            , co_ax_implicit = False
            , co_ax_branches = FirstBranch (branch { cab_incomps = [] }) }
  where
    branch = mkCoAxBranch tvs lhs_tys rhs_ty (getSrcSpan ax_name)
\end{code}

%************************************************************************
%*                                                                      *
                Looking up a family instance
%*                                                                      *
%************************************************************************

@lookupFamInstEnv@ looks up in a @FamInstEnv@, using a one-way match.
Multiple matches are only possible in case of type families (not data
families), and then, it doesn't matter which match we choose (as the
instances are guaranteed confluent).

We return the matching family instances and the type instance at which it
matches.  For example, if we lookup 'T [Int]' and have a family instance

  data instance T [a] = ..

desugared to

  data :R42T a = ..
  coe :Co:R42T a :: T [a] ~ :R42T a

we return the matching instance '(FamInst{.., fi_tycon = :R42T}, Int)'.

\begin{code}

-- when matching a type family application, we get a FamInst,
-- and the list of types the axiom should be applied to
data FamInstMatch = FamInstMatch { fim_instance :: FamInst
                                 , fim_tys      :: [Type]
                                 }
  -- See Note [Over-saturated matches]

instance Outputable FamInstMatch where
  ppr (FamInstMatch { fim_instance = inst
                    , fim_tys      = tys })
    = ptext (sLit "match with") <+> parens (ppr inst) <+> ppr tys

lookupFamInstEnv
    :: FamInstEnvs
    -> TyCon -> [Type]          -- What we are looking for
    -> [FamInstMatch]           -- Successful matches
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnv
   = lookup_fam_inst_env match
   where
     match _ tpl_tvs tpl_tys tys = tcMatchTys tpl_tvs tpl_tys tys

lookupFamInstEnvConflicts
    :: FamInstEnvs
    -> FamInst          -- Putative new instance
    -> [FamInstMatch]   -- Conflicting matches (don't look at the fim_tys field)
-- E.g. when we are about to add
--    f : type instance F [a] = a->a
-- we do (lookupFamInstConflicts f [b])
-- to find conflicting matches
--
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnvConflicts envs fam_inst@(FamInst { fi_axiom = new_axiom })
  = lookup_fam_inst_env my_unify envs fam tys
  where
    (fam, tys) = famInstSplitLHS fam_inst
        -- In example above,   fam tys' = F [b]

    my_unify (FamInst { fi_axiom = old_axiom }) tpl_tvs tpl_tys _
       = ASSERT2( tyCoVarsOfTypes tys `disjointVarSet` tpl_tvs,
                  (ppr fam <+> ppr tys) $$
                  (ppr tpl_tvs <+> ppr tpl_tys) )
                -- Unification will break badly if the variables overlap
                -- They shouldn't because we allocate separate uniques for them
         if compatibleBranches (coAxiomSingleBranch old_axiom) (new_branch)
           then Nothing
           else Just noSubst
      -- Note [Family instance overlap conflicts]

    noSubst = panic "lookupFamInstEnvConflicts noSubst"
    new_branch = coAxiomSingleBranch new_axiom
\end{code}

Note [Family instance overlap conflicts]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- In the case of data family instances, any overlap is fundamentally a
  conflict (as these instances imply injective type mappings).

- In the case of type family instances, overlap is admitted as long as
  the right-hand sides of the overlapping rules coincide under the
  overlap substitution.  eg
       type instance F a Int = a
       type instance F Int b = b
  These two overlap on (F Int Int) but then both RHSs are Int,
  so all is well. We require that they are syntactically equal;
  anything else would be difficult to test for at this stage.

\begin{code}
------------------------------------------------------------
-- Might be a one-way match or a unifier
type MatchFun =  FamInst                -- The FamInst template
              -> TyVarSet -> [Type]     --   fi_tvs, fi_tys of that FamInst
              -> [Type]                         -- Target to match against
              -> Maybe TCvSubst

lookup_fam_inst_env'          -- The worker, local to this module
    :: MatchFun
    -> FamInstEnv
    -> TyCon -> [Type]        -- What we are looking for
    -> [FamInstMatch]
lookup_fam_inst_env' match_fun ie fam match_tys
  | isOpenFamilyTyCon fam
  , Just (FamIE insts) <- lookupUFM ie fam
  = find insts    -- The common case
  | otherwise = []
  where

    find [] = []
    find (item@(FamInst { fi_tcs = mb_tcs, fi_tvs = tpl_tvs,
                          fi_tys = tpl_tys }) : rest)
        -- Fast check for no match, uses the "rough match" fields
      | instanceCantMatch rough_tcs mb_tcs
      = find rest

        -- Proper check
      | Just subst <- match_fun item (mkVarSet tpl_tvs) tpl_tys match_tys1
      = (FamInstMatch { fim_instance = item
                      , fim_tys      = substTyVars subst tpl_tvs `chkAppend` match_tys2 })
        : find rest

        -- No match => try next
      | otherwise
      = find rest

      where
        (rough_tcs, match_tys1, match_tys2) = split_tys tpl_tys

      -- Precondition: the tycon is saturated (or over-saturated)

    -- Deal with over-saturation
    -- See Note [Over-saturated matches]
    split_tys tpl_tys
      | isSynFamilyTyCon fam
      = pre_rough_split_tys

      | otherwise
      = let (match_tys1, match_tys2) = splitAtList tpl_tys match_tys
            rough_tcs = roughMatchTcs match_tys1
        in (rough_tcs, match_tys1, match_tys2)

    (pre_match_tys1, pre_match_tys2) = splitAt (tyConArity fam) match_tys
    pre_rough_split_tys
      = (roughMatchTcs pre_match_tys1, pre_match_tys1, pre_match_tys2)

lookup_fam_inst_env           -- The worker, local to this module
    :: MatchFun
    -> FamInstEnvs
    -> TyCon -> [Type]          -- What we are looking for
    -> [FamInstMatch]           -- Successful matches

-- Precondition: the tycon is saturated (or over-saturated)

lookup_fam_inst_env match_fun (pkg_ie, home_ie) fam tys =
    lookup_fam_inst_env' match_fun home_ie fam tys ++
    lookup_fam_inst_env' match_fun pkg_ie  fam tys

\end{code}

Note [Over-saturated matches]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's ok to look up an over-saturated type constructor.  E.g.
     type family F a :: * -> *
     type instance F (a,b) = Either (a->b)

The type instance gives rise to a newtype TyCon (at a higher kind
which you can't do in Haskell!):
     newtype FPair a b = FP (Either (a->b))

Then looking up (F (Int,Bool) Char) will return a FamInstMatch
     (FPair, [Int,Bool,Char])

The "extra" type argument [Char] just stays on the end.

Because of eta-reduction of data family instances (see
Note [Eta reduction for data family axioms] in TcInstDecls), we must
handle data families and type families separately here. All instances
of a type family must have the same arity, so we can precompute the split
between the match_tys and the overflow tys. This is done in pre_rough_split_tys.
For data instances, though, we need to re-split for each instance, because
the breakdown might be different.

\begin{code}

-- checks if one LHS is dominated by a list of other branches
-- in other words, if an application would match the first LHS, it is guaranteed
-- to match at least one of the others. The RHSs are ignored.
-- This algorithm is conservative:
--   True -> the LHS is definitely covered by the others
--   False -> no information
-- It is currently (Oct 2012) used only for generating errors for
-- inaccessible branches. If these errors go unreported, no harm done.
-- This is defined here to avoid a dependency from CoAxiom to Unify
isDominatedBy :: CoAxBranch -> [CoAxBranch] -> Bool
isDominatedBy branch branches
  = or $ map match branches
    where
      lhs = coAxBranchLHS branch
      match (CoAxBranch { cab_tvs = tvs, cab_lhs = tys })
        = isJust $ tcMatchTys (mkVarSet tvs) tys lhs
\end{code}

%************************************************************************
%*                                                                      *
                Choosing an axiom application
%*                                                                      *
%************************************************************************

The lookupFamInstEnv function does a nice job for *open* type families,
but we also need to handle closed ones when normalising a type:

\begin{code}
reduceTyFamApp_maybe :: FamInstEnvs -> Role -> TyCon -> [Type] -> Maybe (Coercion, Type)
-- Attempt to do a *one-step* reduction of a type-family application
-- It first normalises the type arguments, wrt functions but *not* newtypes,
-- to be sure that nested calls like
--    F (G Int)
-- are correctly reduced
--
-- The TyCon can be oversaturated.
-- Works on both open and closed families
--
-- Always returns a *homogeneous* coercion -- type family reductions are always
-- homogeneous
reduceTyFamApp_maybe env role tc tys
  = reduce_ty_fam_app_maybe env lc role tc tys
  where
    lc = emptyLiftingContext (mkInScopeSet (tyCoVarsOfTypes tys))

-- See Note [Normalising types] to learn about the LiftingContext parameter
reduce_ty_fam_app_maybe :: FamInstEnvs -> LiftingContext -> Role
                        -> TyCon -> [Type] -> Maybe (Coercion, Type)
reduce_ty_fam_app_maybe envs lc role tc tys
  | isOpenFamilyTyCon tc
  , [FamInstMatch { fim_instance = fam_inst
                  , fim_tys =      inst_tys }] <- lookupFamInstEnv envs tc ntys
  = let ax     = famInstAxiom fam_inst
        co     = mkUnbranchedAxInstCo role ax inst_tys
        ty     = pSnd (coercionKind co)
    in Just (args_co `mkTransCo` co, ty)

  | Just ax <- isClosedSynFamilyTyCon_maybe tc
  , Just (ind, inst_tys) <- chooseBranch ax ntys
  = let co     = mkAxInstCo role ax ind inst_tys
        ty     = pSnd (coercionKind co)
    in Just (args_co `mkTransCo` co, ty)

  | Just ax           <- isBuiltInSynFamTyCon_maybe tc
  , Just (coax,ts,ty) <- sfMatchFam ax ntys
  = let co = mkAxiomRuleCo coax ts []
    in Just (args_co `mkTransCo` co, ty)

  | otherwise
  = Nothing

  where
    (args_co, ntys) = normalise_tc_args envs lc role tc tys

-- The axiom can be oversaturated. (Closed families only.)
chooseBranch :: CoAxiom Branched -> [Type] -> Maybe (BranchIndex, [Type])
chooseBranch axiom tys
  = do { let num_pats = coAxiomNumPats axiom
             (target_tys, extra_tys) = splitAt num_pats tys
             branches = coAxiomBranches axiom
       ; (ind, inst_tys) <- findBranch (fromBranchList branches) 0 target_tys
       ; return (ind, inst_tys `chkAppend` extra_tys) }

-- The axiom must *not* be oversaturated
findBranch :: [CoAxBranch]             -- branches to check
           -> BranchIndex              -- index of current branch
           -> [Type]                   -- target types
           -> Maybe (BranchIndex, [Type])
findBranch (CoAxBranch { cab_tvs = tpl_tvs, cab_lhs = tpl_lhs, cab_incomps = incomps }
              : rest) ind target_tys
  = case tcMatchTys (mkVarSet tpl_tvs) tpl_lhs target_tys of
      Just subst -- matching worked. now, check for apartness.
        |  all (isSurelyApart
                . tcUnifyTysFG instanceBindFun flattened_target
                . coAxBranchLHS) incomps
        -> -- matching worked & we're apart from all incompatible branches. success
           Just (ind, substTyCoVars subst tpl_tvs)

      -- failure. keep looking
      _ -> findBranch rest (ind+1) target_tys

  where isSurelyApart SurelyApart = True
        isSurelyApart _           = False

        flattened_target = flattenTys in_scope target_tys
        in_scope = mkInScopeSet (unionVarSets $
                                 map (tyCoVarsOfTypes . coAxBranchLHS) incomps)

-- fail if no branches left
findBranch [] _ _ = Nothing

\end{code}


%************************************************************************
%*                                                                      *
                Looking up a family instance
%*                                                                      *
%************************************************************************

Note [Normalising types]
~~~~~~~~~~~~~~~~~~~~~~~~
The topNormaliseType function removes all occurrences of type families
and newtypes from the top-level structure of a type. normaliseTcApp does
the type family lookup and is fairly straightforward. normaliseType is
a little more involved.

The complication comes from the fact that a type family might be used in the
kind of a variable bound in a forall. We wish to remove this type family
application, but that means coming up with a fresh variable (with the new
kind). Thus, we need a substitution to be built up as we recur through the
type. However, an ordinary TCvSubst just won't do: when we hit a type variable
whose kind has changed during normalisation, we need both the new type
variable *and* the coercion. We could conjure up a new VarEnv with just this
property, but a usable substitution environment already exists:
LiftingContexts from the liftCoSubst family of functions, defined in Coercion.
A LiftingContext maps a type variable to a coercion and a coercion variable to
a pair of coercions. Let's ignore coercion variables for now. Because the
coercion a type variable maps to contains the destination type (via
coercionKind), we don't need to store that destination type separately. Thus,
a LiftingContext has what we need: a map from type variables to (Coercion,
Type) pairs.

We also benefit because we can piggyback on the liftCoSubstVarBndr function to
deal with binders. However, I had to modify that function to work with this
application in two ways. Thus, we now how liftCoSubstVarBndrCallback that
takes two customisations implementing the following differences with lifting:

* liftCoSubstVarBndr has to process the kind of the binder. We don't wish
to lift the kind, but instead normalise it. So, we pass in a callback function
that processes the kind of the binder.

* liftCoSubstVarBndr is happy to deal with heterogeneous coercions. But, we
here require *homogeneous* coercions. Why? A normalisation is essentially a
substitutive operation -- we need to be able to substitute a resultant type in
the place where the original type appears. Thus, all coercions returned in
normaliseType must be *homogeneous*, so the substitution type-checks. When
liftCoSubstVarBndr discovers that the kind of the (type variable) binder
(we'll call the type variable alpha) has changed (let's call the one with the
new kind beta and the coercion between the kinds eta), it uses a TyHetero
PiCoBndr, necessary to build a coercion between two PiTys whose (type)
binders have different kinds. The last component of a TyHetero is a coercion
variable (call it zeta) that witnesses the (heterogeneous) equality between
the two type variables in question (i.e., zeta :: alpha ~# beta). In a lifting
operation, alpha will be mapped to this coercion variable. In normalisation,
this won't do, because zeta is a *heterogeneous* coercion. So, we homogenize
zeta by casting the kind of its right-hand type to match that of its left-hand
type. That is, we make the mapping
  [alpha |-> zeta `mkCoherenceRightCo` (sym eta)]
. Thus, alpha maps to a coercion with type (alpha ~# beta |> sym eta), which
is *homogeneous*. Hurrah.

After that brilliant explanation of all this, I'm sure you've forgotten the
dangling reference to coercion variables. What do we do with those? Nothing at
all. The point of normalising types is to remove type family applications, but
there's no sense in removing these from coercions. We would just get back a
new coercion witnessing the equality between the same types as the original
coercion. Because coercions are irrelevant anyway, there is no point in doing
this. So, whenever we encounter a coercion, we just say that it won't change.
That's what the (CoCoArg co co) is doing in go_arg within normaliseType.

There is still the possibility that the kind of a coercion variable mentions
a type family and will change in normaliseTyCoVarBndr. So, we must perform
the same sort of homogenisation that we did for type variables. Let's use
the same names as before:
  alpha is our original coercion variable, alpha :: s1 ~# t1
  beta is our new coercion variable, beta :: s2 ~# t2
  eta is the coercion between the kinds, eta :: (s1 ~# t1) ~# (s2 ~# t2)
  zeta does not exist -- there is no coercion among coercions.
We must form some coercion, not involving alpha, with type (s1 ~# t1). It
should look something like this:
  g1 ; beta ; g2 :: s1 ~# t1
From this guess, we can see:
  g1 :: s1 ~# s2
  g2 :: t2 ~# t1
It looks like we can extract those from eta. Let's rewrite eta's type:
  eta :: ((~#) _ _ s1 t1) ~# ((~#) _ _ s2 t2)
where those underscores are kinds that we don't care about. Now, it is
easy to see that (nth:2 eta) :: s1 ~# s2 and (nth:3 eta) :: t1 ~# t2.
So, we can derive:
  g1 = nth:2 eta
  g2 = nth:3 (sym eta)
And, so we use the following mapping:
  [alpha |-> (alpha, nth:2 eta ; beta ; nth:3 (sym eta))]
Hurrah again. This last bit is implemented in liftCoSubstVarBndrCallback
in Coercion.

\begin{code}

topNormaliseType :: FamInstEnvs -> Type -> Type
topNormaliseType env ty = case topNormaliseType_maybe env ty of
                            Just (_co, ty') -> ty'
                            Nothing         -> ty

topNormaliseType_maybe :: FamInstEnvs
                       -> Type
                       -> Maybe (Coercion, Type)

-- Get rid of *outermost* (or toplevel)
--      * type function redex
--      * newtypes
-- using appropriate coercions.  Specifically, if
--   topNormaliseType_maybe env ty = Maybe (co, ty')
-- then
--   (a) co :: ty ~ ty'
--   (b) ty' is not a newtype, and is not a type-family redex
--
-- However, ty' can be something like (Maybe (F ty)), where
-- (F ty) is a redex.

-- Its a bit like Type.repType, but handles type families too
-- The coercion returned is always an R coercion

topNormaliseType_maybe env ty
  = go initRecTc Nothing ty
  where
    go :: RecTcChecker -> Maybe Coercion -> Type -> Maybe (Coercion, Type)
    go rec_nts mb_co1 ty
       = case splitTyConApp_maybe ty of
           Just (tc, tys) -> go_tc tc tys
           Nothing        -> all_done mb_co1
       where
         all_done Nothing   = Nothing
         all_done (Just co) = Just (co, ty)

         go_tc tc tys
            | Just (ty', co2) <- instNewTyCon_maybe tc tys
            = case checkRecTc rec_nts tc of
                Just rec_nts' -> go rec_nts' (mb_co1 `trans` co2) ty'
                Nothing       -> Nothing  -- No progress at all!
                                          -- cf topNormaliseNewType_maybe

            | Just (co2, rhs) <- reduceTyFamApp_maybe env Representational tc tys
            = go rec_nts (mb_co1 `trans` co2) rhs

            | otherwise
            = all_done mb_co1

    Nothing    `trans` co2 = Just co2
    (Just co1) `trans` co2 = Just (co1 `mkTransCo` co2)


---------------
normaliseTcApp :: FamInstEnvs -> Role -> TyCon -> [Type] -> (Coercion, Type)
normaliseTcApp env role tc tys
  = normalise_tc_app env lc role tc tys
  where
    in_scope = mkInScopeSet (tyCoVarsOfTypes tys)
    lc       = emptyLiftingContext in_scope

-- See Note [Normalising types] about the LiftingContext
normalise_tc_app :: FamInstEnvs -> LiftingContext -> Role
                 -> TyCon -> [Type] -> (Coercion, Type)
normalise_tc_app env lc role tc tys
  | Just (first_co, ty') <- reduce_ty_fam_app_maybe env lc role tc tys
  = let    -- A reduction is possible
        (rest_co,nty) = normalise_type env lc role ty'
    in
    (first_co `mkTransCo` rest_co, nty)

  | otherwise   -- No unique matching family instance exists;
                -- we do not do anything
  = let (co, ntys) = normalise_tc_args env lc role tc tys in
    (co, mkTyConApp tc ntys)
    

---------------
normalise_tc_args :: FamInstEnvs            -- environment with family instances
                  -> LiftingContext         -- See Note [Normalising types]
                  -> Role                   -- desired role of output coercion
                  -> TyCon -> [Type]        -- tc tys
                  -> (Coercion, [Type])      -- (co, new_tys), where
                                          -- co :: tc tys ~ tc new_tys
normalise_tc_args env lc role tc tys
  = (mkTyConAppCo role tc cois, ntys)
  where
    (cois, ntys) = zipWithAndUnzip (normalise_ty_arg env lc)
                                   (tyConRolesX role tc) tys

---------------
normaliseType :: FamInstEnvs -> Role -> Type -> (Coercion, Type)
normaliseType env role ty
  = normalise_type env lc role ty
  where
    in_scope = mkInScopeSet (tyCoVarsOfType ty)
    lc = emptyLiftingContext in_scope

normalise_type :: FamInstEnvs            -- environment with family instances
               -> LiftingContext         -- necessary because of kind coercions
               -> Role                   -- desired role of coercion
               -> Type                   -- old type
               -> (Coercion, Type)       -- (coercion,new type), where
                                        -- co :: old-type ~ new_type
-- Normalise the input type, by eliminating *all* type-function redexes
-- Returns with Refl if nothing happens
-- Does nothing to newtypes
-- The returned coercion *must* be *homogeneous*
-- See Note [Normalising types]

normalise_type env lc
  = go
  where
    go r ty | Just ty' <- coreView ty = go r ty'
    go r (TyConApp tc tys) = normalise_tc_app env lc r tc tys
    go r ty@(LitTy {})     = (mkReflCo r ty, ty)
    go r (AppTy ty1 ty2)
      = let (co,  nty1) = go r ty1
            (arg, nty2) = normalise_ty_arg env lc Nominal ty2
        in (mkAppCo co arg, mkAppTy nty1 nty2)
    go r (PiTy bndr ty)
      = let (lc', cobndr) = normalise_binder env lc r bndr
            (co, nty)     = normalise_type env lc' r ty
            (_, bndr')    = coBndrBinders cobndr
        in (mkPiCo cobndr co, mkPiTy bndr' nty)
    go r (TyVarTy tv)    = normalise_tyvar lc r tv
    go r (CastTy ty co)  =
      let (nco, nty) = go r ty
          co' = substRightCo lc co
      in (castCoercionKind nco co co', mkCastTy nty co')
    go _ (CoercionTy co) = pprPanic "normalise_type" (ppr co)

normalise_ty_arg :: FamInstEnvs -> LiftingContext -> Role
                 -> Type -> (CoercionArg, Type)
normalise_ty_arg _ lc r (CoercionTy co)
  = let right_co = substRightCo lc co in
    (CoCoArg r co right_co, CoercionTy right_co)
normalise_ty_arg env lc r ty
  = let (co, ty') = normalise_type env lc r ty in
    (TyCoArg co, ty')

normalise_tyvar :: LiftingContext -> Role -> TyVar -> (Coercion, Type)
normalise_tyvar lc r tv
  = ASSERT( isTyVar tv )
    case liftCoSubstTyCoVar lc r tv of
      Just (TyCoArg co) -> (co, pSnd $ coercionKind co)
      Nothing           -> (mkReflCo r ty, ty)
        where ty = mkOnlyTyVarTy tv
      bad_news          -> pprPanic "normaliseTyVar" (ppr bad_news)

normalise_tycovar_bndr :: FamInstEnvs -> LiftingContext -> Role -> TyCoVar
                       -> (LiftingContext, PiCoBndr)
normalise_tycovar_bndr env lc1 r1
  = liftCoSubstVarBndrCallback (\lc r ty -> fst $ normalise_type env lc r ty) True
    r1 lc1
  -- the True there means that we want homogeneous coercions
  -- See Note [Homogenizing TyHetero substs] in Coercion

-- | Unwrap a newtype of a newtype intances. This is analogous to
--   Coercion.instNewTyCon_maybe; differences are:
--     * it also lookups up newtypes families, and
--     * it does not require the newtype to be saturated.
--       (a requirement using it for Coercible)
instNewTyConTF_maybe :: FamInstEnvs -> TyCon -> [Type] -> Maybe (Type, Coercion)
instNewTyConTF_maybe env tc tys = result
  where
  (co1, tc2, tys2)
    | Just (co, rhs1) <- reduceTyFamApp_maybe env Representational tc tys
    , Just (tc2, tys2) <- splitTyConApp_maybe rhs1
    = (co, tc2, tys2)
    | otherwise
    = (mkReflCo Representational (mkTyConApp tc tys), tc, tys)

  result
     | Just (_, _, co_tc) <- unwrapNewTyCon_maybe tc2 -- Check for newtype
     , newTyConEtadArity tc2 <= length tys2           -- Check for enough arguments
     = Just (newTyConInstRhs tc2 tys2
            , co1 `mkTransCo` mkUnbranchedAxInstCo Representational co_tc tys2)
     | otherwise
     = Nothing
\end{code}

%************************************************************************
%*                                                                      *
              Flattening
%*                                                                      *
%************************************************************************

Note [Flattening]
~~~~~~~~~~~~~~~~~

As described in
http://research.microsoft.com/en-us/um/people/simonpj/papers/ext-f/axioms-extended.pdf
we sometimes need to flatten core types before unifying them. Flattening
means replacing all top-level uses of type functions with fresh variables,
taking care to preserve sharing. That is, the type (Either (F a b) (F a b)) should
flatten to (Either c c), never (Either c d).

Defined here because of module dependencies.

\begin{code}

data FlattenEnv = FlattenEnv { fe_type_map :: TypeMap TyVar
                             , fe_in_scope :: InScopeSet
                             , fe_subst    :: TCvSubst }

emptyFlattenEnv :: InScopeSet -> FlattenEnv
emptyFlattenEnv in_scope
  = FlattenEnv { fe_type_map = emptyTypeMap
               , fe_in_scope = in_scope
               , fe_subst    = mkTCvSubst in_scope emptyTvSubstEnv
                                                   emptyCvSubstEnv }

-- See Note [Flattening]
flattenTys :: InScopeSet -> [Type] -> [Type]
flattenTys in_scope tys = snd $ coreFlattenTys env tys
  where
    -- when we hit a type function, we replace it with a fresh variable
    -- but, we need to make sure that this fresh variable isn't mentioned
    -- *anywhere* in the types we're flattening, even if locally-bound in
    -- a forall. That way, we can ensure consistency both within and outside
    -- of that forall.
    all_in_scope = in_scope `extendInScopeSetSet` allTyVarsInTys tys
    env          = emptyFlattenEnv all_in_scope

coreFlattenTys :: FlattenEnv -> [Type] -> (FlattenEnv, [Type])
coreFlattenTys = go []
  where
    go rtys env []         = (env, reverse rtys)
    go rtys env (ty : tys)
      = let (env', ty') = coreFlattenTy env ty in
        go (ty' : rtys) env' tys

coreFlattenTy :: FlattenEnv -> Type -> (FlattenEnv, Type)
coreFlattenTy = go
  where
    go env (TyVarTy tv)    = (env, substTyVar (fe_subst env) tv)
    go env (AppTy ty1 ty2) = let (env1, ty1') = go env  ty1
                                 (env2, ty2') = go env1 ty2 in
                             (env2, AppTy ty1' ty2')
    go env (TyConApp tc tys)
      | isFamilyTyCon tc
      = let (env', tv) = coreFlattenTyFamApp env tc tys in
        (env', mkOnlyTyVarTy tv)

      | otherwise
      = let (env', tys') = coreFlattenTys env tys in
        (env', mkTyConApp tc tys')

    go env (PiTy bndr ty)
      = let (env1, bndr') = coreFlattenBinder env bndr
            (env2, ty')   = go env1 ty in
        (env2, mkPiTy bndr' ty')

    go env ty@(LitTy {}) = (env, ty)

    go env (CastTy ty co) = let (env1, ty') = go env ty
                                (env2, co') = coreFlattenCo env1 co in
                            (env2, CastTy ty' co')

    go env (CoercionTy co) = let (env', co') = coreFlattenCo env co in
                             (env', CoercionTy co')

-- when flattening, we don't care about the contents of coercions.
-- so, just return a fresh variable of the right (flattened) type
coreFlattenCo :: FlattenEnv -> Coercion -> (FlattenEnv, Coercion)
coreFlattenCo env co
  = (env2, mkCoVarCo covar)
  where
    (env1, kind') = coreFlattenTy env (coercionType co)
    fresh_name    = mkFlattenFreshCoName
    in_scope      = fe_in_scope env1
    covar         = uniqAway in_scope $ mkCoVar fresh_name kind'
    env2          = env1 { fe_in_scope = in_scope `extendInScopeSet` covar }

coreFlattenVarBndr :: FlattenEnv -> TyCoVar -> (FlattenEnv, TyCoVar)
coreFlattenVarBndr env tv
  | kind' `eqType` kind
  = ( env { fe_subst = extendTCvSubst old_subst tv (mkTyCoVarTy tv) }
             -- override any previous binding for tv
    , tv)
  | otherwise
  = let new_tv    = uniqAway (fe_in_scope env) (setTyVarKind tv kind')
        new_subst = extendTCvSubst old_subst tv (mkTyCoVarTy new_tv)
        new_is    = extendInScopeSet old_in_scope new_tv
    in
    (env' { fe_in_scope = new_is
          , fe_subst    = new_subst }, new_tv)
  where
    kind          = tyVarKind tv
    (env', kind') = coreFlattenTy env kind
    old_subst     = fe_subst env
    old_in_scope  = fe_in_scope env

coreFlattenTyFamApp :: FlattenEnv
                    -> TyCon         -- type family tycon
                    -> [Type]        -- args
                    -> (FlattenEnv, TyVar)
coreFlattenTyFamApp env fam_tc fam_args
  = case lookupTypeMap type_map fam_ty of
      Just tv -> (env, tv)
              -- we need fresh variables here, but this is called far from
              -- any good source of uniques. So, we generate one from thin
              -- air, using the arbitrary prime number 71 as a seed
      Nothing -> let tyvar_name = mkFlattenFreshTyName fam_tc
                     tv = uniqAway in_scope $ mkTyVar tyvar_name
                                                      (typeKind fam_ty)
                     env' = env { fe_type_map = extendTypeMap type_map fam_ty tv
                                , fe_in_scope = extendInScopeSet in_scope tv }
                 in (env', tv)
  where fam_ty   = mkTyConApp fam_tc fam_args
        FlattenEnv { fe_type_map = type_map
                   , fe_in_scope = in_scope } = env

-- | Get the set of all type variables mentioned anywhere in the list
-- of types. These variables are not necessarily free.
allTyVarsInTys :: [Type] -> VarSet
allTyVarsInTys []       = emptyVarSet
allTyVarsInTys (ty:tys) = allTyVarsInTy ty `unionVarSet` allTyVarsInTys tys

-- | Get the set of all type variables mentioned anywhere in a type.
allTyVarsInTy :: Type -> VarSet
allTyVarsInTy = go
  where
    go (TyVarTy tv)      = unitVarSet tv
    go (AppTy ty1 ty2)   = (go ty1) `unionVarSet` (go ty2)
    go (TyConApp _ tys)  = allTyVarsInTys tys
    go (PiTy bndr ty) =
      caseBinder bndr (\tv -> unitVarSet tv) (const emptyVarSet)
      `unionVarSet` go (binderType bndr) `unionVarSet` go ty
        -- don't remove the tv from the set!
    go (LitTy {})        = emptyVarSet
    go (CastTy ty co)    = go ty `unionVarSet` go_co co
    go (CoercionTy co)   = go_co co

    go_co (Refl _ ty)           = go ty
    go_co (TyConAppCo _ _ args) = go_args args
    go_co (AppCo co arg)        = go_co co `unionVarSet` go_arg arg
    go_co (PiCo cobndr co)      = mkVarSet (coBndrVars cobndr) `unionVarSet` go_co co
    go_co (CoVarCo cv)          = unitVarSet cv
    go_co (AxiomInstCo _ _ cos) = go_args cos
    go_co (PhantomCo h t1 t2)   = go_co h `unionVarSet` go t1 `unionVarSet` go t2
    go_co (UnsafeCo _ t1 t2)    = go t1 `unionVarSet` go t2
    go_co (SymCo co)            = go_co co
    go_co (TransCo c1 c2)       = go_co c1 `unionVarSet` go_co c2
    go_co (NthCo _ co)          = go_co co
    go_co (LRCo _ co)           = go_co co
    go_co (InstCo co arg)       = go_co co `unionVarSet` go_arg arg
    go_co (CoherenceCo c1 c2)   = go_co c1 `unionVarSet` go_co c2
    go_co (KindCo co)           = go_co co
    go_co (SubCo co)            = go_co co
    go_co (AxiomRuleCo _ ts cs) = allTyVarsInTys ts `unionVarSet` go_cos cs

    go_cos = foldr (unionVarSet . go_co) emptyVarSet

    go_arg (TyCoArg co)      = go_co co
    go_arg (CoCoArg _ c1 c2) = go_co c1 `unionVarSet` go_co c2

    go_args = foldr (unionVarSet . go_arg) emptyVarSet

mkFlattenFreshTyName :: Uniquable a => a -> Name
mkFlattenFreshTyName unq
  = mkSysTvName (deriveUnique (getUnique unq) 71) (fsLit "flt")

mkFlattenFreshCoName :: Name
mkFlattenFreshCoName
  = mkSystemVarName (deriveUnique eqPrimTyConKey 71) (fsLit "flc")

\end{code}

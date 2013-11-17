This module allows users to write code that the constraint solver calls
when it gets stuck.

It is highly experimental and very flaky. It exists only in the stage-2 compiler.

\begin{code}

{-# LANGUAGE PolyKinds #-}

module TcCustom (
   -- external to GHC
    CustomSolver(..), UserSolver, nameMatches

   -- internal to GHC
  , runUserSolver
  ) where

import TcEnv
import InstEnv
import MkCore
import CoreSyn
import HscMain
import SrcLoc
import Class
import TcRnTypes
import TcType
import TcMType
import TcEvidence
import TcRnMonad
import PrelNames
import Panic
import Inst
import Module
import Unique
import Outputable
import MkId
import Name
import Var
import FastTypes
import GHC.Exts ( Proxy#, unsafeCoerce# )
import Control.Monad
import qualified Language.Haskell.TH.Syntax as TH

-- | Write an instance of this class to offer a new custom solver.
class CustomSolver (constraint :: k) where
  -- | Write your algorithm in this method.
  solveConstraints :: Proxy# constraint -> UserSolver

-- | This is the type of user solvers. TODO: Describe in detail.
type UserSolver =  WantedConstraints
                -> (WantedConstraints, [(TcTyVar, TcType)], [(EvVar, EvTerm)])

-- | Checks to see if a @Name@ matches a Template Haskell 'Name'. The Template Haskell
-- 'Name' should be created with the @'name@ or @''Type@ syntax. The first parameter
-- *must* be a top-level name (that is, a name with a module).
nameMatches :: Name -> TH.Name -> Bool
nameMatches ghc_name (TH.Name (TH.OccName th_name_str) flavour)
  = case flavour of
      TH.NameS                  -> occs_match
      TH.NameQ (TH.ModName mod) -> occs_match
                                && mod == ghc_module_str
      TH.NameU unique           -> (getKeyFastInt (getUnique ghc_name)) ==# unique
      TH.NameL unique           -> (getKeyFastInt (getUnique ghc_name)) ==# unique
      TH.NameG ns (TH.PkgName pkg) (TH.ModName mod)
                                -> occs_match
                                && mod == ghc_module_str
                                && pkg == packageIdString (modulePackageId ghc_module)
                                && case ns of
                                     TH.VarName   -> isVarName ghc_name
                                     TH.DataName  -> isDataConName ghc_name
                                     TH.TcClsName -> isTyConName ghc_name
  where
    ghc_occ_name   = nameOccName ghc_name
    ghc_module     = nameModule ghc_name
    ghc_module_str = moduleNameString $ moduleName ghc_module
    occs_match     = occNameString ghc_occ_name == th_name_str

runUserSolver :: EvBindsVar -> WantedConstraints -> TcM (Bool, WantedConstraints)
runUserSolver ev_binds_var wc
  = do { inst_envs <- tcGetInstEnvs
       ; custom_solver_class <- tcLookupClass customSolverName
       ; let cls_insts = filter (isExternalName . getName . instanceDFunId)
                                (classInstances inst_envs custom_solver_class)
       ; run_user_solver cls_insts }
  where
    run_user_solver :: [ClsInst] -> TcM (Bool, WantedConstraints)
    run_user_solver [] = return (False, wc)
    run_user_solver (cls_inst : cls_insts)
      = do { solver <- slurp_in_solver cls_inst
           ; let (wc_residual, ty_binds, ev_binds) = solver wc
           ; -- TODO (RAE): add lots of checking here!!
           ; made_progress1 <- write_ty_binds ty_binds
           ; made_progress2 <- write_ev_binds ev_binds_var ev_binds
           ; if made_progress1 || made_progress2
             then return (True, wc_residual)
             else run_user_solver cls_insts }

slurp_in_solver :: ClsInst -> TcM UserSolver
slurp_in_solver (ClsInst { is_tvs = [], is_tys = tys, is_dfun = dfun
                         , is_cls = cls })
  = do { let expr = mkCoreApps (varToCoreExpr solveConstraintsId)
                               [ kExpr, constraintExpr, dfunExpr
                               , proxyExpr ]
       ; hsc_env <- getTopEnv
       ; either_hval <- tryM $ liftIO $
                        hscCompileCoreExpr hsc_env noSrcSpan expr
       ; case either_hval of
           Left exception -> fail_with_exn "load custom solver" exception
           Right hval -> return (unsafeCoerce# hval :: UserSolver) }
  where
    [solveConstraintsId] = classMethods cls
    [kExpr, constraintExpr] = map Type tys
    dfunExpr = varToCoreExpr dfun
    proxyExpr = mkCoreApp (varToCoreExpr proxyHashId) constraintExpr

    -- see Note [Concealed TH exceptions] in TcSplice, where this code is copied from
    fail_with_exn phase exn = do
        exn_msg <- liftIO $ Panic.safeShowException exn
        let msg = vcat [text "Exception when trying to" <+> text phase <+> text "compile-time code:",
                        nest 2 (text exn_msg)]
        failWithTc msg
slurp_in_solver cls_inst
  = failWithTc $ hang (text "Cannot use parameterized instance for CustomSolver")
                    2 (ppr cls_inst)

                
write_ty_binds :: [(TcTyVar, TcType)] -> TcM Bool
write_ty_binds mappings
  = do { forM_ mappings (uncurry writeMetaTyVar)
       ; return (not (null mappings)) }

write_ev_binds :: EvBindsVar -> [(EvVar, EvTerm)] -> TcM Bool
write_ev_binds ev_binds_var mappings
  = do { forM_ mappings (uncurry (addTcEvBind ev_binds_var))
       ; return (not (null mappings)) }


\end{code}
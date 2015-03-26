module Vectorise.Monad.Local 
  ( readLEnv
  , setLEnv
  , updLEnv
  , localV
  , closedV
  , getBindName
  , inBind
  , lookupTyCoVarPA
  , defLocalTyCoVar
  , defLocalTyCoVarWithPA
  , localTyCoVars
  )
where
  
import Vectorise.Monad.Base
import Vectorise.Env

import CoreSyn
import Name
import VarEnv
import Var
import FastString

-- Local Environment ----------------------------------------------------------

-- |Project something from the local environment.
--
readLEnv :: (LocalEnv -> a) -> VM a
readLEnv f  = VM $ \_ genv lenv -> return (Yes genv lenv (f lenv))

-- |Set the local environment.
--
setLEnv :: LocalEnv -> VM ()
setLEnv lenv  = VM $ \_ genv _ -> return (Yes genv lenv ())

-- |Update the environment using the provided function.
--
updLEnv :: (LocalEnv -> LocalEnv) -> VM ()
updLEnv f  = VM $ \_ genv lenv -> return (Yes genv (f lenv) ())

-- |Perform a computation in its own local environment.
-- This does not alter the environment of the current state.
--
localV :: VM a -> VM a
localV p 
  = do  
    { env <- readLEnv id
    ; x   <- p
    ; setLEnv env
    ; return x
    }

-- |Perform a computation in an empty local environment.
--
closedV :: VM a -> VM a
closedV p 
  = do
    { env <- readLEnv id
    ; setLEnv (emptyLocalEnv { local_bind_name = local_bind_name env })
    ; x   <- p
    ; setLEnv env
    ; return x
    }

-- |Get the name of the local binding currently being vectorised.
--
getBindName :: VM FastString
getBindName = readLEnv local_bind_name

-- |Run a vectorisation computation in a local environment, 
-- with this id set as the current binding.
--
inBind :: Id -> VM a -> VM a
inBind id p
  = do updLEnv $ \env -> env { local_bind_name = occNameFS (getOccName id) }
       p

-- |Lookup a PA tyvars from the local environment.
lookupTyCoVarPA :: Var -> VM (Maybe CoreExpr)
lookupTyCoVarPA tv 
   = readLEnv $ \env -> lookupVarEnv (local_tycovar_pa env) tv

-- |Add a tyvar to the local environment.
defLocalTyCoVar :: TyCoVar -> VM ()
defLocalTyCoVar tv = updLEnv $ \env ->
  env { local_tycovars   = tv : local_tycovars env
      , local_tycovar_pa = local_tycovar_pa env `delVarEnv` tv
      }

-- |Add mapping between a tyvar and pa dictionary to the local environment.
defLocalTyCoVarWithPA :: TyCoVar -> CoreExpr -> VM ()
defLocalTyCoVarWithPA tv pa = updLEnv $ \env ->
  env { local_tycovars   = tv : local_tycovars env
      , local_tycovar_pa = extendVarEnv (local_tycovar_pa env) tv pa
      }

-- |Get the set of tyvars from the local environment.
localTyCoVars :: VM [TyCoVar]
localTyCoVars = readLEnv (reverse . local_tycovars)

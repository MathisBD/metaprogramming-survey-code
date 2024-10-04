-- This file defines a global database which contains a list of `Name`s.
-- It has to be in a seperate file because `initialize` commands are
-- only executed at import time.
import Lean
open Lean

namespace NameDb

/-- The database contains a list of `Name`s of global constants. -/
initialize dbExt : EnvExtension (List Name) ← registerEnvExtension $ return []

/-- `NameDb.extend name` adds `name` to the database. -/
def extend {m} [Monad m] [MonadEnv m] (name : Name) : m Unit :=
  modifyEnv fun env => EnvExtension.modifyState dbExt env (name :: ·)

/-- `NameDb.get` returns the contents of the database. -/
def get {m} [Monad m] [MonadEnv m] : m (List Name) := do
  let env ← getEnv
  return EnvExtension.getState dbExt env

end NameDb

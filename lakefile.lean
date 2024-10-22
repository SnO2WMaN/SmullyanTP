import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "master"

package "SmullyanSystem" where
  version := v!"0.1.0"

@[default_target]
lean_lib «SmullyanSystem» where
  -- add library configuration options here

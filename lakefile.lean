import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "master"

package "SmullyanTP" where
  version := v!"0.1.0"

@[default_target]
lean_lib «SmullyanTP» where
  -- add library configuration options here

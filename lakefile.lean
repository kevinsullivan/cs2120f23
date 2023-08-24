import Lake
open Lake DSL

package «cs2120f23» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Cs2120f23» {
  -- add any library configuration options here
}

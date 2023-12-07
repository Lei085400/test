import Lake
open Lake DSL

package «lean4-example» {
  -- add package configuration options here

}
require mathlib from
  git "https://github.com/leanprover-community/mathlib4" @ "60b5e23731ea672fd38f73364e1d3115213fcd04"

-- require mathlib from
--   git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «Lean4Example» {
  -- add library configuration options here
}

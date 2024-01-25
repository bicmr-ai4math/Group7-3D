import Lake
open Lake DSL

package «threedim» where
  -- add package configuration options here

@[default_target]
lean_lib «Threedim» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

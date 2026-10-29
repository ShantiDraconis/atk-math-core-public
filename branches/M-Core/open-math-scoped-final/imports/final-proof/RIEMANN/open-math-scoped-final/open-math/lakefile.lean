import Lake
open Lake DSL

package open_math_minimal where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

lean_lib MCore where

@[default_target]
lean_lib Riemann where

import Lake
open Lake DSL

package "jsp-000788-formalization" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

lean_lib Erdos948

@[default_target]
lean_lib «JSP_000788» where
  roots := #[`JSP_000788, `Erdos948]

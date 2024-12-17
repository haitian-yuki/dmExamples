import Lake
open Lake DSL

package «dmExamples» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"dm_ordering"

@[default_target]
lean_lib «DmExamples» where
  -- add any library configuration options here

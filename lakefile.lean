import Lake
open Lake DSL

package «dmExamples» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.17.0-rc1"

@[default_target]
lean_lib «DmExamples» where
  -- add any library configuration options here

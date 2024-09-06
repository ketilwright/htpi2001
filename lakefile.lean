import Lake
open Lake DSL

package «htpi2001» where
  -- add package configuration options here

lean_lib «Htpi2001» where
  -- add library configuration options here

-- @[default_target]
-- lean_exe «htpi2001» where
--   root := `Main
--   -- Enables the use of the Lean interpreter by the executable (e.g.,
--   -- `runFrontend`) at the expense of increased binary size on Linux.
--   -- Remove this line if you do not need such functionality.
--   supportInterpreter := true

@[default_target] lean_lib HTPILib
@[default_target] lean_lib Library

-- requirements for math2001 (is this really needed here or can the ./lake/packages)
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"v{Lean.versionString}"
require Duper from git "https://github.com/hrmacbeth/duper" @ "main"
--require autograder from git "https://github.com/robertylewis/lean4-autograder-main" @ "864b34ce06d8536aec0c38e57448c17d1f83572a"

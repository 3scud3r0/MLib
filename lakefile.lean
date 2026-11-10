import Lake
open Lake DSL

package «LeanML» where
  version := v!"0.1.0"
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e58cf8d261d79b3803ed199b7afe8253fe6672f8"

@[default_target]
lean_lib LeanML where
  leanOptions := #[⟨`autoImplicit, false⟩]

import Lake
open Lake DSL

package «anisoHilbert» where
  -- Representation skeleton for an anisotropic Hilbert curve project.
  -- Enable native compilation for FFI support
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib «AnisoHilbert» where
  roots := #[`AnisoHilbert]

-- Executable target for testing the FFI exports
lean_exe «hilbert_test» where
  root := `AnisoHilbert.CExport

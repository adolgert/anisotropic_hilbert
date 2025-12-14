import Lake
open Lake DSL

package «anisoHilbert» where
  -- Representation skeleton for an anisotropic Hilbert curve project.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib «AnisoHilbert» where
  roots := #[`AnisoHilbert]

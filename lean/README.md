# Lean 4 skeleton: anisotropic Hilbert curve representation

This project is a *definition-only* skeleton intended to reduce risk before formal proofs.
It defines:
- axis and exponent types
- an explicit bitvector representation `BV k := Fin k → Bool`
- active-axis selection with deterministic ordering
- `pos?` lookup into axis lists
- bit-plane pack/unpack and a Hamilton-style `T` transform (XOR + rotation)

It does **not** yet implement `encode/decode` or prove any theorems.

This skeleton mirrors the bit-level transform style in Hamilton's report
"Compact Hilbert Indices" (Technical Report CS-2006-07).

## Local setup (Lean + Lake)

### 1) Install elan (Lean toolchain manager)

On macOS/Linux (in a terminal):

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

Restart your shell (or run `source ~/.profile` or equivalent).

Check:

```bash
lean --version
lake --version
```

### 2) Build this project

Unzip the project, `cd` into it, then:

```bash
lake build
```

### 3) Run the tiny demo checks

You can typecheck and run the `#eval` blocks in the demo file with:

```bash
lake env lean AnisoHilbert/Demo.lean
```

(You should see `#eval` output for `activeAxes`, `pos?`, and `packPlane`.)

### 4) Editor support

If you use VS Code, install the "Lean 4" extension, open this folder, and the
files should typecheck interactively.

## Notes

- This skeleton uses only Lean's `Std` library.
- If/when you want mathlib, the standard next step is to add it as a dependency in
  `lakefile.lean` and run `lake update`.

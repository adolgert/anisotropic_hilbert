import AnisoHilbert.Loops

namespace AnisoHilbert.CExport

/-!
# C FFI Export Module

This module provides C-callable functions for the anisotropic Hilbert curve
encode/decode operations. It bridges between Lean's dependent types and
C's flat array representations.

## Type Mappings
- C `uint32_t n` → Lean dimension count (runtime)
- C `uint32_t* exponents` → Lean `Exponents n`
- C `uint32_t* coords` → Lean `PointBV m`
- C `uint64_t` → packed Hilbert index (from `Digits`)
-/

/-- Convert array of UInt32 exponents to an Exponents function.
    The array index becomes the axis, value becomes the exponent. -/
def arrayToExponents (arr : Array UInt32) : Exponents arr.size :=
  fun j => arr[j].toNat

/-- Convert array of UInt32 coordinates to a PointBV.
    Each coordinate is converted to a BV of appropriate length. -/
def arrayToPoint {n : Nat} (m : Exponents n) (coords : Array UInt32) (hn : coords.size = n) :
    PointBV m :=
  fun j =>
    let idx : Fin coords.size := ⟨j.val, by rw [hn]; exact j.isLt⟩
    let coordVal := coords[idx].toNat
    BV.ofNat coordVal

/-- Convert PointBV to array of UInt32 coordinates. -/
def pointToArray {n : Nat} {m : Exponents n} (p : PointBV m) : Array UInt32 :=
  let axes := allAxes n
  axes.foldl (fun acc j => acc.push (BV.toNat (p j)).toUInt32) #[]

/-- Pack a list of variable-width digits into a single UInt64.
    Digits are packed MSB-first (first digit = highest significance).
    Each digit is shifted left to make room for subsequent digits. -/
def packDigitsToUInt64 (ds : Digits) : UInt64 :=
  ds.foldl (fun (acc : UInt64) (d : Digit) =>
    let ⟨k, bv⟩ := d
    let digitVal := (BV.toNat bv).toUInt64
    (acc <<< k.toUInt64) ||| digitVal
  ) 0

/-- Compute digit widths from exponents (number of active axes at each level).
    Returns list of widths from level mmax down to 1. -/
def digitWidths {n : Nat} (m : Exponents n) : List Nat :=
  let s0 := mMax m
  if s0 = 0 then []
  else
    let rec go (s : Nat) (acc : List Nat) : List Nat :=
      match s with
      | 0 => acc
      | Nat.succ s' => go s' ((activeAxes m (Nat.succ s')).length :: acc)
    (go s0 []).reverse

/-- Unpack UInt64 into variable-width digits given the digit widths. -/
def unpackUInt64ToDigits (h : UInt64) (widths : List Nat) : Digits :=
  -- First compute total bits and extract each digit from MSB to LSB
  let rec extractDigits (h : UInt64) (ws : List Nat) (acc : Digits) : Digits :=
    match ws with
    | [] => acc.reverse
    | w :: rest =>
      -- Compute bits remaining after this digit
      let restBits := rest.foldl (· + ·) 0
      let shifted := h >>> restBits.toUInt64
      let mask := (1 : UInt64) <<< w.toUInt64 - 1
      let digitVal := shifted &&& mask
      let digit : Digit := ⟨w, BV.ofNat digitVal.toNat⟩
      extractDigits h rest (digit :: acc)
  extractDigits h widths []

/-- Compute total bits needed for index from exponents. -/
def totalBits {n : Nat} (m : Exponents n) : Nat :=
  (digitWidths m).foldl (· + ·) 0

/-- Encode: coordinates → Hilbert index (as UInt64).
    Returns 0 on failure (e.g., mismatched array sizes). -/
@[export lean_hilbert_encode]
def hilbertEncode (nDims : UInt32) (coords : @& Array UInt32) (exponents : @& Array UInt32) : UInt64 :=
  if h1 : exponents.size = nDims.toNat then
    if h2 : coords.size = nDims.toNat then
      let m : Exponents nDims.toNat := fun j =>
        let idx : Fin exponents.size := ⟨j.val, by rw [h1]; exact j.isLt⟩
        exponents[idx].toNat
      let p : PointBV m := fun j =>
        let idx : Fin coords.size := ⟨j.val, by rw [h2]; exact j.isLt⟩
        BV.ofNat coords[idx].toNat
      match encodeDigits? (n := nDims.toNat) (m := m) p with
      | none => 0
      | some digits => packDigitsToUInt64 digits
    else 0
  else 0

/-- Decode: Hilbert index → coordinates (as Array UInt32).
    Returns empty array on failure. -/
@[export lean_hilbert_decode]
def hilbertDecode (nDims : UInt32) (exponents : @& Array UInt32) (index : UInt64) : Array UInt32 :=
  if h1 : exponents.size = nDims.toNat then
    let m : Exponents nDims.toNat := fun j =>
      let idx : Fin exponents.size := ⟨j.val, by rw [h1]; exact j.isLt⟩
      exponents[idx].toNat
    let widths := digitWidths m
    let digits := unpackUInt64ToDigits index widths
    match decodeDigits? (n := nDims.toNat) (m := m) digits with
    | none => #[]
    | some p => pointToArray p
  else #[]

/-- Simple test: encode then decode should return original point. -/
def testRoundtrip (nDims : UInt32) (coords : Array UInt32) (exponents : Array UInt32) : Bool :=
  let encoded := hilbertEncode nDims coords exponents
  let decoded := hilbertDecode nDims exponents encoded
  coords == decoded

end AnisoHilbert.CExport

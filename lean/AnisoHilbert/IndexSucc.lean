import AnisoHilbert.Loops

namespace AnisoHilbert

/-!
Variable-radix successor for the `Digits` representation of the Hilbert index.

`Digits` is a most-significant-first list of variable-width binary digits
(`Digit = Σ k, BV k`). For lattice continuity we will eventually analyze the
increment `h ↦ h+1` by locating the smallest level where the digit changes and
all lower digits overflow. This file implements the carry-propagating successor
and proves basic “shape preservation” facts (length and per-digit widths).

This file is intentionally index-only: it does not mention `decode` or geometry.
-/

namespace Digits

/-- Base (radix) for a digit of width `k` is `2^k`. -/
def base (k : Nat) : Nat := Nat.shiftLeft 1 k

/-- Maximum value of a `k`-bit digit, i.e. `2^k - 1`. -/
def maxVal (k : Nat) : Nat := (base k) - 1

/-- Interpret a digit word as a natural number. -/
def val (d : Digit) : Nat :=
  BV.toNat d.2

/-- Successor of a single digit, with carry-out.

If the digit does not overflow, returns `(d+1, false)`.
If it overflows, returns `(0, true)`.

The bit-width `k` is preserved.
-/
def succDigit (d : Digit) : Digit × Bool :=
  match d with
  | ⟨k, w⟩ =>
      let n := BV.toNat w
      let b := base k
      if h : n.succ < b then
        (⟨k, BV.ofNat (k := k) n.succ⟩, false)
      else
        (⟨k, BV.zero⟩, true)

/-- Auxiliary: successor on *least-significant-first* lists, with carry-out.

Return value is `(ds', carry)` where `ds'` has the same shape as `ds`.

* `carry = false` means success (no overflow beyond the most significant digit)
* `carry = true` means the whole word overflowed (e.g. `111..11 + 1`).
-/
def succAux : List Digit → List Digit × Bool
  | [] => ([], true)
  | d :: ds =>
      let (d', c) := succDigit d
      if c then
        let (ds', c') := succAux ds
        (d' :: ds', c')
      else
        (d' :: ds, false)

/-- Successor on the “most-significant-first” `Digits` representation.

We treat the *last* digit in the list as least significant.
Returns `none` exactly on total overflow.
-/
def succ (ds : Digits) : Option Digits :=
  let (rev', carry) := succAux ds.reverse
  if carry then none else some rev'.reverse

/-! ### Basic shape lemmas -/

theorem succDigit_preserves_width (d : Digit) : (succDigit d).1.1 = d.1 := by
  cases d with
  | mk k w =>
      simp only [succDigit]
      split <;> rfl

theorem succAux_preserves_widths : ∀ ds : List Digit,
    (succAux ds).1.map (fun d => d.1) = ds.map (fun d => d.1) := by
  intro ds
  induction ds with
  | nil =>
      simp [succAux]
  | cons d ds ih =>
      simp only [succAux]
      split
      · simp only [List.map]
        rw [succDigit_preserves_width, ih]
      · simp only [List.map]
        rw [succDigit_preserves_width]

theorem succAux_preserves_length : ∀ ds : List Digit,
    (succAux ds).1.length = ds.length := by
  intro ds
  induction ds with
  | nil =>
      simp [succAux]
  | cons d ds ih =>
      simp only [succAux]
      split
      · simp only [List.length]
        rw [ih]
      · simp only [List.length]

theorem succ_preserves_widths (ds ds' : Digits) (h : succ ds = some ds') :
    ds'.map (fun d => d.1) = ds.map (fun d => d.1) := by
  -- expose the internal `succAux` result
  unfold succ at h
  -- destruct the auxiliary computation
  cases haux : succAux ds.reverse with
  | mk rev' carry =>
      -- simplify using the computed pair
      simp only [haux] at h
      split at h
      · -- carry = true case: impossible since `none ≠ some ds'`
        simp at h
      · -- carry = false case: `some rev'.reverse = some ds'`
        simp at h
        subst h
        -- widths lemma on `ds.reverse`
        have hw : rev'.map (fun d => d.1) = ds.reverse.map (fun d => d.1) := by
          have := succAux_preserves_widths ds.reverse
          simp only [haux] at this
          exact this
        -- reverse both sides and use `map_reverse`
        have hw' : (rev'.map (fun d => d.1)).reverse = (ds.reverse.map (fun d => d.1)).reverse :=
          congrArg List.reverse hw
        simpa [List.map_reverse] using hw'

theorem succ_preserves_length (ds ds' : Digits) (h : succ ds = some ds') :
    ds'.length = ds.length := by
  -- expose the internal `succAux` result
  unfold succ at h
  cases haux : succAux ds.reverse with
  | mk rev' carry =>
      simp only [haux] at h
      split at h
      · -- carry = true case: impossible since `none ≠ some ds'`
        simp at h
      · -- carry = false case: `some rev'.reverse = some ds'`
        simp at h
        subst h
        have hl : rev'.length = ds.reverse.length := by
          have := succAux_preserves_length ds.reverse
          simp only [haux] at this
          exact this
        -- `List.length_reverse` rewrites the goal
        simpa [List.length_reverse] using hl

end Digits

end AnisoHilbert

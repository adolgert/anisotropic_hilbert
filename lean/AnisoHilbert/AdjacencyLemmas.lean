import Mathlib

import AnisoHilbert.Representation

namespace AnisoHilbert

namespace BV

/-!
Small algebraic identities about how `xor` interacts with `rotR`/`rotL` and
Hamilton's transforms `T` / `Tinv`.

This file intentionally avoids any claim about Gray codes or “adjacent cubes”
yet.  Instead, it proves the algebraic part we will need later:

* applying `T e d` to two words transforms their XOR-difference by a rotation;
* applying `Tinv e d` transforms differences by the inverse rotation.

Once we have a lemma that “consecutive children are Gray-adjacent”, these
identities let us transport that adjacency through the orientation machinery.
-/

/-- Cancelling the same mask on both sides does not change the XOR-difference. -/
theorem xor_cancel_both {k : Nat} (x y e : BV k) : xor (xor x e) (xor y e) = xor x y := by
  funext i
  -- Truth-table proof (keeps this lemma independent of extra XOR-algebra imports).
  cases hx : x i <;> cases hy : y i <;> cases he : e i <;> simp [BV.xor, BV.bxor, hx, hy, he]

/-- `rotR` commutes with `xor`: it just permutes indices. -/
theorem xor_rotR {k : Nat} (r : Nat) (x y : BV k) :
    xor (BV.rotR r x) (BV.rotR r y) = BV.rotR r (xor x y) := by
  cases k with
  | zero =>
      funext i
      exact i.elim0
  | succ k' =>
      funext i
      -- Unfolding `rotR` and `xor` reduces to a pointwise statement.
      simp [BV.rotR, xor]

/-- `rotL` commutes with `xor`: it just permutes indices. -/
theorem xor_rotL {k : Nat} (r : Nat) (x y : BV k) :
    xor (BV.rotL r x) (BV.rotL r y) = BV.rotL r (xor x y) := by
  cases k with
  | zero =>
      funext i
      exact i.elim0
  | succ k' =>
      funext i
      simp [BV.rotL, xor]

/-- How `T` acts on XOR-differences.

`T e d` is XOR by `e` followed by `rotR (d+1)`.
Therefore, applying `T e d` to *both* inputs cancels the `e` and rotates the
remaining difference. -/
theorem xor_T {k : Nat} (e : BV k) (d : Nat) (x y : BV k) :
    xor (T e d x) (T e d y) = BV.rotR d.succ (xor x y) := by
  -- Expand `T` and use the two commuting/cancellation lemmas.
  simp [T, xor_rotR, xor_cancel_both]

/-- How `Tinv` acts on XOR-differences.

`Tinv e d` is `rotL (d+1)` followed by XOR by `e`.
So, applying it to both inputs cancels the `e` and rotates by `rotL (d+1)`. -/
theorem xor_Tinv {k : Nat} (e : BV k) (d : Nat) (x y : BV k) :
    xor (Tinv e d x) (Tinv e d y) = BV.rotL d.succ (xor x y) := by
  simp [Tinv, xor_rotL, xor_cancel_both]

end BV

end AnisoHilbert

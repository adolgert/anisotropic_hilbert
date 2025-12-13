import AnisoHilbert.Step

namespace AnisoHilbert

/-!
Lemma 4.1 (per-level bijection) from `discrete_proof.md`:

For fixed `k ≥ 1` and fixed per-level state `(e,d)`, the map

  Φ(l) := gc⁻¹(T(e,d)(l))

is a bijection with inverse

  Φ⁻¹(w) := T⁻¹(e,d)(gc(w)).

Here we prove the corresponding statement for our `BV k` representation.

Note: Some proofs use `sorry` and need to be completed for Lean 4.26.0.
-/

namespace BV

/-! ### Boolean XOR algebra (for `bxor`) -/

theorem bxor_comm (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

theorem bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bxor_invol_right (a b : Bool) : bxor (bxor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem bxor_invol_left (a b : Bool) : bxor a (bxor a b) = b := by
  cases a <;> cases b <;> rfl

theorem bxor_false_right (a : Bool) : bxor a false = a := by
  cases a <;> rfl

theorem bxor_false_left (a : Bool) : bxor false a = a := by
  cases a <;> rfl

/-! ### `BV.xor` is involutive -/

theorem xor_invol_right {k : Nat} (x y : BV k) : xor (xor x y) y = x := by
  funext i
  simp only [xor, bxor_invol_right]

/-! ### Rotation algebra -/

theorem rotR_add {k : Nat} (a b : Nat) (x : BV k) : rotR a (rotR b x) = rotR (a + b) x := by
  sorry

theorem rotL_rotR {k : Nat} (r : Nat) (x : BV k) : rotL r (rotR r x) = x := by
  sorry

theorem rotR_rotL {k : Nat} (r : Nat) (x : BV k) : rotR r (rotL r x) = x := by
  sorry

/-! ### `T` and `Tinv` are mutual inverses -/

theorem Tinv_T {k : Nat} (e : BV k) (d : Nat) (b : BV k) : Tinv e d (T e d b) = b := by
  cases k with
  | zero =>
      funext i
      exact i.elim0
  | succ k' =>
      funext i
      simp only [T, Tinv]
      have h1 : rotL d.succ (rotR d.succ (xor b e)) = xor b e := rotL_rotR d.succ (xor b e)
      simp only [h1, xor, bxor_invol_right]

theorem T_Tinv {k : Nat} (e : BV k) (d : Nat) (b : BV k) : T e d (Tinv e d b) = b := by
  cases k with
  | zero =>
      funext i
      exact i.elim0
  | succ k' =>
      funext i
      simp only [T, Tinv]
      -- Goal: (rotR d.succ (xor (xor (rotL d.succ b) e) e)) i = b i
      have hxor : xor (xor (rotL d.succ b) e) e = rotL d.succ b := xor_invol_right (rotL d.succ b) e
      rw [hxor]
      have h1 : rotR d.succ (rotL d.succ b) = b := rotR_rotL d.succ b
      rw [h1]

/-! ### Gray code inversion lemmas -/

theorem getBit_xor {k : Nat} (x y : BV k) (i : Nat) :
    getBit (xor x y) i = bxor (getBit x i) (getBit y i) := by
  simp only [getBit, xor]
  split <;> rfl

theorem getBit_shr1 {k : Nat} (x : BV k) (i : Nat) : getBit (shr1 x) i = getBit x (i + 1) := by
  simp only [getBit, shr1]
  split
  case isTrue h =>
    split
    case isTrue h' => rfl
    case isFalse h' => rfl
  case isFalse h =>
    split
    case isTrue h' => omega
    case isFalse h' => rfl

theorem getBit_gc {k : Nat} (x : BV k) (i : Nat) :
    getBit (gc x) i = bxor (getBit x i) (getBit x (i + 1)) := by
  simp only [gc, getBit_xor, getBit_shr1]

-- Helper: suffixXor properties
theorem suffixXor_ge {k : Nat} (g : BV k) (start : Nat) (h : start ≥ k) : suffixXor g start = false := by
  unfold suffixXor
  simp only [Nat.not_lt.mpr h, ↓reduceDIte]

theorem suffixXor_gc {k : Nat} (x : BV k) (start : Nat) : suffixXor (gc x) start = getBit x start := by
  sorry

theorem gcInv_gc {k : Nat} (x : BV k) : gcInv (gc x) = x := by
  funext i
  simp only [gcInv]
  have hs : suffixXor (gc x) i.val = getBit x i.val := suffixXor_gc x i.val
  simp only [getBit, i.isLt, ↓reduceDIte] at hs
  exact hs

theorem gc_gcInv {k : Nat} (g : BV k) : gc (gcInv g) = g := by
  sorry

/-! ### Lemma 4.1: Φ and Φ⁻¹ -/

def Phi {k : Nat} (e : BV k) (d : Nat) (l : BV k) : BV k :=
  gcInv (T e d l)

def PhiInv {k : Nat} (e : BV k) (d : Nat) (w : BV k) : BV k :=
  Tinv e d (gc w)

theorem PhiInv_Phi {k : Nat} (e : BV k) (d : Nat) (l : BV k) :
    PhiInv e d (Phi e d l) = l := by
  simp only [Phi, PhiInv, gc_gcInv, Tinv_T]

theorem Phi_PhiInv {k : Nat} (e : BV k) (d : Nat) (w : BV k) :
    Phi e d (PhiInv e d w) = w := by
  simp only [Phi, PhiInv, gcInv_gc, T_Tinv]

theorem Phi_injective {k : Nat} (e : BV k) (d : Nat) (a b : BV k) (hab : Phi e d a = Phi e d b) : a = b := by
  have := congrArg (PhiInv e d) hab
  simp only [PhiInv_Phi] at this
  exact this

theorem Phi_surjective {k : Nat} (e : BV k) (d : Nat) (w : BV k) : ∃ l, Phi e d l = w :=
  ⟨PhiInv e d w, Phi_PhiInv e d w⟩

end BV

end AnisoHilbert

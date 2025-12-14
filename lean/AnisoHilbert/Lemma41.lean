import Mathlib
import Mathlib.Tactic

import AnisoHilbert.Step

namespace AnisoHilbert

namespace BV

-- We use the same `bxor` as in `Representation.lean`.

/-! ## Small XOR algebra -/

theorem bxor_self (a : Bool) : bxor a a = false := by
  cases a <;> rfl

theorem bxor_false_right (a : Bool) : bxor a false = a := by
  cases a <;> rfl

theorem bxor_false_left (a : Bool) : bxor false a = a := by
  cases a <;> rfl

theorem bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bxor_invol_right (a b : Bool) : bxor (bxor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem bxor_invol_left (a b : Bool) : bxor b (bxor b a) = a := by
  cases a <;> cases b <;> rfl

theorem xor_invol_right {k : Nat} (x e : BV k) : xor (xor x e) e = x := by
  funext i
  -- Pointwise: (x ⊕ e) ⊕ e = x.
  simpa [xor] using (bxor_invol_right (x i) (e i))

theorem xor_invol_left {k : Nat} (x e : BV k) : xor e (xor e x) = x := by
  funext i
  -- Pointwise: e ⊕ (e ⊕ x) = x.
  simpa [xor] using (bxor_invol_left (x i) (e i))

/-! ## Rotation group laws (mod k) -/

/-- `rotR` composition adds the rotation amounts (mod `k`). -/
theorem rotR_add {k : Nat} (a b : Nat) (x : BV k) : rotR a (rotR b x) = rotR (a + b) x := by
  cases k with
  | zero =>
      rfl
  | succ k' =>
      funext i
      let n : Nat := Nat.succ k'
      have hnpos : 0 < n := Nat.succ_pos k'

      -- Normalise the nested mod-expression.
      have hval : (((i.val + a) % n + b) % n) = (i.val + (a + b)) % n := by
        -- First, replace the raw `b` by `b % n` under `% n`.
        have h1 : (((i.val + a) % n + b) % n) = ((i.val + a) % n + b % n) % n := by
          have hmodlt : ((i.val + a) % n) < n := Nat.mod_lt _ hnpos
          have hmodid : (((i.val + a) % n) % n) = ((i.val + a) % n) := Nat.mod_eq_of_lt hmodlt
          calc
            (((i.val + a) % n + b) % n)
                = ((((i.val + a) % n) % n + b % n) % n) := by
                    simpa using (Nat.add_mod ((i.val + a) % n) b n)
            _ = (((i.val + a) % n + b % n) % n) := by
                    simp [hmodid]

        -- Second, relate `(i + (a+b)) % n` to the same normal form.
        have h2 : (i.val + (a + b)) % n = ((i.val + a) % n + b % n) % n := by
          -- `Nat.add_mod (i+a) b n` gives `(i+a+b)%n = ((i+a)%n + b%n)%n`.
          have := Nat.add_mod (i.val + a) b n
          -- Re-associate `i + a + b`.
          simpa [Nat.add_assoc] using this

        -- Combine.
        calc
          (((i.val + a) % n + b) % n)
              = ((i.val + a) % n + b % n) % n := h1
          _ = (i.val + (a + b)) % n := by
              simpa using h2.symm

      -- Identify the two `Fin n` indices, and then evaluate both sides.
      have hfin : (⟨(((i.val + a) % n + b) % n), Nat.mod_lt _ hnpos⟩ : Fin n)
            = ⟨(i.val + (a + b)) % n, Nat.mod_lt _ hnpos⟩ :=
        Fin.ext hval

      -- `simp` may additionally rewrite the left index to `(i.val + a + b) % n`.
      -- Provide a second `Fin` equality to bridge that normal form.
      have hfin' : (⟨(i.val + a + b) % n, Nat.mod_lt _ hnpos⟩ : Fin n)
            = ⟨(i.val + (a + b)) % n, Nat.mod_lt _ hnpos⟩ := by
        apply Fin.ext
        simp [Nat.add_assoc]

      -- Unfold both sides and rewrite via the index equalities.
      simp [BV.rotR, n, hnpos, hfin, hfin']

/-- `rotL r` is the inverse of `rotR r`. -/
theorem rotL_rotR {k : Nat} (r : Nat) (x : BV k) : rotL r (rotR r x) = x := by
  cases k with
  | zero =>
      funext i; exact i.elim0
  | succ k' =>
      let n : Nat := Nat.succ k'
      have hnpos : 0 < n := Nat.succ_pos k'
      let s : Nat := n - (r % n)

      -- Net rotation amount is `s + r ≡ 0 (mod n)`.
      have hstep : (s + r) % n = 0 := by
        have hadd : (s + r) % n = (s % n + r % n) % n := by
          simpa using (Nat.add_mod s r n)
        let t : Nat := r % n
        by_cases ht0 : t = 0
        ·
          -- `t = 0` ⇒ `r % n = 0` and `s = n`.
          have hs : s = n := by simp [s, t, ht0]
          -- `(n + r) % n = r % n = 0`.
          simp [hadd, hs, t, ht0]
        ·
          have htlt : t < n := by
            simpa [t] using (Nat.mod_lt r hnpos)
          have htpos : 0 < t := Nat.pos_of_ne_zero ht0
          have hslt : s < n := by
            -- `s = n - t` and `t ≤ n`.
            have hle : t ≤ n := Nat.le_of_lt htlt
            -- `Nat.sub_lt_self` expects `0 < t` and `t ≤ n`.
            simpa [s] using (Nat.sub_lt_self htpos hle)
          have hsmod : s % n = s := Nat.mod_eq_of_lt hslt
          have hrmod : r % n = t := rfl
          have hsadd : s + t = n := by
            have hle : t ≤ n := Nat.le_of_lt htlt
            -- `s = n - t`.
            simpa [s] using (Nat.sub_add_cancel hle)
          calc
            (s + r) % n
                = (s % n + r % n) % n := hadd
            _ = (s + t) % n := by simp [hsmod, hrmod]
            _ = n % n := by simpa [hsadd]
            _ = 0 := Nat.mod_self n

      -- Show the composed map is pointwise equal to the identity.
      funext i
      have hi : i.val < n := by
        simpa [n] using i.isLt

      -- Unfold `rotL` and `rotR` at `i`.
      -- `rotL r (rotR r x) i = x[((i+s)%n + r)%n]`.
      -- Reduce that index to `i` using `hstep`.
      have hidx : (i.val + (s + r)) % n = i.val := by
        calc
          (i.val + (s + r)) % n
              = (i.val % n + (s + r) % n) % n := by
                  simpa using (Nat.add_mod i.val (s + r) n)
          _ = (i.val + 0) % n := by
                  simp [Nat.mod_eq_of_lt hi, hstep]
          _ = i.val % n := by simp
          _ = i.val := by simp [Nat.mod_eq_of_lt hi]

      have hfin : (⟨(i.val + (s + r)) % n, Nat.mod_lt _ hnpos⟩ : Fin n) = ⟨i.val, hi⟩ :=
        Fin.ext hidx

      -- Relate `rotL r (rotR r x)` to `rotR (s+r) x` via `rotR_add`.
      have hcomp : rotL r (rotR r x) = rotR (s + r) x := by
        -- `rotL r = rotR s` (definitional in the `succ` branch).
        simpa [BV.rotL, BV.rotR, n, s] using (rotR_add (k := Nat.succ k') (a := s) (b := r) x)

      have := congrArg (fun f => f i) hcomp
      -- Now `simp` on `rotR` and rewrite the `Fin` index.
      simpa [BV.rotR, n, hnpos, hfin] using this

/-- `rotR r` is the inverse of `rotL r`. -/
theorem rotR_rotL {k : Nat} (r : Nat) (x : BV k) : rotR r (rotL r x) = x := by
  cases k with
  | zero =>
      funext i; exact i.elim0
  | succ k' =>
      let n : Nat := Nat.succ k'
      have hnpos : 0 < n := Nat.succ_pos k'
      let s : Nat := n - (r % n)

      -- Compose to a single `rotR`.
      have hcomp : rotR r (rotL r x) = rotR (r + s) x := by
        -- `rotL r x = rotR s x` (definitional in the succ branch).
        simpa [BV.rotL, BV.rotR, n, s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (rotR_add (k := Nat.succ k') (a := r) (b := s) x)

      -- Net rotation `r + s ≡ 0 (mod n)`; reuse the computation from `rotL_rotR`.
      have hstep : (r + s) % n = 0 := by
        -- Since addition commutes, this is the same as `(s + r) % n = 0`.
        have : (s + r) % n = 0 := by
          -- Repeat the inner proof from `rotL_rotR`.
          have hadd : (s + r) % n = (s % n + r % n) % n := by
            simpa using (Nat.add_mod s r n)
          let t : Nat := r % n
          by_cases ht0 : t = 0
          ·
            have hs : s = n := by simp [s, t, ht0]
            simp [hadd, hs, t, ht0]
          ·
            have htlt : t < n := by
              simpa [t] using (Nat.mod_lt r hnpos)
            have htpos : 0 < t := Nat.pos_of_ne_zero ht0
            have hslt : s < n := by
              have hle : t ≤ n := Nat.le_of_lt htlt
              simpa [s] using (Nat.sub_lt_self htpos hle)
            have hsmod : s % n = s := Nat.mod_eq_of_lt hslt
            have hrmod : r % n = t := rfl
            have hsadd : s + t = n := by
              have hle : t ≤ n := Nat.le_of_lt htlt
              simpa [s] using (Nat.sub_add_cancel hle)
            calc
              (s + r) % n
                  = (s % n + r % n) % n := hadd
              _ = (s + t) % n := by simp [hsmod, hrmod]
              _ = n % n := by simpa [hsadd]
              _ = 0 := Nat.mod_self n
        simpa [Nat.add_comm] using this

      funext i
      have hi : i.val < n := by
        simpa [n] using i.isLt

      have hidx : (i.val + (r + s)) % n = i.val := by
        calc
          (i.val + (r + s)) % n
              = (i.val % n + (r + s) % n) % n := by
                  simpa using (Nat.add_mod i.val (r + s) n)
          _ = (i.val + 0) % n := by
                  simp [Nat.mod_eq_of_lt hi, hstep]
          _ = i.val % n := by simp
          _ = i.val := by simp [Nat.mod_eq_of_lt hi]

      have hfin : (⟨(i.val + (r + s)) % n, Nat.mod_lt _ hnpos⟩ : Fin n) = ⟨i.val, hi⟩ :=
        Fin.ext hidx

      have := congrArg (fun f => f i) hcomp
      simpa [BV.rotR, n, hnpos, hfin] using this

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

/-- Key identity: the suffix-XOR of the Gray code at position `start` recovers the original bit `x[start]`. -/
theorem suffixXor_gc {k : Nat} (x : BV k) (start : Nat) : suffixXor (gc x) start = getBit x start := by
  classical

  -- Strong induction on the measure `k - start` (the same one used in `suffixXor`).
  have main : ∀ t : Nat, ∀ start : Nat, k - start = t → suffixXor (gc x) start = getBit x start := by
    intro t
    induction t with
    | zero =>
        intro start hks
        have hk : k ≤ start := (Nat.sub_eq_zero_iff_le).mp hks
        have hsx : suffixXor (gc x) start = false :=
          suffixXor_ge (g := gc x) start (show start ≥ k from hk)
        have hgb : getBit x start = false := by
          simp [getBit, Nat.not_lt.mpr hk]
        simpa [hsx, hgb]
    | succ t ih =>
        intro start hks
        -- From `k - start = t+1` we infer `start < k`.
        have hlt : start < k := by
          apply Nat.lt_of_not_ge
          intro hk
          have h0 : k - start = 0 := Nat.sub_eq_zero_of_le hk
          have : 0 = Nat.succ t := by
            exact h0.symm.trans hks
          exact (Nat.succ_ne_zero t) (this.symm)

        -- Unfold only the *outer* layer of `suffixXor` at `start`.
        have hsuf : suffixXor (gc x) start = bxor (getBit (gc x) start) (suffixXor (gc x) (start + 1)) := by
          -- `suffixXor` is defined by a *dependent* `if` (`if h : start < k then ...`).
          -- After unfolding, `simp [hlt]` reduces the `dif_pos` branch.
          unfold suffixXor
          -- Reduce only the *outer* `if`; do not unfold the recursive call.
          rw [dif_pos hlt]
          rfl

        -- The measure decreases by 1 at the recursive call.
        have hks' : k - (start + 1) = t := by
          have hrew : k - (start + 1) = (k - start) - 1 := by
            simpa [Nat.succ_eq_add_one] using (Nat.sub_succ k start)
          simpa [hrew, hks]  -- substitute `k - start = t+1`.

        have ih' : suffixXor (gc x) (start + 1) = getBit x (start + 1) :=
          ih (start := start + 1) hks'

        -- Combine with `getBit(gc x,start) = x[start] XOR x[start+1]`.
        calc
          suffixXor (gc x) start
              = bxor (getBit (gc x) start) (suffixXor (gc x) (start + 1)) := hsuf
          _ = bxor (getBit (gc x) start) (getBit x (start + 1)) := by
              simpa [ih']
          _ = bxor (bxor (getBit x start) (getBit x (start + 1))) (getBit x (start + 1)) := by
              simpa [getBit_gc]
          _ = getBit x start := by
              simpa [bxor_assoc] using (bxor_invol_right (getBit x start) (getBit x (start + 1)))

  -- instantiate the induction at `t := k - start`.
  simpa using (main (k - start) start rfl)

/-- Gray-code inverse followed by Gray-code is the identity. -/
theorem gcInv_gc {k : Nat} (x : BV k) : gcInv (gc x) = x := by
  funext i
  simp only [gcInv]
  have hs : suffixXor (gc x) i.val = getBit x i.val := suffixXor_gc x i.val
  simp only [getBit, i.isLt, ↓reduceDIte] at hs
  exact hs

/-- Gray-code followed by Gray-code inverse is the identity. -/
theorem gc_gcInv {k : Nat} (g : BV k) : gc (gcInv g) = g := by
  funext i
  have hi : i.val < k := i.isLt

  -- One-step unfolding for `suffixXor` at an in-range index.
  have hsuf : suffixXor g i.val = bxor (getBit g i.val) (suffixXor g (i.val + 1)) := by
    -- Same remark as above: `suffixXor` uses a dependent `if`.
    unfold suffixXor
    -- Reduce only the *outer* `if`; do not unfold the recursive call.
    rw [dif_pos hi]
    rfl

  -- `getBit (gcInv g) (i+1) = suffixXor g (i+1)` (even when out-of-range).
  have hgb : getBit (gcInv g) (i.val + 1) = suffixXor g (i.val + 1) := by
    by_cases h : i.val + 1 < k
    · simp [getBit, gcInv, h]
    ·
      have hge : i.val + 1 ≥ k := Nat.le_of_not_gt h
      have hs : suffixXor g (i.val + 1) = false := suffixXor_ge (g := g) (start := i.val + 1) hge
      simp [getBit, gcInv, h, hs]

  -- Compute `gc (gcInv g)` at bit `i`.
  calc
    gc (gcInv g) i
        = bxor (gcInv g i) ((shr1 (gcInv g)) i) := by
            simp [gc, xor]
    _ = bxor (suffixXor g i.val) (getBit (gcInv g) (i.val + 1)) := by
            simp [gcInv, shr1]
    _ = bxor (suffixXor g i.val) (suffixXor g (i.val + 1)) := by
            simp [hgb]
    _ = bxor (bxor (getBit g i.val) (suffixXor g (i.val + 1))) (suffixXor g (i.val + 1)) := by
            -- Rewrite only the first occurrence of `suffixXor g i.val`.
            rw [hsuf]
    _ = getBit g i.val := by
            simpa [bxor_assoc] using (bxor_invol_right (getBit g i.val) (suffixXor g (i.val + 1)))
    _ = g i := by
            simp [getBit, hi]

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

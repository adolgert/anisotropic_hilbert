import Mathlib

import AnisoHilbert.Step

namespace AnisoHilbert

namespace BV

private theorem foldl_add_eq {α : Type} (xs : List α) (term : α → Nat) (init : Nat) :
    xs.foldl (fun acc a => acc + term a) init = init + xs.foldl (fun acc a => acc + term a) 0 := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons a xs ih =>
      -- Expand one step, then rewrite both folds using the IH.
      simp [List.foldl_cons]
      have h1 := ih (init := init + term a)
      have h2 := ih (init := term a)
      -- `simp` does the remaining associativity bookkeeping.
      simpa [h1, h2, Nat.add_assoc]

private theorem foldl_add_mul_two {α : Type} (xs : List α) (term : α → Nat) (init : Nat) :
    xs.foldl (fun acc a => acc + 2 * term a) (2 * init) = 2 * xs.foldl (fun acc a => acc + term a) init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons a xs ih =>
      -- fold once and apply the IH at the updated accumulator
      simp [List.foldl_cons]
      -- rewrite the new accumulator so the IH matches
      have hstart : 2 * init + 2 * term a = 2 * (init + term a) := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Nat.mul_add 2 init (term a)).symm
      -- now apply the IH at `init + term a`
      simpa [hstart] using ih (init := init + term a)

private theorem shiftLeft_one_succ (n : Nat) :
    Nat.shiftLeft 1 n.succ = 2 * Nat.shiftLeft 1 n := by
  -- `1 <<< n = 2^n`, so shifting by `n+1` multiplies by `2`.
  simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem one_shl_succ (n : Nat) : (1 <<< n.succ) = 2 * (1 <<< n) := by
  -- Convert shifts to powers of two.
  simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem toNat_succ {k : Nat} (x : BV (Nat.succ k)) :
    toNat x = Nat.bit (x 0) (toNat (fun j : Fin k => x (Fin.succ j))) := by
  -- Split off the low bit and reindex the remaining bits.
  let tail : BV k := fun j => x (Fin.succ j)
  -- Package the "tail contribution" at each index as a `Nat` term, using the same
  -- `Fin` indices that appear after `foldl_map`.
  let term : Fin k → Nat := fun j => if x j.succ = true then Nat.shiftLeft 1 j.val else 0

  -- Expand the fold defining `toNat` and split off the `0` bit.
  unfold toNat
  rw [List.finRange_succ]
  -- Avoid rewriting `Nat.shiftLeft` into `<<<` by using `simp only`.
  simp only [List.foldl_cons]
  -- `Nat.shiftLeft 1 0 = 1`, so the head accumulator is `if x 0 then 1 else 0`.
  simp only [Fin.val_zero, Nat.shiftLeft_zero, Nat.zero_add]

  -- Reindex the remaining fold from `Fin.succ`.
  simp only [List.foldl_map]

  -- Turn the conditional update into addition of `2 * term`.
  have hstep :
      (fun acc j => if x j.succ = true then acc + Nat.shiftLeft 1 (↑j.succ) else acc) =
        (fun acc j => acc + 2 * term j) := by
    funext acc j
    by_cases hj : x j.succ = true
    · -- update branch
      -- Rewrite both sides and reduce to the shift lemma.
      have hterm : term j = Nat.shiftLeft 1 j.val := by simp [term, hj]
      have hshift : Nat.shiftLeft 1 (↑j.succ) = 2 * Nat.shiftLeft 1 j.val := by
        simpa using shiftLeft_one_succ (n := j.val)
      -- `if_pos` selects the update branch.
      rw [if_pos hj, hterm]
      -- Rewrite the shifted term and close.
      simpa [hshift]
    · -- no-op branch
      rw [if_neg hj]
      simp [term, hj]

  -- Replace the step function.
  rw [hstep]

  -- Factor out the leading accumulator and the factor `2`.
  have hsum :
      List.foldl (fun acc j => acc + 2 * term j) (if x 0 then 1 else 0) (List.finRange k)
        =
      (if x 0 then 1 else 0) + 2 * List.foldl (fun acc j => acc + term j) 0 (List.finRange k) := by
    have h1 :=
      foldl_add_eq (xs := List.finRange k) (term := fun j => 2 * term j) (init := (if x 0 then 1 else 0))
    have h2 :
        List.foldl (fun acc j => acc + 2 * term j) 0 (List.finRange k)
          =
        2 * List.foldl (fun acc j => acc + term j) 0 (List.finRange k) := by
      simpa using (foldl_add_mul_two (xs := List.finRange k) (term := term) (init := 0))
    calc
      List.foldl (fun acc j => acc + 2 * term j) (if x 0 then 1 else 0) (List.finRange k)
          = (if x 0 then 1 else 0) + List.foldl (fun acc j => acc + 2 * term j) 0 (List.finRange k) := by
              simpa using h1
      _ = (if x 0 then 1 else 0) + 2 * List.foldl (fun acc j => acc + term j) 0 (List.finRange k) := by
              simp [h2]

  -- Rewrite the tail fold as `toNat tail`.
  have hTail :
      List.foldl (fun acc j => acc + term j) 0 (List.finRange k) = toNat tail := by
    unfold toNat
    have hfun :
        (fun acc j => acc + term j) = (fun acc j => if tail j then acc + Nat.shiftLeft 1 j.val else acc) := by
      funext acc j
      cases hj : tail j with
      | false =>
          simp [hj, term, Nat.add_assoc, tail]
      | true =>
          -- `tail j = true` means `x j.succ = true`, so `term j = shiftLeft 1 j.val`.
          have hx : x j.succ = true := by simpa [tail] using hj
          simp [hj, term, hx, Nat.add_assoc, tail]
    simpa [hfun]

  -- Assemble and normalize to `Nat.bit`.
  calc
    List.foldl (fun acc j => acc + 2 * term j) (if x 0 then 1 else 0) (List.finRange k)
        = (if x 0 then 1 else 0) + 2 * List.foldl (fun acc j => acc + term j) 0 (List.finRange k) := hsum
    _ = (if x 0 then 1 else 0) + 2 * toNat tail := by simp [hTail]
    _ = Nat.bit (x 0) (toNat tail) := by
        -- `Nat.bit b m` is `2*m` or `2*m+1`.
        cases h : x 0 with
        | false =>
            simp [Nat.bit, h]
        | true =>
            -- `1 + 2*m = 2*m + 1`
            simp [Nat.bit, h, Nat.add_assoc]
            simpa [Nat.add_assoc] using (Nat.add_comm 1 (2 * toNat tail))

theorem ofNat_toNat {k : Nat} (x : BV k) : ofNat (k := k) (toNat x) = x := by
  induction k with
  | zero =>
      funext i
      exact i.elim0
  | succ k ih =>
      -- Use the `Nat.bit` decomposition of `toNat` and `Nat.testBit_bit_*` lemmas.
      funext i
      let tail : BV k := fun j => x (Fin.succ j)
      have hToNat : toNat x = Nat.bit (x 0) (toNat tail) := by
        simpa [tail] using (toNat_succ (x := x))
      refine Fin.cases ?_ ?_ i
      · -- bit 0
        simp [ofNat, hToNat, Nat.testBit_bit_zero]
      · intro j
        -- higher bits shift down by one
        have : Nat.testBit (toNat tail) j.val = tail j := by
          -- Apply the IH pointwise.
          have := congrArg (fun f => f j) (ih (x := tail))
          simpa [ofNat] using this
        simp [ofNat, hToNat, Nat.testBit_bit_succ, tail, this]

end BV

end AnisoHilbert

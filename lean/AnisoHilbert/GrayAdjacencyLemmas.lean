import AnisoHilbert.Step
import AnisoHilbert.Lemma41

namespace AnisoHilbert

/-!
Gray-code adjacency facts.

For the `k`-bit reflected Gray code `gc : BV k → BV k` (defined as `x XOR (x >> 1)`),
successive integers (when increment does not wrap inside the low `k` bits)
map to vertices that differ in exactly one bit.

We formulate this as an equality

`gc(i) XOR gc(i+1) = oneHot(tsb i)`

where `tsb i` is the number of trailing `1` bits of `i` (our `tsb`), and `oneHot` is
the bitvector with a single `true` entry.
-/

namespace BV

/-- A one-hot `k`-bit word (single `true` bit). -/
def oneHotFin {k : Nat} (g : Fin k) : BV k := fun i => decide (i = g)

@[simp] lemma oneHotFin_apply {k : Nat} (g i : Fin k) : oneHotFin g i = decide (i = g) := rfl

/-!
### Small `Nat.testBit` helpers

We only need the low-bit (index `0`) toggle under successor.
The proof is by splitting `m` into even/odd using `m % 2` and rewriting with
`Nat.div_add_mod`.
-/

private lemma testBit_succ_zero (m : Nat) : Nat.testBit (m.succ) 0 = ! Nat.testBit m 0 := by
  -- split on `m % 2` (0 or 1; the `≥ 2` case is impossible)
  have hlt : m % 2 < 2 := Nat.mod_lt _ (by decide)
  cases hmod : m % 2 with
  | zero =>
      -- even: m = (m/2)*2, so `m = bit0 (m/2)` and `m+1 = bit1 (m/2)`.
      let t := m / 2
      have hdiv : t * 2 + m % 2 = m := by
        simpa [t] using (Nat.div_add_mod m 2)
      have hm : m = bit0 t := by
        -- from `t*2 + 0 = m`
        have : t * 2 = m := by simpa [hmod] using hdiv
        -- `t*2 = t+t = bit0 t`
        calc
          m = t * 2 := this.symm
          _ = bit0 t := by simp [Nat.mul_two, bit0]
      have hms : m.succ = bit1 t := by
        -- `bit1 t = bit0 t + 1`
        simp [hm, bit1, Nat.succ_eq_add_one]
      simp [hm, hms]
  | succ r =>
      cases r with
      | zero =>
          -- odd: m = (m/2)*2 + 1, so `m = bit1 (m/2)` and `m+1 = bit0 ((m/2)+1)`.
          let t := m / 2
          have hdiv : t * 2 + m % 2 = m := by
            simpa [t] using (Nat.div_add_mod m 2)
          have hm : m = bit1 t := by
            have : t * 2 + 1 = m := by simpa [hmod] using hdiv
            -- `bit1 t = bit0 t + 1 = t*2 + 1`
            calc
              m = t * 2 + 1 := this.symm
              _ = bit1 t := by simp [bit1, bit0, Nat.mul_two, Nat.succ_eq_add_one, Nat.add_assoc]
          have hms : m.succ = bit0 (t.succ) := by
            -- (2*t+1)+1 = 2*(t+1)
            -- write everything in terms of `t*2` and `mul_two`.
            --
            -- `simp` will normalize `bit0`/`bit1` and arithmetic.
            simp [hm, bit1, bit0, Nat.mul_two, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm]
          simp [hm, hms]
      | succ r2 =>
          -- impossible since `m % 2 < 2`
          exfalso
          have : (Nat.succ (Nat.succ r2)) < 2 := by simpa [hmod] using hlt
          exact Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))) this

/-!
### `ofNat` and `gc` shift lemmas

When we pass from width `k` to width `k+1`, and look at indices `Fin.succ j`,
`ofNat (bit0 m)` and `ofNat (bit1 m)` behave like `ofNat m`.
This is the usual right-shift on binary representations.
-/

private lemma ofNat_bit0_zero {k : Nat} (m : Nat) : (ofNat (k := Nat.succ k) (bit0 m)) 0 = false := by
  simp [ofNat]

private lemma ofNat_bit1_zero {k : Nat} (m : Nat) : (ofNat (k := Nat.succ k) (bit1 m)) 0 = true := by
  simp [ofNat]

private lemma ofNat_bit0_succ {k : Nat} (m : Nat) (j : Fin k) :
    (ofNat (k := Nat.succ k) (bit0 m)) (Fin.succ j) = (ofNat (k := k) m) j := by
  -- `testBit (2*m) (j+1) = testBit m j`
  simp [ofNat]

private lemma ofNat_bit1_succ {k : Nat} (m : Nat) (j : Fin k) :
    (ofNat (k := Nat.succ k) (bit1 m)) (Fin.succ j) = (ofNat (k := k) m) j := by
  -- `testBit (2*m+1) (j+1) = testBit m j`
  simp [ofNat]

private lemma gc_ofNat_bit0_succ {k : Nat} (m : Nat) (j : Fin k) :
    (gc (ofNat (k := Nat.succ k) (bit0 m))) (Fin.succ j) = (gc (ofNat (k := k) m)) j := by
  -- unfold `gc` and use the `ofNat` shift facts
  -- `gc x i = x i XOR getBit x (i+1)`
  simp [gc, xor, shr1, getBit, ofNat_bit0_succ, ofNat]

private lemma gc_ofNat_bit1_succ {k : Nat} (m : Nat) (j : Fin k) :
    (gc (ofNat (k := Nat.succ k) (bit1 m))) (Fin.succ j) = (gc (ofNat (k := k) m)) j := by
  simp [gc, xor, shr1, getBit, ofNat_bit1_succ, ofNat]

/-!
### Main adjacency lemma

Assuming `tsb i < k` (i.e. there is a `0` bit among the lowest `k` bits),
incrementing `i` does not wrap in the `k`-bit truncation, and the Gray code
changes exactly in bit `tsb i`.
-/

theorem xor_gc_ofNat_succ_eq_oneHotFin
    {k : Nat} (i : Nat) (ht : tsb i < k) :
    xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin ⟨tsb i, ht⟩ := by
  induction k generalizing i with
  | zero =>
      -- `tsb i < 0` is impossible
      cases (Nat.not_lt_zero _ ht)
  | succ k ih =>
      -- split on `i % 2` (0 or 1)
      have hlt : i % 2 < 2 := Nat.mod_lt _ (by decide)
      cases hmod : i % 2 with
      | zero =>
          -- even case: `tsb i = 0`, and `i = bit0 (i/2)`
          let m : Nat := i / 2
          have hi : i = bit0 m := by
              have h := Nat.div_add_mod i 2
              have hm2 : m * 2 = i := by
                -- `i / 2 * 2 + i % 2 = i`
                simpa [m, hmod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
              calc
                i = m * 2 := by simpa using hm2.symm
                _ = bit0 m := by simp [Nat.mul_two, bit0]
          have hsucc : i.succ = bit1 m := by
              simp [hi, bit1, bit0, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          have htsb : tsb i = 0 := by
            simp [tsb, hmod]
          -- show pointwise equality
          ext j
          refine Fin.cases ?hz ?hs j
          · -- j = 0
            -- both words share the same `getBit` at 1; the leading bit differs
            -- so the Gray code differs at bit 0.
            subst hi; subst hsucc
            -- simplify to a Bool identity
            -- (we also rewrite `tsb (bit0 m)` to `0` so the RHS is `oneHotFin 0`)
            simp [oneHotFin, htsb, ofNat_bit0_zero, ofNat_bit1_zero, gc, xor, shr1, getBit, ofNat]
          · intro j
            subst hi; subst hsucc
            -- higher bits of Gray codes agree, so XOR is false
            simp [oneHotFin, htsb, gc_ofNat_bit0_succ, gc_ofNat_bit1_succ, xor, bxor_self]
      | succ r =>
          cases r with
          | zero =>
              -- odd case: `i = bit1 (i/2)`, `i+1 = bit0 ((i/2)+1)`
              let m : Nat := i / 2
              have hi : i = bit1 m := by
                      have h := Nat.div_add_mod i 2
                      have hm2 : m * 2 + 1 = i := by
                        -- `i / 2 * 2 + i % 2 = i`
                        simpa [m, hmod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
                      calc
                        i = m * 2 + 1 := by simpa using hm2.symm
                        _ = bit1 m := by simp [bit1, bit0, Nat.mul_two, Nat.add_assoc]
              have hsucc : i.succ = bit0 (m.succ) := by
                -- (2*m+1)+1 = 2*(m+1)
                simp [hi, bit1, bit0, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                  Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
              have htsb : tsb i = Nat.succ (tsb m) := by
                -- `i % 2 = 1` so we take the recursive branch
                unfold tsb
                simp [hmod]
              have ht' : tsb m < k := by
                -- from `succ (tsb m) < succ k`
                have : Nat.succ (tsb m) < Nat.succ k := by simpa [htsb] using ht
                exact Nat.lt_of_succ_lt_succ this
              have ih' := ih (i := m) ht'
              ext j
              refine Fin.cases ?hz ?hs j
              · -- bit 0: unchanged for odd step
                subst hi; subst hsucc
                -- RHS: `oneHotFin ⟨succ (tsb m), _⟩` is false at index 0
                -- LHS: use `testBit_succ_zero` to show the Gray-code bit 0 is equal
                simp [oneHotFin, htsb, gc, xor, shr1, getBit, ofNat, testBit_succ_zero]
              · intro j
                subst hi; subst hsucc
                -- lift IH through `Fin.succ`
                -- LHS at `Fin.succ j` reduces to the IH stream at `j`
                -- and RHS reduces by `decide` congruence.
                --
                -- First rewrite the `gc` terms using the shift lemmas.
                -- Then apply IH.
                have :
                    (xor (gc (ofNat (k := k) m)) (gc (ofNat (k := k) m.succ))) j =
                      (oneHotFin ⟨tsb m, ht'⟩) j := by
                  simpa [oneHotFin] using congrArg (fun f => f j) ih'
                -- Now normalize both sides to the width-`succ k` statement.
                simp [oneHotFin, htsb, xor, gc_ofNat_bit1_succ, gc_ofNat_bit0_succ, this]
          | succ r2 =>
              -- impossible since `i % 2 < 2`
              exfalso
              have : (Nat.succ (Nat.succ r2)) < 2 := by simpa [hmod] using hlt
              exact Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))) this

theorem gc_ofNat_succ_adjacent
    {k : Nat} (i : Nat) (ht : tsb i < k) :
    ∃ g : Fin k, xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin g := by
  refine ⟨⟨tsb i, ht⟩, ?_⟩
  simpa using xor_gc_ofNat_succ_eq_oneHotFin (k := k) i ht

end BV

end AnisoHilbert

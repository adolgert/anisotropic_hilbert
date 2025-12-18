import AnisoHilbert.Loops
import AnisoHilbert.Lemma41
import AnisoHilbert.PlaneAccumulatorLemmas

namespace AnisoHilbert

/-!
Level-indexed statements that mirror the structure of Theorem 4.4 in `discrete_proof.md`.

This file is intended to be the next “bridge” layer:

* prove the one-step decoding identity at a fixed level (uses Lemma 4.1), and
* state the full level-indexed encode/decode inversion lemma for later induction.

We keep the main induction proof as a skeleton for now; the hard sub-lemmas
needed are:

1. correctness of `writePlane` against `packPlane` (requires `pos?`/`get` facts and
   `Nodup` of active axis lists), and
2. totality of activation embedding for consecutive `activeAxes` lists.
-/

namespace Level

/--
Overwrite bits strictly below level `s` (i.e. bit indices `< s`) from `src` into `dst`.

This is the natural “accumulator invariant” for level-indexed decoding:
`decodeFromLevel s …` should overwrite exactly planes `0 .. s-1`.
-/
def overwriteBelow {n : Nat} {m : Exponents n} (dst src : PointBV m) (s : Nat) : PointBV m :=
  fun j =>
    fun t => if t.val < s then src j t else dst j t

/-- One-step plane reconstruction lemma (Lemma 4.1 instantiated to `hilbertStep`). -/
theorem decodePlane_of_hilbertStep
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat) :
    Tinv st.e st.dPos.val (BV.gc (hilbertStep (A := A) st p i).w) =
      (hilbertStep (A := A) st p i).l := by
  -- Lemma 4.1 says: Tinv e d (gc (gcInv (T e d l))) = l.
  have h := BV.PhiInv_Phi (k := A.length) (e := st.e) (d := st.dPos.val) (l := packPlane A p i)
  -- `hilbertStep` defines `.l = packPlane …` and `.w = gcInv (T … (.l))`.
  simpa [BV.Phi, BV.PhiInv, hilbertStep] using h

/--
The state update computed by `hilbertStep` matches the shared `stateUpdate` helper
used by the full encode/decode loops.
-/
theorem hilbertStep_stateUpdate
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat) :
    (hilbertStep (A := A) st p i).stNext =
      stateUpdate (A := A) st (hilbertStep (A := A) st p i).w := by
  -- This is definitional: both sides compute the same expressions.
  simp [hilbertStep, stateUpdate]

/--
The "seam" lemma connecting a single-level `writePlane` with the accumulator invariant.

After decoding plane `s'` and writing it into an accumulator `pAcc`, the recursive
result is stated in terms of `overwriteBelow` at threshold `s'`.  This lemma rewrites
that to threshold `s'+1`, so it can be compared directly to the outer goal.

This is exactly the `hSeam` step in `discrete_proof.md`.
-/
theorem overwriteBelow_seam
    {n : Nat} {m : Exponents n} (pAcc p : PointBV m) (s' : Nat) :
    let A := activeAxes m (Nat.succ s')
    let p1 := writePlane A (packPlane A p s') pAcc s'
    overwriteBelow p1 p s' = overwriteBelow pAcc p (Nat.succ s') := by
  intro A p1
  -- Unfold `overwriteBelow` and discharge using the plane-accumulator lemma.
  -- (This lemma is proven in `PlaneAccumulatorLemmas.lean` without importing this file.)
  simpa [overwriteBelow, p1, A] using
    Plane.overwriteBelow_writePlane_packPlane_activeAxes (m := m) (pAcc := pAcc) (p := p) (i := s')

/--
Level-indexed inversion statement (Theorem 4.4 “by induction on levels”, but with
an explicit accumulator via `overwriteBelow`).

This is the next target lemma; proof will be by induction on `s`.
-/
theorem decodeFromLevel_encodeFromLevel
    {n : Nat} {m : Exponents n} (p : PointBV m) :
    ∀ s : Nat, ∀ pAcc : PointBV m, ∀ st : State n (activeAxes m s), ∀ ds : Digits,
      encodeFromLevel (m := m) p s st = some ds →
      decodeFromLevel (m := m) s st ds pAcc = some (overwriteBelow pAcc p s) := by
  intro s
  induction s with
  | zero =>
      intro pAcc st ds hEnc
      -- At level `0`, the encoder always returns `[]`, so the digit stream must be `[]`.
      have hds : ds = [] := by
        simpa [encodeFromLevel] using hEnc
      subst hds

      -- Now the decoder at level `0` reduces to the accumulator unchanged.
      -- The remaining goal is exactly `pAcc = overwriteBelow pAcc p 0`.
      simp [decodeFromLevel]

      -- And `overwriteBelow _ _ 0` is pointwise the identity on its destination.
      funext j
      funext t
      have ht : ¬ t.val < 0 := Nat.not_lt_zero _
      simp [overwriteBelow, ht]
  | succ s0 ih =>
      intro pAcc st ds hEnc
      -- Split on whether `s0 = 0` (one level left) or `s0 = succ s` (true recursion).
      cases s0 with
      | zero =>
          -- ### Case: `s = 1` (no recursive call / no activation embedding)
          --
          -- Ordering (no embedding):
          --   encode: packPlane → T → gcInv  (digit)
          --   decode: gc → Tinv → writePlane
          --
          -- After rewriting the reconstructed plane via `decodePlane_of_hilbertStep`,
          -- use `overwriteBelow_seam` at `s' = 0` to show that writing plane 0 is
          -- exactly `overwriteBelow _ _ 1`.
          simp [encodeFromLevel] at hEnc
          -- After the simp, `ds` is definitionally `[digit]`.
          cases hEnc
          -- Now unfold the decoder on that singleton digit list.
          --
          -- At this point the goal is of the form
          --   `some p1 = some (overwriteBelow pAcc p 1)`
          -- where `p1` is the level-0 write computed by the decoder.
          --
          -- The key rewrite is that the decoder's reconstructed plane `l` equals
          -- `packPlane (activeAxes m 1) p 0`.
          have hPlane :
              Tinv st.e st.dPos.val (BV.gc (hilbertStep (A := activeAxes m 1) st p 0).w)
                = packPlane (activeAxes m 1) p 0 := by
            -- `decodePlane_of_hilbertStep` gives `… = step.l`, and `step.l` is defeq to `packPlane …`.
            simpa [hilbertStep] using
              (decodePlane_of_hilbertStep (A := activeAxes m 1) st p 0)
          -- Use the seam lemma specialized to `s' = 0`.
          have hSeam :
              let A := activeAxes m 1
              let p1 := writePlane A (packPlane A p 0) pAcc 0
              p1 = overwriteBelow pAcc p 1 := by
            intro A p1
            -- `overwriteBelow p1 p 0 = p1`.
            have := overwriteBelow_seam (m := m) (pAcc := pAcc) (p := p) (s' := 0)
            simpa [overwriteBelow, p1, A] using this
          -- Extract the let-bound seam statement as a plain equation.
          have hSeam' :
              writePlane (activeAxes m 1) (packPlane (activeAxes m 1) p 0) pAcc 0
                = overwriteBelow pAcc p 1 := by
            simpa using hSeam
          -- Unfold the decoder for a singleton digit list and simplify.
          -- `hPlane` rewrites the reconstructed plane, and `hSeam'` closes the accumulator goal.
          simp [decodeFromLevel, hPlane, hSeam', overwriteBelow]
      | succ s =>
          -- ### Case: `s = succ (succ s)` (recursive call + activation embedding)
          --
          -- This branch is where the seam bookkeeping matters.
          -- We structure the proof to make the ordering explicit:
          --
          --  (1) `encodeFromLevel` produces:
          --      * the head digit `digit := ⟨A.length, step.w⟩`
          --      * an embedding witness `hEmbed : embedState? step.stNext = some st'`
          --      * the recursive encoding equality `hRec : encodeFromLevel p (succ s) st' = some rest`
          --
          --  (2) `decodeFromLevel` consumes the head digit and computes:
          --      * `l := Tinv … (gc step.w)` and `p1 := writePlane A l pAcc i`
          --      * `stNext := stateUpdate … step.w`
          --
          --  (3) **Before IH**:
          --      use `decodePlane_of_hilbertStep` to rewrite `l` into `packPlane …`,
          --      and use `hilbertStep_stateUpdate` + `hEmbed` to force the decoder
          --      into the same `some st'` branch.
          --
          --  (4) **Apply IH** to the recursive call, with accumulator `p1`.
          --
          --  (5) **After IH**:
          --      apply `overwriteBelow_seam` (your `hSeam`) to rewrite
          --      `overwriteBelow p1 p i` into `overwriteBelow pAcc p (i+1)`.
          --
          -- Name the active axes at this level and the one-step encoding output.
          let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s))
          let step : StepOut n A := hilbertStep (A := A) st p (Nat.succ s)
          let digit : Digit := ⟨A.length, step.w⟩

          -- Unfold the encoder to obtain:
          --   hEmb : embedState? step.stNext = some st'
          --   hRec : encodeFromLevel p (succ s) st' = some rest
          --   ds = digit :: rest
          --
          -- Use `split` on the nested matches (more robust than rewriting them with `simp`).
          simp [encodeFromLevel, A, step, digit] at hEnc
          split at hEnc
          · -- embedState? = none: impossible under `= some ds`
            cases hEnc
          · rename_i st' hEmb
            split at hEnc
            · -- recursive encode returned `none`: impossible under `= some ds`
              cases hEnc
            · rename_i rest hRec
              -- Now hEnc : some (digit :: rest) = some ds
              injection hEnc with hDs
              subst hDs

              -- Decoder-side: rewrite the reconstructed plane before the IH.
              have hPlane :
                  Tinv st.e st.dPos.val (BV.gc step.w) = packPlane A p (Nat.succ s) := by
                -- `decodePlane_of_hilbertStep` gives `… = (hilbertStep …).l`.
                -- With `step := hilbertStep …`, `step.l` is defeq to `packPlane …`.
                simpa [step, hilbertStep] using
                  (decodePlane_of_hilbertStep (A := A) st p (Nat.succ s))

              -- Decoder-side: align the embedding branch by rewriting the state update.
              have hState : step.stNext = stateUpdate (A := A) st step.w := by
                simpa [step] using (hilbertStep_stateUpdate (A := A) st p (Nat.succ s))
              have hEmb' :
                  Embed.embedState? (Aold := A) (Anew := activeAxes m (Nat.succ s))
                    (stateUpdate (A := A) st step.w) = some st' := by
                simpa [hState] using hEmb

              -- Define the accumulator point after writing this plane *as it should be*.
              -- This is the `p1` that will be fed into the recursive IH.
              let p1 : PointBV m := writePlane A (packPlane A p (Nat.succ s)) pAcc (Nat.succ s)

              -- Apply the IH to the recursive call with accumulator `p1`.
              have ihRes :
                  decodeFromLevel (m := m) (Nat.succ s) st' rest p1 =
                    some (overwriteBelow p1 p (Nat.succ s)) :=
                ih (pAcc := p1) (st := st') (ds := rest) hRec

              -- This is the `hSeam` rewrite: it happens **after** `ihRes`.
              have hSeam : overwriteBelow p1 p (Nat.succ s) = overwriteBelow pAcc p (Nat.succ (Nat.succ s)) := by
                -- `overwriteBelow_seam` is stated with `let`-bindings.
                -- `simpa` instantiates them with our `A` and `p1`.
                simpa [A, p1] using
                  (overwriteBelow_seam (m := m) (pAcc := pAcc) (p := p) (s' := Nat.succ s))

              -- Final assembly:
              --   decode (one step) → recursive decode
              --   rewrite by IH (`ihRes`)
              --   rewrite by seam (`hSeam`)
              --
              -- Unfold/simplify the decoder one step; then rewrite by IH and the seam lemma.
              -- First, identify the decoder's accumulator with our `p1`.
              have hp1' :
                  writePlane A (Tinv st.e st.dPos.val (BV.gc step.w)) pAcc (Nat.succ s) = p1 := by
                simp [p1, hPlane]

              -- Evaluate the outer decoder one step and use `hEmb'` to select the recursive branch.
              have hOuter :
                  decodeFromLevel (m := m) (Nat.succ (Nat.succ s)) st (digit :: rest) pAcc =
                    decodeFromLevel (m := m) (Nat.succ s) st' rest p1 := by
                simp [decodeFromLevel, A, digit, hEmb', hp1']

              -- Now use IH then seam.
              calc
                decodeFromLevel (m := m) (Nat.succ (Nat.succ s)) st (digit :: rest) pAcc =
                    decodeFromLevel (m := m) (Nat.succ s) st' rest p1 := hOuter
                _ = some (overwriteBelow p1 p (Nat.succ s)) := ihRes
                _ = some (overwriteBelow pAcc p (Nat.succ (Nat.succ s))) := by
                    simpa [hSeam]
end Level

end AnisoHilbert

import Std

namespace AnisoHilbert

/-!
Representation skeleton for an anisotropic (unequal-dimension) Hilbert lattice curve.

This file is intentionally "definitions only": it sets up types and core operators
so that we can iterate on formal proofs next.

The structure mirrors the bit-labelling / transforms used by Hamilton (2006):
- vertices labelled by bitstrings
- transforms built from XOR and bit-rotations
- per-level extraction of a bit-plane as a k-bit word
- active-axis masks when dimensions have unequal precisions

Reference: "Compact Hilbert Indices" (Technical Report CS-2006-07). fileciteturn0file0
-/

abbrev Axis (n : Nat) := Fin n
abbrev Exponents (n : Nat) := Axis n → Nat

/-- Nondegenerate exponent data: every axis has at least one bit (exclude `m j = 0`). -/
def ExponentsPos {n : Nat} (m : Exponents n) : Prop :=
  ∀ j : Axis n, 0 < m j

/-- A bitvector of length `k`, represented as a total function `Fin k → Bool`.

We use this instead of committing immediately to `Std.BitVec` APIs.
Later we can either:
- prove it is defeq/isomorphic to `BitVec k`, or
- swap the abbrev to `BitVec k` once we are confident the library support is sufficient.
-/
abbrev BV (k : Nat) := Fin k → Bool

namespace BV

/-- Boolean XOR (total, definitional). -/
def bxor (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

/-- Bitwise XOR on `BV k`. -/
def xor {k : Nat} (x y : BV k) : BV k :=
  fun i => bxor (x i) (y i)

/-- Rotate right by `r` (mod `k`). For `k = 0`, this is the identity on the empty type. -/
def rotR {k : Nat} (r : Nat) (x : BV k) : BV k :=
  match k with
  | 0 => x
  | Nat.succ k' =>
      fun i =>
        let n := Nat.succ k'
        x ⟨(i.val + r) % n, by
            have : n > 0 := Nat.succ_pos k'
            exact Nat.mod_lt _ this⟩

/-- Rotate left by `r` (mod `k`). For `k = 0`, this is the identity on the empty type. -/
def rotL {k : Nat} (r : Nat) (x : BV k) : BV k :=
  match k with
  | 0 => x
  | Nat.succ k' =>
      let n := Nat.succ k'
      let s := n - (r % n)   -- add `s ≡ -r (mod n)`
      fun i =>
        x ⟨(i.val + s) % n, by
            have : n > 0 := Nat.succ_pos k'
            exact Nat.mod_lt _ this⟩

end BV

/-- Total bit access on a `BV len` using a `Nat` index.
Out-of-range indices return `false`, matching the informal convention that missing bits are 0. -/
def getBit {len : Nat} (x : BV len) (i : Nat) : Bool :=
  if h : i < len then x ⟨i, h⟩ else false

/-- Total bit update on a `BV len`. If `i ≥ len` this is a no-op. -/
def setBit {len : Nat} (x : BV len) (i : Nat) (b : Bool) : BV len :=
  fun k => if k.val = i then b else x k

/-- Coordinate space: each axis `j` has precision `m j` bits. -/
abbrev PointBV {n : Nat} (m : Exponents n) := (j : Axis n) → BV (m j)

/-- Deterministic axis priority key: sort by `m j` (shorter dimensions first),
breaking ties by axis id. -/
def axisKey {n : Nat} (m : Exponents n) (j : Axis n) : Nat :=
  (m j) * (n.succ) + j.val

/-- Stable insertion into a list sorted by a `Nat` key. -/
def insertByKey {α : Type} (key : α → Nat) (a : α) : List α → List α
| [] => [a]
| b :: bs =>
    if key a ≤ key b then a :: b :: bs
    else b :: insertByKey key a bs

/-- Stable insertion sort by a `Nat` key (definition-only, good enough for a skeleton). -/
def sortByKey {α : Type} (key : α → Nat) : List α → List α
| [] => []
| a :: as => insertByKey key a (sortByKey key as)

/-- All axes in canonical id order. -/
def allAxes (n : Nat) : List (Axis n) :=
  List.finRange n

/-- Active axes at (1-based) level `s`: `j` is active iff `m j ≥ s`.
Returned as an ordered list, sorted by `axisKey`. -/
def activeAxes {n : Nat} (m : Exponents n) (s : Nat) : List (Axis n) :=
  sortByKey (axisKey m) ((allAxes n).filter (fun j => s ≤ m j))

/-- Position of an element in a list, as a `Fin xs.length` if present. -/
def pos? {α : Type} [DecidableEq α] : (xs : List α) → α → Option (Fin xs.length)
| [], _ => none
| x :: xs, a =>
    if h : a = x then
      some ⟨0, by simp⟩
    else
      match pos? xs a with
      | none => none
      | some i =>
          some ⟨i.val.succ, by
            -- i.isLt : i.val < xs.length
            simpa using Nat.succ_lt_succ i.isLt⟩

/-- Pack one bit-plane `i` of a point `p` into a `k`-bit word, using an ordered active-axis list `A`. -/
def packPlane {n : Nat} {m : Exponents n} (A : List (Axis n)) (p : PointBV m) (i : Nat) : BV A.length :=
  fun t =>
    let j := A.get t
    getBit (p j) i

/-- Unpack a packed plane back into an `Axis n → Bool` map (inactive axes map to `false`). -/
def unpackPlane {n : Nat} (A : List (Axis n)) (l : BV A.length) : (Axis n → Bool) :=
  fun j =>
    match pos? A j with
    | none => false
    | some t => l t

/-- Write a packed plane into a point (touching only axes in `A`; other axes unchanged). -/
def writePlane {n : Nat} {m : Exponents n} (A : List (Axis n)) (l : BV A.length) (p : PointBV m) (i : Nat) : PointBV m :=
  fun j =>
    match pos? A j with
    | none => p j
    | some t => setBit (p j) i (l t)

/-- Hamilton-style T-transform on a `k`-bit word: XOR by `e` then rotate right by `d+1`. -/
def T {k : Nat} (e : BV k) (d : Nat) (b : BV k) : BV k :=
  BV.rotR (d.succ) (BV.xor b e)

/-- Inverse of `T`: rotate left by `d+1` then XOR by `e`. -/
def Tinv {k : Nat} (e : BV k) (d : Nat) (b : BV k) : BV k :=
  BV.xor (BV.rotL (d.succ) b) e

end AnisoHilbert

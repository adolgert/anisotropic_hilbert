import AnisoHilbert.MutualInverses
import AnisoHilbert.EncodeTotal

namespace AnisoHilbert

/-!
Convenience theorems that remove `Option` hypotheses from the *encoder* side.

The core theorem in `MutualInverses.lean` is stated in the proof-friendly form

  encodeDigits? p = some ds → decodeDigits? ds = some p

This file packages the encoder totality lemma (`Encode.encodeDigits_spec`) so that
clients can simply write

  decodeDigits? (Encode.encodeDigits p) = some p.

This is the same statement, but it avoids the “pick a `ds` and carry an equality”
pattern in downstream proofs.
-/

namespace MutualTotal

open Encode
open Mutual

theorem decodeDigits?_encodeDigits
    {n : Nat} {m : Exponents n} (p : PointBV m) :
    decodeDigits? (m := m) (Encode.encodeDigits (m := m) p) = some p := by
  -- `Encode.encodeDigits_spec : encodeDigits? p = some (encodeDigits p)`
  exact Mutual.decodeDigits?_encodeDigits? (m := m) (p := p)
    (ds := Encode.encodeDigits (m := m) p)
    (h := Encode.encodeDigits_spec (m := m) p)

end MutualTotal

end AnisoHilbert

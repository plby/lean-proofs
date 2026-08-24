import ErdosProblems.Erdos360.AffineConnector
import ErdosProblems.Erdos360.CyclicInverse

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-!
# A constant-loss cyclic inverse connector

The final resolution only requires absolute multiplicative constants.  This
module therefore records a robust alternative to the sharp fibre-excess
endpoint: the public dense-core completion already covers the original
cyclic set by long progressions, and the coarse controlled-fibre mass and
support-span estimates make that cover linear in the original cardinality.
-/

/-- A normalized affine product core gives the *original* cyclic set a long
progression cover of mass at most `768 |B|`.  The deliberately generous
constant keeps the arithmetic integral: `L ≤ 2s`, `s|H| ≤ 4Δ`, and
`Δ ≤ 2|X|` under strict `5/2` doubling. -/
theorem normalized_affine_productCore_linear_cover
    {m g : ℕ} [NeZero g] [NeZero (m * g)]
    {B C D : Finset (ZMod (m * g))}
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m g D)).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m g D))
    (hAcard : 6 ≤
      (firstCoordinateSet (zmodQuotRemImage m g D)).card)
    (hgcd : (firstCoordinateSet (zmodQuotRemImage m g D)).gcd
      (fun n => (n : ℤ)) = 1)
    (hXsmall : 2 *
        (zmodQuotRemImage m g D + zmodQuotRemImage m g D).card <
      5 * (zmodQuotRemImage m g D).card) :
    ∃ mass : ℕ,
      mass ≤ 768 * B.card ∧
        HasLongProgressionCover (shiftedZmodValues B) mass := by
  classical
  let X := zmodQuotRemImage m g D
  let A := firstCoordinateSet X
  obtain ⟨base, hbase, H, u, v, _hbaseCos, _hHdense, _hbaseMax,
      _hAll, hmass, haffine⟩ :=
    exists_common_dense_coset_with_mass_bound_and_affine_labels
      X (by simpa [X, A] using hA) (by simpa [X, A] using hzero)
      (by simpa [X, A] using hAcard) (by simpa [X, A] using hgcd)
      (by simpa [X] using hXsmall)
  let L := A.max' (by simpa [X, A] using hA) + 1
  have hspan : 2 * A.max' (by simpa [X, A] using hA) < 3 * A.card := by
    simpa [X, A] using fiber_span_lt_three_halves X
      (by simpa [X, A] using hA) (by simpa [X, A] using hzero)
      (by simpa [X, A] using hAcard) (by simpa [X, A] using hgcd)
      (by simpa [X] using hXsmall)
  have hLle : L ≤ 2 * A.card := by
    dsimp only [L]
    omega
  have hLH : L * Nat.card H ≤
      8 * ((X + X).card - X.card) := by
    calc
      L * Nat.card H ≤ (2 * A.card) * Nat.card H :=
        Nat.mul_le_mul_right (Nat.card H) hLle
      _ = 2 * (A.card * Nat.card H) := by ring
      _ ≤ 2 * (4 * ((X + X).card - X.card)) :=
        Nat.mul_le_mul_left 2 (by simpa [X, A] using hmass)
      _ = 8 * ((X + X).card - X.card) := by ring
  have hdiff : (X + X).card - X.card ≤ 2 * X.card := by
    have hs := hXsmall
    change 2 * (X + X).card < 5 * X.card at hs
    omega
  have hXcard : X.card = C.card := by
    calc
      X.card = D.card := zmodQuotRemImage_card hm D
      _ = C.card := by
        rw [hDaff, zmodAffineImage_card w.isUnit]
  have hCleB : C.card ≤ B.card := Finset.card_le_card hCB
  have hmassB : 48 * (L * Nat.card H) ≤ 768 * B.card := by
    calc
      48 * (L * Nat.card H) ≤
          48 * (8 * ((X + X).card - X.card)) :=
        Nat.mul_le_mul_left 48 hLH
      _ ≤ 48 * (8 * (2 * X.card)) :=
        Nat.mul_le_mul_left 48 (Nat.mul_le_mul_left 8 hdiff)
      _ = 768 * X.card := by ring
      _ = 768 * C.card := by rw [hXcard]
      _ ≤ 768 * B.card := Nat.mul_le_mul_left 768 hCleB
  refine ⟨48 * (L * Nat.card H), hmassB, ?_⟩
  have hcover := affine_productCore_to_original_longProgressionCover
    w c hC hCB hdense hBsmall hDaff hm hA H u v haffine
  simpa [X, A, L] using hcover

end Erdos360

#print axioms Erdos360.normalized_affine_productCore_linear_cover

import ErdosProblems.Erdos587.PolynomialDenseProper

/-!
Standardize polynomial-count dense outputs. The exact common side divisor
and the uniform step multiplier bound remain polynomial in reciprocal
density at each fixed rank.
-/

open Erdos587.GeneralizedAP
open scoped BigOperators

namespace Erdos587.CFP

def denseStandardFactor (D d : ℕ) : ℕ :=
  denseProperFactor D d * (denseBoxCount D d + 1) ^ d

theorem denseStandardFactor_pos {D d : ℕ} (hD : 0 < D) : 0 < denseStandardFactor D d := by
  unfold denseStandardFactor
  exact Nat.mul_pos (denseProperFactor_pos hD) (by positivity)

theorem denseStandardFactor_le {D : ℕ} (hD : 0 < D) (d : ℕ) :
    denseStandardFactor D d ≤
      (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d * D ^ (9 * d) := by
  have hone : 1 ≤ D ^ 4 := pow_pos hD 4
  have hcount : denseBoxCount D d + 1 ≤ (256 * d + 1) * D ^ 4 := by
    calc
      denseBoxCount D d + 1 ≤ 256 * d * D ^ 4 + D ^ 4 :=
        Nat.add_le_add (denseBoxCount_le hD d) hone
      _ = (256 * d + 1) * D ^ 4 := by ring
  calc
    denseStandardFactor D d ≤
        ((4 * (256 * d + 1) * (d + 1)) ^ d * D ^ (5 * d)) *
          (((256 * d + 1) * D ^ 4) ^ d) :=
      Nat.mul_le_mul (denseProperFactor_le hD d) (Nat.pow_le_pow_left hcount d)
    _ = ((4 * (256 * d + 1) * (d + 1)) * (256 * d + 1)) ^ d *
        (D ^ (5 * d) * D ^ (4 * d)) := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ = (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d * D ^ (9 * d) := by
      rw [← pow_add]
      congr 1
      · congr 1
        ring
      · congr 1
        ring

def denseStepBound (D d : ℕ) : ℕ := 2 * denseBoxCount D d * denseStandardFactor D d

theorem denseStepBound_le {D : ℕ} (hD : 0 < D) (d : ℕ) :
    denseStepBound D d ≤
      (512 * d * (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d) * D ^ (9 * d + 4) := by
  calc
    denseStepBound D d ≤ (2 * (256 * d * D ^ 4)) *
        ((4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d * D ^ (9 * d)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (denseBoxCount_le hD d))
        (denseStandardFactor_le hD d)
    _ = (512 * d * (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d) *
        (D ^ (9 * d) * D ^ 4) := by ring
    _ = (512 * d * (4 * (256 * d + 1) ^ 2 * (d + 1)) ^ d) * D ^ (9 * d + 4) := by
      rw [← pow_add]

def PolynomialStandardOutput (Q : GeneralizedAP) (D : ℕ)
    (Xs : List (Finset ℤ)) (S : GeneralizedAP) : Prop :=
  S.rank = Q.rank ∧ S.Proper ∧ S.carrier ⊆ nvFinsetListSum Xs ∧
  S.StepMultipliersBoundedByConstant Q
    (2 * denseBoxCount D Q.rank * denseStandardFactor D Q.rank) ∧
  (∀ i : Fin S.rank, ∀ j : Fin Q.rank, i.val = j.val →
    S.length i = Q.length j / denseStandardFactor D Q.rank) ∧
  S.carrier.card = ∏ i : Fin Q.rank, (Q.length i / denseStandardFactor D Q.rank + 1)

theorem PolynomialDenseProperOutput.exists_standardized
    {Q R : GeneralizedAP} {D : ℕ} {Xs : List (Finset ℤ)}
    (h : PolynomialDenseProperOutput Q D Xs R) (hD : 0 < D)
    (hlen : Xs.length = denseBoxCount D Q.rank) :
    ∃ S : GeneralizedAP, PolynomialStandardOutput Q D Xs S := by
  let F := denseProperFactor D Q.rank
  let t := Xs.length
  let S := R.commonSideCrop Q h.1 F t
  have hF : 0 < F := denseProperFactor_pos hD
  have hSproper : S.Proper :=
    R.commonSideCrop_proper Q F t hF h.1 h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2
  have hSuniform : S.StepMultipliersBoundedByConstant Q
      (2 * t * (F * (t + 1) ^ Q.rank)) :=
    R.commonSideCrop_stepMultipliersBoundedByConstant Q F t hF h.1 h.2.1
      h.2.2.2.2.1 h.2.2.2.2.2.2 h.2.2.2.1
  have hSsub : S.carrier ⊆ nvFinsetListSum Xs :=
    (R.commonSideCrop_subset Q F t hF h.1 h.2.1 h.2.2.2.2.1
      h.2.2.2.2.2.2).trans h.2.2.2.2.2.1
  refine ⟨S, h.1, hSproper, hSsub, ?_, ?_, ?_⟩
  · change S.StepMultipliersBoundedByConstant Q
      (2 * Xs.length * (F * (Xs.length + 1) ^ Q.rank)) at hSuniform
    rw [hlen] at hSuniform
    exact hSuniform
  · intro i j hij
    change Q.length (Fin.cast h.1 i) / (F * (Xs.length + 1) ^ Q.rank) = _
    have hidx : Fin.cast h.1 i = j := Fin.ext hij
    rw [hidx, hlen]
    rfl
  · rw [R.commonSideCrop_card Q h.1 F t hSproper]
    change (∏ i : Fin Q.rank, (Q.length i / (F * (Xs.length + 1) ^ Q.rank) + 1)) = _
    rw [hlen]
    rfl

theorem exists_standardized_GAP_of_dense_summands
    (Q : GeneralizedAP) (D : ℕ) (hD : 0 < D) (hQproper : Q.Proper)
    (Xs : List (Finset ℤ)) (hlen : Xs.length = denseBoxCount D Q.rank)
    (hXs : ∀ X ∈ Xs, X ⊆ Q.carrier)
    (hdense : ∀ X ∈ Xs, Q.boxCard ≤ D * X.card) :
    ∃ S : GeneralizedAP, PolynomialStandardOutput Q D Xs S := by
  obtain ⟨R, hR⟩ := exists_large_proper_GAP_of_dense_summands Q D hD hQproper Xs hlen hXs hdense
  exact hR.exists_standardized hD hlen

end Erdos587.CFP

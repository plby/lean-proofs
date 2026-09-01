/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterOrbitFourier

/-!
# Second-moment bounds for arithmetic orbit kernels
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace Erdos984

noncomputable section

lemma normSq_hunterGeomSum_le_X_sq
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    Complex.normSq (hunterGeomSum D theta d q) ≤ (hunterX D : ℝ) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_hunterGeomSum_le_X D theta d q) 2

lemma normSq_hunterGeomSum_le_tolerance_sq
    (D : ℕ) (hD : 4 ≤ D) (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D))
    (hq : q ∉ hunterResonantDigits D theta d) :
    Complex.normSq (hunterGeomSum D theta d q) ≤
      (1 / hunterPhaseTolerance D) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_hunterGeomSum_le_of_nonresonant D hD theta d q hq) 2

lemma sq_hunterLocalizedCoeff_le_mean_sq
    (D : ℕ) (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    hunterLocalizedCoeff D q ^ 2 ≤ hunterKernelMean D ^ 2 := by
  exact pow_le_pow_left₀ (hunterLocalizedCoeff_nonneg D q)
    (hunterLocalizedCoeff_le_mean D q) 2

/-- The resonant contribution is controlled only by its cardinality; the
nonresonant contribution uses the complete coefficient `ℓ²` bound. -/
lemma integral_normSq_hunterOrbitKernelSum_le
    (D : ℕ) (hD : 4 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    (a d : ℕ) (hd : 0 < d) (hdN : d < hunterN D) :
    ∫ center : UnitAddTorus (Fin D),
        Complex.normSq (hunterOrbitKernelSum D theta a d center) ≤
      ((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) *
          hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 +
        hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 := by
  classical
  let Q := Fin D → HunterKernelDigit (hunterKernelPower D)
  let R := hunterResonantDigits D theta d
  let f : Q → ℝ := fun q ↦
    hunterLocalizedCoeff D q ^ 2 *
      Complex.normSq (hunterGeomSum D theta d q)
  have hf_nonneg (q : Q) : 0 ≤ f q :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hpartition :
      ∑ q : Q, f q =
        (∑ q ∈ R, f q) +
          ∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R), f q := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset Q) (fun q ↦ q ∈ R) f]
    congr 2
    all_goals
      ext q
      simp
  have hres : ∑ q ∈ R, f q ≤
      (R.card : ℝ) * (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) := by
    calc
      ∑ q ∈ R, f q ≤
          ∑ _q ∈ R,
            hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        dsimp [f]
        exact mul_le_mul
          (sq_hunterLocalizedCoeff_le_mean_sq D q)
          (normSq_hunterGeomSum_le_X_sq D theta d q)
          (Complex.normSq_nonneg _) (sq_nonneg _)
      _ = (R.card : ℝ) *
          (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) := by simp
  have hnonres :
      ∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R), f q ≤
        hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 := by
    calc
      ∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R), f q ≤
          ∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R),
            hunterLocalizedCoeff D q ^ 2 *
              (1 / hunterPhaseTolerance D) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply normSq_hunterGeomSum_le_tolerance_sq D hD theta d q
          simpa [R] using hq
        · exact sq_nonneg _
      _ = (1 / hunterPhaseTolerance D) ^ 2 *
          (∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R),
            hunterLocalizedCoeff D q ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        ring
      _ ≤ (1 / hunterPhaseTolerance D) ^ 2 *
          (∑ q : Q, hunterLocalizedCoeff D q ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro q _hq _hnot
            exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ (1 / hunterPhaseTolerance D) ^ 2 * hunterKernelMean D := by
        exact mul_le_mul_of_nonneg_left
          (sum_sq_hunterLocalizedCoeff_le_mean D) (sq_nonneg _)
      _ = hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 := by ring
  rw [integral_normSq_hunterOrbitKernelSum, show
    (∑ q : Q, hunterLocalizedCoeff D q ^ 2 *
      Complex.normSq (hunterGeomSum D theta d q)) = ∑ q : Q, f q by rfl,
    hpartition]
  calc
    (∑ q ∈ R, f q) +
        ∑ q ∈ (Finset.univ.filter fun q : Q ↦ q ∉ R), f q ≤
      (R.card : ℝ) *
          (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) +
        hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 :=
      add_le_add hres hnonres
    _ ≤ ((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) *
          hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 +
        hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 := by
      have hmain : (R.card : ℝ) *
            (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) ≤
          ((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) *
            hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by
        calc
        (R.card : ℝ) *
            (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) ≤
          (((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) : ℝ) *
            (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_hunterResonantDigits_le D hD htheta hd hdN
          · positivity
        _ = ((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) *
            hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by ring
      exact add_le_add hmain le_rfl

end

end Erdos984

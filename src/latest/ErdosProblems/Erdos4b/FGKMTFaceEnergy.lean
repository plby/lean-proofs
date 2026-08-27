/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceCutoff
import ErdosProblems.Erdos4b.FGKMTCutoffEnergyBounds

/-!
# The quantitative face-energy comparison

For the intended scales, the inner face integral retains at least a
quarter of the product of the first mass squared and the remaining
tensor square mass. The numerical moment condition is discharged.
-/

namespace Erdos4b.FGKMT

noncomputable section

def dimensionFaceEnergy (k j : ℕ) : ℝ :=
  cutoffCubeIntegral (fun t => dimensionProfileFactor k t ^ 2)
    (fun s => dimensionFaceCutoff k s ^ 2) j 0

theorem dimensionFaceEnergy_bounds {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    (hj : j ≤ k) :
    dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j / 4 ≤ dimensionFaceEnergy k j ∧
      dimensionFaceEnergy k j ≤ dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j := by
  obtain ⟨C, _hC, hcutoff⟩ := exists_dimensionFaceCutoff_sq_bounded
  have hG : Continuous (fun t : ℝ => dimensionProfileFactor k t ^ 2) :=
    (dimensionProfileFactor_contDiff k (n := 1)).continuous.pow 2
  have hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ dimensionProfileFactor k t ^ 2 :=
    fun t _ht => sq_nonneg _
  have hupper := cutoffCubeIntegral_upper_constant hG hG0 (hcutoff k)
    (fun s hs => (dimensionFaceCutoff_sq_bounds hk hlog hs).2) j
  have hlower := cutoffCubeIntegral_lower_linear
    (α := dimensionProfileFirstMass k ^ 2) (β := (5 / 4) * dimensionProfileFirstMass k ^ 2)
    hG hG0 (hcutoff k) (fun s hs => by
      calc
        _ = dimensionProfileFirstMass k ^ 2 * (1 - (5 / 4) * s) := by ring
        _ ≤ _ := (dimensionFaceCutoff_sq_bounds hk hlog hs).1) j
  change dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ j -
    (5 / 4) * dimensionProfileFirstMass k ^ 2 * (j : ℝ) *
      (∫ t in (0 : ℝ)..1, t * dimensionProfileFactor k t ^ 2) * dimensionProfileMass k ^ (j - 1) ≤
    dimensionFaceEnergy k j at hlower
  refine ⟨?_, hupper⟩
  cases j with
  | zero =>
      simp only [Nat.cast_zero, pow_zero, mul_zero, zero_mul, sub_zero, mul_one] at hlower ⊢
      nlinarith [sq_nonneg (dimensionProfileFirstMass k)]
  | succ j =>
      have ha := (dimensionProfileMass_pos hk hlog).le
      have hm := dimensionProfile_firstMoment_condition hk hlog hj
      have hscale := mul_le_mul_of_nonneg_right hm
        (mul_nonneg (sq_nonneg (dimensionProfileFirstMass k)) (pow_nonneg ha j))
      simp only [Nat.add_sub_cancel] at hlower
      rw [pow_succ (dimensionProfileMass k) j] at hlower ⊢
      nlinarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionFaceEnergy_bounds

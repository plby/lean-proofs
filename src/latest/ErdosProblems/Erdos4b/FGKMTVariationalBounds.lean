/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceEnergy
import ErdosProblems.Erdos4b.FGKMTDimensionMass

/-!
# The logarithmic variational amplification

The ratio of the face energy to the full energy is bounded above and
below by absolute multiples of `log k / k`, for the actual scales.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem dimensionFaceEnergy_pos {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    (hj : j ≤ k) : 0 < dimensionFaceEnergy k j := by
  have hA := dimensionProfileFirstMass_pos hk hlog
  have hM := dimensionProfileMass_pos hk hlog
  exact lt_of_lt_of_le (by positivity) (dimensionFaceEnergy_bounds hk hlog hj).1

theorem dimensionProfile_variational_ratio_bounds {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    Real.log k / (16 * (k : ℝ)) ≤ dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k ∧
      dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k ≤ 6 * Real.log k / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hA := dimensionProfileFirstMass_pos hk hlog
  have hM := dimensionProfileMass_pos hk hlog
  have hI := dimensionProfileEnergy_bounds hk hlog (le_refl k)
  have hI0 := dimensionProfileEnergy_pos hk hlog (le_refl k)
  have hJ := dimensionFaceEnergy_bounds hk hlog (Nat.sub_le k 1)
  have hJ0 := dimensionFaceEnergy_pos hk hlog (Nat.sub_le k 1)
  have hratio := dimensionProfile_mass_ratio_bounds hk hlog
  have hpow : dimensionProfileMass k ^ k =
      dimensionProfileMass k ^ (k - 1) * dimensionProfileMass k := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using
      pow_succ (dimensionProfileMass k) (k - 1)
  have hpow0 := pow_ne_zero (k - 1) hM.ne'
  constructor
  · calc
      _ = (Real.log k / (4 * (k : ℝ))) / 4 := by ring
      _ ≤ (dimensionProfileFirstMass k ^ 2 / dimensionProfileMass k) / 4 :=
        div_le_div_of_nonneg_right hratio.1 (by norm_num)
      _ = (dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ (k - 1) / 4) /
          dimensionProfileMass k ^ k := by
        rw [hpow]
        field_simp [hM.ne', hpow0]
      _ ≤ dimensionFaceEnergy k (k - 1) / dimensionProfileMass k ^ k :=
        div_le_div_of_nonneg_right hJ.1 (pow_nonneg hM.le k)
      _ ≤ _ := div_le_div_of_nonneg_left hJ0.le hI0 hI.2
  · calc
      _ ≤ (dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ (k - 1)) /
          dimensionProfileEnergy k k := div_le_div_of_nonneg_right hJ.2 hI0.le
      _ ≤ (dimensionProfileFirstMass k ^ 2 * dimensionProfileMass k ^ (k - 1)) /
          (dimensionProfileMass k ^ k / 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hI.1
      _ = 3 * (dimensionProfileFirstMass k ^ 2 / dimensionProfileMass k) := by
        rw [hpow]
        field_simp [hM.ne', hpow0]
      _ ≤ 3 * (2 * Real.log k / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio.2 (by norm_num)
      _ = _ := by ring

theorem dimensionProfile_variational_gain {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    Real.log k / 16 ≤
      (k : ℝ) * dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  calc
    _ = (k : ℝ) * (Real.log k / (16 * (k : ℝ))) := by field_simp
    _ ≤ (k : ℝ) * (dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k) :=
      mul_le_mul_of_nonneg_left (dimensionProfile_variational_ratio_bounds hk hlog).1 hkR.le
    _ = _ := by ring

theorem eventually_dimensionProfile_variational_bounds :
    ∀ᶠ k : ℕ in atTop,
      0 < dimensionProfileEnergy k k ∧ 0 < dimensionFaceEnergy k (k - 1) ∧
      Real.log k / (16 * (k : ℝ)) ≤ dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k ∧
      dimensionFaceEnergy k (k - 1) / dimensionProfileEnergy k k ≤ 6 * Real.log k / (k : ℝ) := by
  filter_upwards [eventually_profile_scale_hypotheses] with k hk
  exact ⟨dimensionProfileEnergy_pos hk.1 hk.2 (le_refl k),
    dimensionFaceEnergy_pos hk.1 hk.2 (Nat.sub_le k 1),
    dimensionProfile_variational_ratio_bounds hk.1 hk.2⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionProfile_variational_gain
#print axioms Erdos4b.FGKMT.eventually_dimensionProfile_variational_bounds

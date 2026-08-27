/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceCutoff

/-!
# The first-mass amplification at the intended scales

The first mass is between `1/(2k)` and `1/k`; the square mass is
between `1/(2T)` and `1/T`. Their ratio gives the logarithmic gain.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem dimensionProfileFirstMass_eq {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    dimensionProfileFirstMass k =
      ∫ t in (0 : ℝ)..sieveProfileWidth k, dimensionProfileFactor k t := by
  have hb := profile_scales_bounds hk hlog
  simpa only [Nat.zero_add, pow_one, dimensionProfileFirstMass, dimensionProfileFactor] using
    sieveFactor_pow_integral_eq hb.2.1 (by linarith [hb.2.2.1]) (sieveProfileScale k) 0

theorem dimensionProfileFirstMass_bounds {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    1 / (2 * (k : ℝ)) ≤ dimensionProfileFirstMass k ∧
      dimensionProfileFirstMass k ≤ 1 / (k : ℝ) := by
  have hb := profile_scales_bounds hk hlog
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le hb.1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < Real.log k := by linarith
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hTUge : Real.sqrt k ≤ (9 / 10) * (sieveProfileScale k * sieveProfileWidth k) := by
    rw [sieveProfileScale_mul_width hk]
    nlinarith [mul_nonneg hs.le (show 0 ≤ (9 / 10) * Real.log k - 1 by linarith)]
  have harg : Real.sqrt k ≤
      1 + sieveProfileScale k * ((9 / 10) * sieveProfileWidth k) := by nlinarith
  have hloglower := Real.log_le_log hs harg
  rw [Real.log_sqrt hkR.le] at hloglower
  have hmass := sieveFactor_mass_bounds hT hb.2.1
  rw [dimensionProfileFirstMass_eq hk hlog]
  constructor
  · calc
      _ = (Real.log k / 2) / sieveProfileScale k := by
        unfold sieveProfileScale
        field_simp [hkR.ne', hL.ne']
      _ ≤ Real.log (1 + sieveProfileScale k * ((9 / 10) * sieveProfileWidth k)) /
          sieveProfileScale k := div_le_div_of_nonneg_right hloglower hT.le
      _ ≤ _ := hmass.1
  · calc
      _ ≤ Real.log (1 + sieveProfileScale k * sieveProfileWidth k) / sieveProfileScale k := hmass.2
      _ ≤ ((11 / 20) * Real.log k) / sieveProfileScale k :=
        div_le_div_of_nonneg_right (profile_scales_log_bound hk hlog) hT.le
      _ = (11 / 20) / (k : ℝ) := by
        unfold sieveProfileScale
        field_simp [hkR.ne', hL.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hkR.le

theorem dimensionProfileFirstMass_pos {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    0 < dimensionProfileFirstMass k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity)
    (dimensionProfileFirstMass_bounds hk hlog).1

theorem dimensionProfileMass_le_inv {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    dimensionProfileMass k ≤ 1 / sieveProfileScale k := by
  have hb := profile_scales_bounds hk hlog
  unfold dimensionProfileMass dimensionProfileFactor
  rw [sieveFactor_sq_unit_mass_eq hb.2.1 (by linarith [hb.2.2.1])]
  exact sieveFactor_sq_mass_le_inv (zero_lt_one.trans_le hb.1) hb.2.1

theorem dimensionProfile_mass_ratio_bounds {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    Real.log k / (4 * (k : ℝ)) ≤ dimensionProfileFirstMass k ^ 2 / dimensionProfileMass k ∧
      dimensionProfileFirstMass k ^ 2 / dimensionProfileMass k ≤ 2 * Real.log k / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < Real.log k := by linarith
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hA := dimensionProfileFirstMass_bounds hk hlog
  have hM := dimensionProfileMass_pos hk hlog
  constructor
  · calc
      _ = (1 / (2 * (k : ℝ))) ^ 2 / (1 / sieveProfileScale k) := by
        unfold sieveProfileScale
        field_simp [hkR.ne', hL.ne']
        ring
      _ ≤ (1 / (2 * (k : ℝ))) ^ 2 / dimensionProfileMass k :=
        div_le_div_of_nonneg_left (sq_nonneg _) hM (dimensionProfileMass_le_inv hk hlog)
      _ ≤ _ := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hA.1 2) hM.le
  · calc
      _ ≤ (1 / (k : ℝ)) ^ 2 / dimensionProfileMass k :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (dimensionProfileFirstMass_nonneg k) hA.2 2) hM.le
      _ ≤ (1 / (k : ℝ)) ^ 2 / (1 / (2 * sieveProfileScale k)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (dimensionProfileMass_ge_half_inv hk hlog)
      _ = _ := by
        unfold sieveProfileScale
        field_simp [hkR.ne', hL.ne']

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionProfileFirstMass_bounds
#print axioms Erdos4b.FGKMT.dimensionProfile_mass_ratio_bounds

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileScales
import ErdosProblems.Erdos4b.FGKMTProfileEnergy

/-!
# Energy of the actual dimension-dependent profile

The first-moment condition is now proved for the intended scales.
No asymptotic analytic estimate is assumed by these energy bounds.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def dimensionProfileFactor (k : ℕ) : ℝ → ℝ :=
  sieveFactor (sieveProfileScale k) (sieveProfileWidth k)

def dimensionProfileMass (k : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, dimensionProfileFactor k t ^ 2

def dimensionProfileEnergy (k j : ℕ) : ℝ :=
  cutoffCubeIntegral (fun t => dimensionProfileFactor k t ^ 2) (fun s => sieveCutoff s ^ 2) j 0

theorem dimensionProfileMass_pos {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    0 < dimensionProfileMass k := by
  have hb := profile_scales_bounds hk hlog
  exact sieveFactor_sq_unit_mass_pos (zero_le_one.trans hb.1) hb.2.1 (by linarith [hb.2.2.1])

theorem dimensionProfileMass_ge_half_inv {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    1 / (2 * sieveProfileScale k) ≤ dimensionProfileMass k := by
  have hb := profile_scales_bounds hk hlog
  unfold dimensionProfileMass dimensionProfileFactor
  rw [sieveFactor_sq_unit_mass_eq hb.2.1 (by linarith [hb.2.2.1])]
  exact sieveFactor_sq_mass_ge_half_inv (zero_lt_one.trans_le hb.1) hb.2.1 (by linarith [hb.2.2.2])

theorem dimensionProfileEnergy_bounds {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    (hj : j ≤ k) :
    dimensionProfileMass k ^ j / 3 ≤ dimensionProfileEnergy k j ∧
      dimensionProfileEnergy k j ≤ dimensionProfileMass k ^ j := by
  have hb := profile_scales_bounds hk hlog
  exact sieveProfile_energy_bounds (zero_lt_one.trans_le hb.1) hb.2.1 (by linarith [hb.2.2.1]) j
    (profile_scales_moment_condition hk hlog hj)

theorem dimensionProfile_firstMoment_condition {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (j : ℝ) * (∫ t in (0 : ℝ)..1, t * dimensionProfileFactor k t ^ 2) ≤
      (3 / 5) * dimensionProfileMass k := by
  have hb := profile_scales_bounds hk hlog
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le hb.1
  have hU1 : sieveProfileWidth k ≤ 1 := by linarith [hb.2.2.1]
  have hmass : ((9 / 10) * sieveProfileWidth k) /
      (1 + sieveProfileScale k * ((9 / 10) * sieveProfileWidth k)) ≤ dimensionProfileMass k := by
    unfold dimensionProfileMass dimensionProfileFactor
    rw [sieveFactor_sq_unit_mass_eq hb.2.1 hU1]
    exact sieveFactor_sq_mass_lower hT.le hb.2.1
  calc
    _ ≤ (j : ℝ) * (Real.log (1 + sieveProfileScale k * sieveProfileWidth k) /
        sieveProfileScale k ^ 2) :=
      mul_le_mul_of_nonneg_left (sieveFactor_firstMoment_unit_bound hT hb.2.1 hU1)
        (Nat.cast_nonneg j)
    _ ≤ _ := (profile_scales_moment_condition hk hlog hj).trans
      (mul_le_mul_of_nonneg_left hmass (by norm_num))

theorem dimensionProfileEnergy_pos {k j : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    (hj : j ≤ k) : 0 < dimensionProfileEnergy k j :=
  lt_of_lt_of_le (div_pos (pow_pos (dimensionProfileMass_pos hk hlog) j) (by norm_num))
    (dimensionProfileEnergy_bounds hk hlog hj).1

theorem dimensionProfileEnergy_explicit_lower {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (1 / (2 * sieveProfileScale k)) ^ j / 3 ≤ dimensionProfileEnergy k j := by
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (2 * sieveProfileScale k))
    (dimensionProfileMass_ge_half_inv hk hlog) j
  exact (div_le_div_of_nonneg_right hpow (by norm_num)).trans
    (dimensionProfileEnergy_bounds hk hlog hj).1

theorem eventually_dimensionProfileEnergy_bounds :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, j ≤ k →
      0 < dimensionProfileEnergy k j ∧
      (1 / (2 * sieveProfileScale k)) ^ j / 3 ≤ dimensionProfileEnergy k j ∧
      dimensionProfileMass k ^ j / 3 ≤ dimensionProfileEnergy k j ∧
      dimensionProfileEnergy k j ≤ dimensionProfileMass k ^ j := by
  filter_upwards [eventually_profile_scale_hypotheses] with k hk
  intro j hj
  exact ⟨dimensionProfileEnergy_pos hk.1 hk.2 hj,
    dimensionProfileEnergy_explicit_lower hk.1 hk.2 hj, dimensionProfileEnergy_bounds hk.1 hk.2 hj⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_dimensionProfileEnergy_bounds

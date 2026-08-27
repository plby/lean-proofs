/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionMass

/-!
# The long-cutoff factor controlling changes of the sieve profile

Its support extends to two, not one. The mass comparisons therefore
retain the entire interval `[0,2]`. The short-factor derivative is
bounded pointwise by an absolute multiple of `T` times this factor.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped Topology

def dimensionLongFactor (k : ℕ) : ℝ → ℝ := sieveFactor (sieveProfileScale k) 2

def dimensionLongMass (k : ℕ) : ℝ := ∫ t in (0 : ℝ)..2, dimensionLongFactor k t ^ 2

def dimensionLongFirstMass (k : ℕ) : ℝ := ∫ t in (0 : ℝ)..2, dimensionLongFactor k t

theorem dimensionLongFactor_contDiff (k : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (dimensionLongFactor k) := sieveFactor_contDiff _ _

theorem dimensionLongFactor_nonneg (k : ℕ) (t : ℝ) : 0 ≤ dimensionLongFactor k t :=
  sieveFactor_nonneg _ _ _

theorem dimensionLongFactor_zero {t : ℝ} (ht : 2 ≤ t) (k : ℕ) :
    dimensionLongFactor k t = 0 := sieveFactor_zero_of_ge (by norm_num) ht _

theorem sieveFactor_mono_width {U V t : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (ht : 0 ≤ t) (T : ℝ) : sieveFactor T U t ≤ sieveFactor T V t := by
  unfold sieveFactor
  apply div_le_div_of_nonneg_right _ (profileDenominator_pos _).le
  exact sieveCutoff_antitone (div_le_div_of_nonneg_left ht hU hUV)

theorem dimensionProfileFactor_le_long {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {t : ℝ} (ht : 0 ≤ t) :
    dimensionProfileFactor k t ≤ dimensionLongFactor k t := by
  have hb := profile_scales_bounds hk hlog
  exact sieveFactor_mono_width hb.2.1 (by linarith [hb.2.2.1]) ht _

theorem dimensionLongMass_le_twice {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    dimensionLongMass k ≤ 2 * dimensionProfileMass k := by
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  calc
    _ ≤ 1 / sieveProfileScale k := sieveFactor_sq_mass_le_inv hT (by norm_num)
    _ = 2 * (1 / (2 * sieveProfileScale k)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dimensionProfileMass_ge_half_inv hk hlog) (by norm_num)

theorem dimensionLongFirstMass_le_two_div {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) : dimensionLongFirstMass k ≤ 2 / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hklarge : 10000 ≤ (k : ℝ) := by linarith [Real.log_le_sub_one_of_pos hkR]
  have hlogsmall := log_le_fiftieth_of_large hklarge
  have hlog0 : 0 < Real.log k := by linarith
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have harg : 1 + sieveProfileScale k * 2 ≤ (k : ℝ) ^ 2 := by
    dsimp only [sieveProfileScale]
    nlinarith
  have hl : Real.log (1 + sieveProfileScale k * 2) ≤ 2 * Real.log k := by
    have h := Real.log_le_log (by positivity : 0 < 1 + sieveProfileScale k * 2) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ Real.log (1 + sieveProfileScale k * 2) / sieveProfileScale k :=
      (sieveFactor_mass_bounds hT (by norm_num : (0 : ℝ) < 2)).2
    _ ≤ (2 * Real.log k) / sieveProfileScale k := div_le_div_of_nonneg_right hl hT.le
    _ = _ := by unfold sieveProfileScale; field_simp

theorem dimensionLongFirstMass_le_four {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    dimensionLongFirstMass k ≤ 4 * dimensionProfileFirstMass k := by
  calc
    _ ≤ 2 / (k : ℝ) := dimensionLongFirstMass_le_two_div hk hlog
    _ = 4 * (1 / (2 * (k : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dimensionProfileFirstMass_bounds hk hlog).1 (by norm_num)

theorem sieveFactor_deriv_zero_of_gt {U t : ℝ} (hU : 0 < U) (ht : U < t) (T : ℝ) :
    deriv (sieveFactor T U) t = 0 := by
  have h : HasDerivAt (sieveFactor T U) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact sieveFactor_zero_of_ge hU hs.le T)
  exact h.deriv

theorem dimensionProfileFactor_deriv_le_long {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {K : ℝ} (hψ : BoundedCutoff sieveCutoff K)
    {t : ℝ} (ht : 0 ≤ t) :
    |deriv (dimensionProfileFactor k) t| ≤
      (K + 1) * sieveProfileScale k * dimensionLongFactor k t := by
  have hb := profile_scales_bounds hk hlog
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le hb.1
  have hK := hψ.constant_nonneg
  by_cases ht1 : t ≤ 1
  · have hD : dimensionLongFactor k t = 1 / (1 + sieveProfileScale k * t) :=
      sieveFactor_eq_inv hT.le (by norm_num) ht (by linarith)
    have hinv : 1 / sieveProfileWidth k ≤ sieveProfileScale k :=
      (div_le_iff₀ hb.2.1).mpr (by linarith [hb.2.2.2])
    have hcost : K / sieveProfileWidth k + sieveProfileScale k ≤
        (K + 1) * sieveProfileScale k := by
      calc
        _ = K * (1 / sieveProfileWidth k) + sieveProfileScale k := by ring
        _ ≤ K * sieveProfileScale k + sieveProfileScale k :=
          add_le_add (mul_le_mul_of_nonneg_left hinv hK) le_rfl
        _ = _ := by ring
    calc
      _ ≤ (K / sieveProfileWidth k + sieveProfileScale k) /
          (1 + sieveProfileScale k * t) := sieveFactor_deriv_decay hT.le hb.2.1 ht hψ
      _ ≤ ((K + 1) * sieveProfileScale k) / (1 + sieveProfileScale k * t) :=
        div_le_div_of_nonneg_right hcost (by positivity)
      _ = _ := by rw [hD]; ring
  · have hz : deriv (dimensionProfileFactor k) t = 0 :=
      sieveFactor_deriv_zero_of_gt hb.2.1 (by linarith [hb.2.2.1]) _
    rw [hz, abs_zero]
    exact mul_nonneg (by positivity) (dimensionLongFactor_nonneg k t)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionLongMass_le_twice
#print axioms Erdos4b.FGKMT.dimensionLongFirstMass_le_four
#print axioms Erdos4b.FGKMT.dimensionProfileFactor_deriv_le_long

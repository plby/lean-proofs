import ErdosProblems.Erdos941.SiegelNearOne
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Adapted from the existing `Erdos1141/SiegelLowerBound.lean` proof.

# Siegel's lower bound with an arbitrary positive exponent
-/

namespace Erdos941.Analytic

open Filter
open BoundedGaps.Maynard

theorem eventually_rpow_neg_le_log_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ (-δ) ≤ 1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3) := by
  have hlittle := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound (show (0 : ℝ) < 1 / (2 ^ 24 : ℝ) by positivity)
  filter_upwards [hbound, eventually_ge_atTop 3] with q hbound hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hpow : 0 < (q : ℝ) ^ δ := Real.rpow_pos_of_pos hq0 _
  simp only [Function.comp_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_pos (Real.rpow_pos_of_pos hlog _), abs_of_pos hpow] at hbound
  have hlogpow : Real.log (q : ℝ) ^ (3 : ℝ) = Real.log (q : ℝ) ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hlogpow] at hbound
  have hdom : (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3 ≤ (q : ℝ) ^ δ := by
    nlinarith only [hbound]
  have hrecip := one_div_le_one_div_of_le
    (by positivity : 0 < (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3) hdom
  simpa only [Real.rpow_neg hq0.le, one_div] using hrecip

theorem eventually_quadratic_LFunction_one_re_ge_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsQuadratic →
        (q : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := by
  obtain ⟨c, hc, hzeroFree⟩ := exists_siegelRealCharacterZeroFree (δ / 2) (half_pos hδ)
  have hpowTendsto : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(δ / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (half_pos hδ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hpowTendsto.eventually (eventually_lt_nhds (show 0 < c / 8 by positivity))
  filter_upwards [eventually_rpow_neg_le_log_threshold hδ, hsmall, eventually_gt_atTop 1]
    with q hlog hsmall hq
  intro _ χ hχ1 hχ
  by_contra hnot
  have hv : (DirichletCharacter.LFunction χ (1 : ℂ)).re < (q : ℝ) ^ (-δ) := lt_of_not_ge hnot
  obtain ⟨β, hβlower, _hβupper, hβzero⟩ :=
    exists_real_zero_of_LFunction_one_re_lt hq χ hχ1 hχ.sq_eq_one (hv.trans_le hlog)
  have hq0 : (0 : ℝ) < q := by positivity
  have hsq : (q : ℝ) ^ (-δ) = ((q : ℝ) ^ (-(δ / 2))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have ha : 0 < (q : ℝ) ^ (-(δ / 2)) := Real.rpow_pos_of_pos hq0 _
  have hgap : 8 * (DirichletCharacter.LFunction χ (1 : ℂ)).re < c * (q : ℝ) ^ (-(δ / 2)) := by
    rw [hsq] at hv
    nlinarith only [hv, hsmall, ha]
  have hβ : 1 - c * (q : ℝ) ^ (-(δ / 2)) < β := by linarith only [hgap, hβlower]
  exact (hzeroFree q χ hχ1 hχ.sq_eq_one β hβ) hβzero

/-- Uniformity includes bounded conductors, which is essential when the sphere
radius has arbitrarily large square factors. -/
theorem exists_quadratic_LFunction_one_re_lower {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ.IsQuadratic →
        c * (q : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := by
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp (eventually_quadratic_LFunction_one_re_ge_rpow hδ)
  let Q := max Q₀ 3
  have hQ3 : (3 : ℝ) ≤ Q := by exact_mod_cast (le_max_right Q₀ 3)
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  let c : ℝ := min 1 (1 / (8192 * Real.sqrt (Q : ℝ) * Real.log (Q : ℝ) ^ 2))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro q _ χ hχ1 hχ
  have hq3 : 3 ≤ q := three_le_modulus_of_character_ne_one χ hχ1
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hqpos : (0 : ℝ) < q := by linarith
  by_cases hqQ : Q ≤ q
  · have hlarge := hQ₀ q ((le_max_left Q₀ 3).trans hqQ) χ hχ1 hχ
    calc
      c * (q : ℝ) ^ (-δ) ≤ 1 * (q : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hqpos.le _)
      _ ≤ _ := by simpa only [one_mul] using hlarge
  · have hqleQ : (q : ℝ) ≤ Q := by exact_mod_cast (by omega : q ≤ Q)
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
    have hden : 8192 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤
        8192 * Real.sqrt (Q : ℝ) * Real.log (Q : ℝ) ^ 2 := by
      gcongr
    have hrecip := one_div_le_one_div_of_le
      (by positivity : 0 < 8192 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ^ 2) hden
    have heff := (Complex.le_def.mp
      (effectiveQuadraticLValueLowerBound (by omega : 1 < q) χ hχ1 hχ.sq_eq_one)).1
    change 1 / (8192 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ^ 2) ≤
      (DirichletCharacter.LFunction χ (1 : ℂ)).re at heff
    have hpow : (q : ℝ) ^ (-δ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc
      c * (q : ℝ) ^ (-δ) ≤ c := mul_le_of_le_one_right hc.le hpow
      _ ≤ 1 / (8192 * Real.sqrt (Q : ℝ) * Real.log (Q : ℝ) ^ 2) := min_le_right _ _
      _ ≤ _ := hrecip.trans heff

end Erdos941.Analytic

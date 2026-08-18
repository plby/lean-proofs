/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.PrimeWeightedInterval
import ErdosProblems.Erdos49.Analytic

/-!
# Logarithmic scales for the high-index argument

The reciprocal estimate near `sqrt n` uses the relatively long cutoff
`log^40`; the inverse-square estimate uses `log^7` and separates the far
range at `log^8`.  Keeping these scales distinct is what makes the two
parts of Granville--Ramaré's argument meet quantitatively.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace HighIndexCutoffs

noncomputable section

def logPowerCutoff (e y : ℕ) : ℕ :=
  Nat.floor (Real.log (y : ℝ) ^ e) + 1

def nearVaughanCutoff (y : ℕ) : ℕ := logPowerCutoff 40 y

def farVaughanCutoff (y : ℕ) : ℕ := logPowerCutoff 7 y

def farSeparation (y : ℕ) : ℕ := logPowerCutoff 8 y

lemma logPowerCutoff_pos (e y : ℕ) : 0 < logPowerCutoff e y := by
  unfold logPowerCutoff
  omega

lemma logPowerCutoff_real_bounds {e y : ℕ} (hy : 1 ≤ y) :
    Real.log (y : ℝ) ^ e < (logPowerCutoff e y : ℝ) ∧
      (logPowerCutoff e y : ℝ) ≤ Real.log (y : ℝ) ^ e + 1 := by
  have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  constructor
  · simpa only [logPowerCutoff, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.log (y : ℝ) ^ e)
  · unfold logPowerCutoff
    push_cast
    gcongr
    exact Nat.floor_le (pow_nonneg hlog0 e)

lemma logPowerCutoff_le_two_log_pow {e y : ℕ} (hy : 4 ≤ y) :
    (logPowerCutoff e y : ℝ) ≤ 2 * Real.log (y : ℝ) ^ e := by
  have hb := (logPowerCutoff_real_bounds (e := e) (show 1 ≤ y by omega)).2
  have hlog : 1 ≤ Real.log (y : ℝ) :=
    BoundedGaps.Maynard.one_le_log_natCast hy
  have hone : (1 : ℝ) ≤ Real.log (y : ℝ) ^ e := one_le_pow₀ hlog
  linarith

lemma tendsto_logPowerCutoff_atTop (e : ℕ) (he : 0 < e) :
    Tendsto (logPowerCutoff e) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ e) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) he.ne').comp hlogTop
  have hevent : ∀ᶠ y : ℕ in atTop, (B : ℝ) < Real.log (y : ℝ) ^ e :=
    hpowTop.eventually (eventually_gt_atTop (B : ℝ))
  rcases (hevent.and (eventually_ge_atTop 1)).exists_forall_of_atTop with
    ⟨Y, hY⟩
  refine ⟨Y, fun y hy ↦ ?_⟩
  have hb := (logPowerCutoff_real_bounds (e := e) (hY y hy).2).1
  exact Nat.le_of_lt (by exact_mod_cast (hY y hy).1.trans hb)

lemma tendsto_nearVaughanCutoff_atTop : Tendsto nearVaughanCutoff atTop atTop :=
  tendsto_logPowerCutoff_atTop 40 (by omega)

lemma tendsto_farVaughanCutoff_atTop : Tendsto farVaughanCutoff atTop atTop :=
  tendsto_logPowerCutoff_atTop 7 (by omega)

lemma tendsto_farSeparation_atTop : Tendsto farSeparation atTop atTop :=
  tendsto_logPowerCutoff_atTop 8 (by omega)

/-- The logarithm of any fixed log-power cutoff is smaller than the fourth
root of `log y`.  This sharper estimate, rather than the coarse bound by
`log y`, is needed when the dyadic fourth Vaughan term is normalized. -/
theorem eventually_log_logPowerCutoff_add_three_le (e : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      Real.log (logPowerCutoff e y : ℝ) + 3 ≤
        Real.log (y : ℝ) ^ (1 / 4 : ℝ) := by
  let G : ℕ → ℝ := fun y ↦ Real.log (y : ℝ)
  have hGTop : Tendsto G atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio : Tendsto (fun t : ℝ ↦
      (Real.log (2 * t ^ e) + 3) / t ^ (1 / 4 : ℝ)) atTop (nhds 0) := by
    have hlog : (fun t : ℝ ↦ Real.log (2 * t ^ e) + 3) =O[atTop]
        fun t ↦ Real.log t := by
      have hevent : ∀ᶠ t : ℝ in atTop,
          Real.log (2 * t ^ e) + 3 ≤
            (e + 5 : ℝ) * Real.log t := by
        filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
        have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
        have hlogt : 1 ≤ Real.log t := by
          calc
            (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
            _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) ht
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (pow_ne_zero e ht0.ne'), Real.log_pow]
        have hlog2 : Real.log 2 ≤ Real.log t :=
          Real.log_le_log (by norm_num) (by
            exact (show (2 : ℝ) ≤ Real.exp 1 by
              exact Real.exp_one_gt_two.le).trans ht)
        push_cast
        nlinarith
      refine Asymptotics.IsBigO.of_bound (e + 5) ?_
      filter_upwards [hevent, eventually_ge_atTop (Real.exp 1)] with t ht ht1
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by
          exact (show (1 : ℝ) ≤ Real.exp 1 by
            simpa using (Real.exp_pos 1).le).trans ht1))]
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht1
      have harg : 1 ≤ 2 * t ^ e := by
        have htone : 1 ≤ t :=
          (show (1 : ℝ) ≤ Real.exp 1 by
            simpa using (Real.exp_pos 1).le).trans ht1
        nlinarith [one_le_pow₀ (n := e) htone]
      have hleft : 0 ≤ Real.log (2 * t ^ e) + 3 := by
        linarith [Real.log_nonneg harg]
      rw [abs_of_nonneg hleft]
      exact ht
    have hlittle : (fun t : ℝ ↦ Real.log t) =o[atTop]
        fun t ↦ t ^ (1 / 4 : ℝ) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have hsmall := hlog.trans_isLittleO hlittle
    exact hsmall.tendsto_div_nhds_zero
  have hratioNat := hratio.comp hGTop
  have hsmall : ∀ᶠ y : ℕ in atTop,
      (Real.log (2 * G y ^ e) + 3) / G y ^ (1 / 4 : ℝ) ≤ 1 :=
    hratioNat.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 4] with y hsmall hy
  have hG : 1 ≤ G y := by
    simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
  have hden : 0 < G y ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hG) _
  have hcut := logPowerCutoff_le_two_log_pow (e := e) hy
  have hcutPos : (0 : ℝ) < logPowerCutoff e y := by
    exact_mod_cast logPowerCutoff_pos e y
  have hlogMono : Real.log (logPowerCutoff e y : ℝ) ≤
      Real.log (2 * G y ^ e) := by
    apply Real.log_le_log hcutPos
    simpa only [G] using hcut
  calc
    Real.log (logPowerCutoff e y : ℝ) + 3 ≤
        Real.log (2 * G y ^ e) + 3 := by linarith
    _ ≤ G y ^ (1 / 4 : ℝ) := (div_le_one hden).mp hsmall
    _ = Real.log (y : ℝ) ^ (1 / 4 : ℝ) := rfl

end

end HighIndexCutoffs
end Erdos378

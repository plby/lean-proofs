import ErdosProblems.Erdos4.FGKMTSharpRankin
import ErdosProblems.Erdos4.FGKMTOuterDensity

/-! A logarithmic Rankin parameter closes the Euler budget at the actual smoothness cutoff. -/

namespace Erdos4.FGKMT

open Filter

noncomputable def growingRankinDelta (x : ℕ) : ℝ :=
  20 * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)

theorem growingRandomEnd_tendsto : Tendsto growingRandomEnd atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [growingRandomStart_tendsto.eventually (eventually_ge_atTop N),
    eventually_growing_random_cutoff_logs] with x hN hcut
  exact hN.trans hcut.2.1

theorem eventually_growing_rankin_parameters :
    ∀ᶠ x : ℕ in atTop,
      0 < growingRankinDelta x ∧ growingRankinDelta x ≤ 1 / 2 ∧
      growingRankinDelta x * Real.log (x : ℝ) = 20 * Real.log (Real.log (x : ℝ)) ∧
      (growingRandomEnd x : ℝ) ^ growingRankinDelta x ≤
        Real.log (Real.log (x : ℝ)) ^ (1 / 5 : ℝ) ∧
      Real.log (Real.log (growingRandomEnd x : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
  filter_upwards [eventually_growing_outer_log_budget,
    eventually_growing_random_cutoff_logs] with x hlogs hcut
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hL1 : 1 ≤ L := hlogs.1
  have hl1 : 1 ≤ l := hlogs.2.1
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl1
  have hδpos : 0 < growingRankinDelta x := by
    change 0 < 20 * l / L
    positivity
  have hrootle : Real.sqrt L ≤ L := by
    have hs := Real.sq_sqrt hLpos.le
    nlinarith [sq_nonneg (Real.sqrt L - 1)]
  have hdom : 1000 * l ≤ Real.sqrt L := hlogs.2.2.1
  have hδhalf : growingRankinDelta x ≤ 1 / 2 := by
    change 20 * l / L ≤ 1 / 2
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hprod : growingRankinDelta x * L = 20 * l := by
    change (20 * l / L) * L = 20 * l
    exact div_mul_cancel₀ _ hLpos.ne'
  have hz2 : 2 ≤ growingRandomEnd x := hcut.1.trans hcut.2.1
  have hzpos : (0 : ℝ) < growingRandomEnd x := by exact_mod_cast (show 0 < growingRandomEnd x by omega)
  have hlogz : 0 < Real.log (growingRandomEnd x : ℝ) := Real.log_pos (by exact_mod_cast hz2)
  have hlogup : Real.log (growingRandomEnd x : ℝ) ≤ L := by
    have hscale : growingOuterScale x ≤ L := hlogs.2.2.2.2
    have hh := hcut.2.2.2.2.2
    linarith
  refine ⟨hδpos, hδhalf, hprod, ?_, Real.log_le_log hlogz hlogup⟩
  calc
    _ = Real.exp (Real.log (growingRandomEnd x : ℝ) * growingRankinDelta x) :=
      Real.rpow_def_of_pos hzpos _
    _ ≤ Real.exp ((growingOuterScale x / 100) * growingRankinDelta x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcut.2.2.2.2.2 hδpos.le)
    _ = Real.exp (Real.log l / 5) := by
      congr 1
      change ((L * Real.log l / l) / 100) * (20 * l / L) = Real.log l / 5
      field_simp [hLpos.ne', hlpos.ne'] <;> ring
    _ = l ^ (1 / 5 : ℝ) := by
      rw [Real.rpow_def_of_pos hlpos]
      congr 1
      ring

theorem eventually_growing_rankin_euler :
    ∀ᶠ x : ℕ in atTop,
      Erdos469.smoothRankinEulerProduct (growingRankinDelta x) (growingRandomEnd x) ≤
        Real.exp (10 * Real.log (Real.log (x : ℝ))) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hgrow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hloglog
  filter_upwards [growingRandomEnd_tendsto.eventually eventually_sharp_rankin_euler,
    eventually_growing_rankin_parameters,
    hloglog.eventually (eventually_ge_atTop 1), hgrow.eventually (eventually_ge_atTop 4)]
    with x heuler hpar hl hlarge
  let l := Real.log (Real.log (x : ℝ))
  change 1 ≤ l at hl
  change 4 ≤ l ^ (4 / 5 : ℝ) at hlarge
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hsmall : 4 * l ^ (1 / 5 : ℝ) ≤ l := by
    calc
      _ ≤ l ^ (4 / 5 : ℝ) * l ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hlpos.le _)
      _ = l := by rw [← Real.rpow_add hlpos]; norm_num
  apply (heuler _ hpar.1 hpar.2.1).trans
  apply Real.exp_le_exp.mpr
  have hpower := hpar.2.2.2.1
  have hlogbound := hpar.2.2.2.2
  change (growingRandomEnd x : ℝ) ^ growingRankinDelta x ≤ l ^ (1 / 5 : ℝ) at hpower
  change Real.log (Real.log (growingRandomEnd x : ℝ)) ≤ l at hlogbound
  change _ ≤ 10 * l
  linarith

end Erdos4.FGKMT

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceCompactPrimitive

/-!
# Smooth interval indicators with unchanged support endpoints

Pointwise convergence holds at all real points, including the endpoints.
The compact interval majorant also controls products of two such cutoffs.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff

def sourceIntervalIndicator (a b : ℝ) : ℝ → ℝ :=
  (Set.Ioo a b).indicator (fun _ ↦ 1)

def sourceSmoothInterval (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((n + 1 : ℝ) * (t - a)) *
    Real.smoothTransition ((n + 1 : ℝ) * (b - t))

theorem sourceIntervalIndicator_norm_le_one (a b t : ℝ) :
    ‖sourceIntervalIndicator a b t‖ ≤ 1 := by
  by_cases ht : t ∈ Set.Ioo a b <;> simp [sourceIntervalIndicator, ht]

theorem sourceIntervalIndicator_integrable (a b : ℝ) :
    Integrable (sourceIntervalIndicator a b) := by
  apply (integrableOn_const (μ := volume) (C := (1 : ℝ))
    (s := Set.Ioo a b) ?_).integrable_indicator measurableSet_Ioo
  exact (lt_of_le_of_lt (measure_mono Set.Ioo_subset_Icc_self)
    isCompact_Icc.measure_lt_top).ne

theorem sourceIntervalIndicator_pair_integrable (a b c d : ℝ) :
    Integrable (fun t ↦ sourceIntervalIndicator a b t * sourceIntervalIndicator c d t) :=
  (sourceIntervalIndicator_integrable a b).mul_bdd
    (sourceIntervalIndicator_integrable c d).aestronglyMeasurable
    (ae_of_all _ (sourceIntervalIndicator_norm_le_one c d))

theorem sourceSmoothInterval_smooth (a b : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (sourceSmoothInterval a b n) := by
  unfold sourceSmoothInterval
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem sourceSmoothInterval_nonneg (a b : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ sourceSmoothInterval a b n t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem sourceSmoothInterval_le_one (a b : ℝ) (n : ℕ) (t : ℝ) :
    sourceSmoothInterval a b n t ≤ 1 := by
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem sourceSmoothInterval_eq_zero_of_le {a b t : ℝ} (n : ℕ) (ht : t ≤ a) :
    sourceSmoothInterval a b n t = 0 := by
  unfold sourceSmoothInterval
  rw [Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
    (by positivity) (sub_nonpos.mpr ht)), zero_mul]

theorem sourceSmoothInterval_eq_zero_of_ge {a b t : ℝ} (n : ℕ) (ht : b ≤ t) :
    sourceSmoothInterval a b n t = 0 := by
  unfold sourceSmoothInterval
  rw [Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
    (by positivity) (sub_nonpos.mpr ht)), mul_zero]

theorem sourceSmoothInterval_eq_zero_of_not_mem {a b t : ℝ} (n : ℕ)
    (ht : t ∉ Set.Ioo a b) : sourceSmoothInterval a b n t = 0 := by
  have hh : t ≤ a ∨ b ≤ t := by simpa only [Set.mem_Ioo, not_and_or, not_lt] using ht
  exact hh.elim (sourceSmoothInterval_eq_zero_of_le n) (sourceSmoothInterval_eq_zero_of_ge n)

theorem sourceSmoothInterval_compact (a b : ℝ) (n : ℕ) :
    HasCompactSupport (sourceSmoothInterval a b n) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := b))
  intro t ht
  exact sourceSmoothInterval_eq_zero_of_not_mem n (fun hh ↦ ht ⟨hh.1.le, hh.2.le⟩)

theorem sourceSmoothInterval_pair_integrable (a b c d : ℝ) (n : ℕ) :
    Integrable (fun t ↦ sourceSmoothInterval a b n t * sourceSmoothInterval c d n t) :=
  ((sourceSmoothInterval_smooth a b n).continuous.mul
    (sourceSmoothInterval_smooth c d n).continuous).integrable_of_hasCompactSupport
      (sourceSmoothInterval_compact a b n).mul_right

theorem sourceSmoothInterval_norm_le_indicator (a b : ℝ) (n : ℕ) (t : ℝ) :
    ‖sourceSmoothInterval a b n t‖ ≤ (Set.Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ)) t := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceSmoothInterval_nonneg a b n t)]
  by_cases ht : t ∈ Set.Icc a b
  · rw [Set.indicator_of_mem ht]
    exact sourceSmoothInterval_le_one a b n t
  · rw [Set.indicator_of_notMem ht,
      sourceSmoothInterval_eq_zero_of_not_mem n (fun hh ↦ ht ⟨hh.1.le, hh.2.le⟩)]

theorem tendsto_sourceSmoothInterval (a b t : ℝ) :
    Tendsto (fun n : ℕ ↦ sourceSmoothInterval a b n t) atTop (𝓝 (sourceIntervalIndicator a b t)) := by
  by_cases ht : t ∈ Set.Ioo a b
  · have hn : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      exact tendsto_atTop_mono (fun n ↦ by linarith : (fun n : ℕ ↦ (n : ℝ)) ≤
        (fun n : ℕ ↦ (n + 1 : ℝ))) tendsto_natCast_atTop_atTop
    have hleft := (hn.atTop_mul_const (sub_pos.mpr ht.1)).eventually (eventually_ge_atTop 1)
    have hright := (hn.atTop_mul_const (sub_pos.mpr ht.2)).eventually (eventually_ge_atTop 1)
    apply tendsto_const_nhds.congr'
    filter_upwards [hleft, hright] with n hl hr
    simp only [sourceSmoothInterval, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hr, one_mul, sourceIntervalIndicator,
      Set.indicator_of_mem ht]
  · have heq : (fun n : ℕ ↦ sourceSmoothInterval a b n t) = fun _ ↦ (0 : ℝ) :=
      funext fun n ↦ sourceSmoothInterval_eq_zero_of_not_mem n ht
    rw [heq, sourceIntervalIndicator, Set.indicator_of_notMem ht]
    exact tendsto_const_nhds

theorem tendsto_integral_sourceSmoothInterval (a b : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ t : ℝ in Set.Ioi 0, sourceSmoothInterval a b n t) atTop
      (𝓝 (∫ t : ℝ in Set.Ioi 0, sourceIntervalIndicator a b t)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Set.Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ)))
  · intro n
    exact (sourceSmoothInterval_smooth a b n).continuous.aestronglyMeasurable
  · exact ((integrableOn_const (μ := volume) (C := (1 : ℝ)) (s := Set.Icc a b)
      isCompact_Icc.measure_lt_top.ne).integrable_indicator
      measurableSet_Icc).integrableOn
  · intro n
    exact ae_of_all _ (sourceSmoothInterval_norm_le_indicator a b n)
  · exact ae_of_all _ (tendsto_sourceSmoothInterval a b)

theorem tendsto_integral_sourceSmoothInterval_pair (a b c d : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ t : ℝ in Set.Ioi 0,
      sourceSmoothInterval a b n t * sourceSmoothInterval c d n t) atTop
      (𝓝 (∫ t : ℝ in Set.Ioi 0,
        sourceIntervalIndicator a b t * sourceIntervalIndicator c d t)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Set.Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ)))
  · intro n
    exact ((sourceSmoothInterval_smooth a b n).continuous.mul
      (sourceSmoothInterval_smooth c d n).continuous).aestronglyMeasurable
  · exact ((integrableOn_const (μ := volume) (C := (1 : ℝ)) (s := Set.Icc a b)
      isCompact_Icc.measure_lt_top.ne).integrable_indicator
      measurableSet_Icc).integrableOn
  · intro n
    apply ae_of_all _
    intro t
    rw [norm_mul]
    have hc : ‖sourceSmoothInterval c d n t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceSmoothInterval_nonneg c d n t)]
      exact sourceSmoothInterval_le_one c d n t
    exact (mul_le_of_le_one_right (norm_nonneg _) hc).trans
      (sourceSmoothInterval_norm_le_indicator a b n t)
  · exact ae_of_all _ fun t ↦ (tendsto_sourceSmoothInterval a b t).mul
      (tendsto_sourceSmoothInterval c d t)

end

end Erdos4b

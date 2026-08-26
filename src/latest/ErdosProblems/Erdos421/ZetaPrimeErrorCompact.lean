import ErdosProblems.Erdos421.ZetaPoleLogDerivative
import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniform pole-cancelled bounds at bounded imaginary height -/

namespace Erdos421

open Complex Set Metric

theorem exists_zetaPrimeError_bounded_height (T : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ β t : ℝ,
      |β - 1| ≤ η → |t| ≤ T →
      riemannZeta₁ ((β : ℂ) + t * I) ≠ 0 ∧ ‖zetaPrimeError ((β : ℂ) + t * I)‖ ≤ C := by
  let S : Set ℂ := ({1} : Set ℝ) ×ℂ Icc (-T) T
  have hS : IsCompact S := isCompact_singleton.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    differentiable_riemannZeta₁.continuous.isOpen_preimage _ isOpen_ne
  have hsub : S ⊆ {s : ℂ | riemannZeta₁ s ≠ 0} := by
    intro s hs
    have hre : s.re = 1 := hs.1
    exact riemannZeta₁_ne_zero_on_right (by rw [hre])
  obtain ⟨η, hη, hthick⟩ := hS.exists_cthickening_subset_open hU hsub
  have hc : IsCompact (cthickening η S) := hS.cthickening
  have hcont : ContinuousOn zetaPrimeError (cthickening η S) := by
    intro s hs
    exact (analyticAt_zetaPrimeError (hthick hs)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨η, hη, |C| + 1, by positivity, ?_⟩
  intro β t hβ ht
  have hz : (1 : ℂ) + t * I ∈ S := by
    change ((1 : ℂ) + t * I).re ∈ ({1} : Set ℝ) ∧
      ((1 : ℂ) + t * I).im ∈ Icc (-T) T
    simpa only [add_re, one_re, mul_I_re, ofReal_im, neg_zero, add_zero, mem_singleton_iff,
      add_im, one_im, mul_I_im, ofReal_re, zero_add, true_and, mem_Icc] using abs_le.mp ht
  have hd : dist ((β : ℂ) + t * I) ((1 : ℂ) + t * I) = |β - 1| := by
    rw [dist_eq_norm, add_sub_add_right_eq_sub, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hmem : (β : ℂ) + t * I ∈ cthickening η S :=
    closedBall_subset_cthickening hz η (by rwa [mem_closedBall, hd])
  refine ⟨hthick hmem, (hC _ hmem).trans ?_⟩
  linarith [le_abs_self C]

end Erdos421

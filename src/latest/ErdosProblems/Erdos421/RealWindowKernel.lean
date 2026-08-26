import ErdosProblems.Erdos421.OneSidedSchwartzWindow
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The real smooth kernel underlying the arithmetic windows -/

namespace Erdos421

open MeasureTheory
open scoped SchwartzMap

noncomputable def oneSidedRealWindow : 𝓢(ℝ, ℝ) :=
  (oneSidedBump.hasCompactSupport_normed (μ := volume)).toSchwartzMap
    oneSidedBump.contDiff_normed

theorem oneSidedRealWindow_complex (t : ℝ) :
    (oneSidedRealWindow t : ℂ) = oneSidedSchwartzWindow t := rfl

theorem oneSidedRealWindow_nonneg (t : ℝ) : 0 ≤ oneSidedRealWindow t :=
  oneSidedBump.nonneg_normed t

theorem oneSidedRealWindow_integral : (∫ t : ℝ, oneSidedRealWindow t) = 1 := by
  exact oneSidedBump.integral_normed

theorem oneSidedRealWindow_nonzero {t : ℝ} (ht : oneSidedRealWindow t ≠ 0) :
    -1 < t ∧ t < 0 := by
  apply oneSidedSchwartzWindow_nonzero
  rw [← oneSidedRealWindow_complex]
  exact_mod_cast ht

theorem oneSidedRealWindow_deriv_continuous : Continuous (deriv (oneSidedRealWindow : ℝ → ℝ)) :=
  (oneSidedRealWindow.smooth 1).continuous_deriv_one

theorem exists_oneSidedRealWindow_deriv_bound :
    ∃ C > 0, ∀ t : ℝ, |deriv (oneSidedRealWindow : ℝ → ℝ) t| ≤ C := by
  let C : ℝ := 1 + SchwartzMap.seminorm ℝ 0 1 oneSidedRealWindow
  have hc : 0 ≤ SchwartzMap.seminorm ℝ 0 1 oneSidedRealWindow := apply_nonneg _ _
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro t
  have h := SchwartzMap.le_seminorm' ℝ 0 1 oneSidedRealWindow t
  simp only [pow_zero, one_mul, iteratedDeriv_one, Real.norm_eq_abs] at h
  exact h.trans (by dsimp only [C]; linarith)

end Erdos421

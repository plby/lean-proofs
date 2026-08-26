import ErdosProblems.Erdos421.SchwartzWindowScaling
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # A nonnegative smooth window supported in the preceding unit interval -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

noncomputable def oneSidedBump : ContDiffBump (-1 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def oneSidedSchwartzWindow : 𝓢(ℝ, ℂ) :=
  (oneSidedBump.hasCompactSupport_normed (μ := volume)).comp_left
    (by simp : ((0 : ℝ) : ℂ) = 0) |>.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp oneSidedBump.contDiff_normed)

theorem oneSidedSchwartzWindow_apply (x : ℝ) :
    oneSidedSchwartzWindow x = (oneSidedBump.normed volume x : ℂ) := rfl

theorem oneSidedSchwartzWindow_real_nonneg (x : ℝ) :
    (oneSidedSchwartzWindow x).im = 0 ∧ 0 ≤ (oneSidedSchwartzWindow x).re := by
  rw [oneSidedSchwartzWindow_apply]
  exact ⟨Complex.ofReal_im _, oneSidedBump.nonneg_normed x⟩

theorem oneSidedSchwartzWindow_integral : (∫ x : ℝ, oneSidedSchwartzWindow x) = 1 := by
  simp only [oneSidedSchwartzWindow_apply, integral_complex_ofReal, ContDiffBump.integral_normed,
    Complex.ofReal_one]

theorem oneSidedSchwartzWindow_nonzero {x : ℝ} (hx : oneSidedSchwartzWindow x ≠ 0) :
    -1 < x ∧ x < 0 := by
  have hn : oneSidedBump.normed volume x ≠ 0 := by
    intro he
    apply hx
    rw [oneSidedSchwartzWindow_apply, he, Complex.ofReal_zero]
  have hs : x ∈ Function.support (oneSidedBump.normed volume) := hn
  rw [oneSidedBump.support_normed_eq] at hs
  change x ∈ Metric.ball (-1 / 2 : ℝ) (1 / 2) at hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hs
  constructor <;> linarith

theorem normalized_oneSidedSchwartzWindow_nonzero {δ x : ℝ} (hδ : 0 < δ)
    (hx : normalizedSchwartzScale δ hδ oneSidedSchwartzWindow x ≠ 0) :
    -δ < x ∧ x < 0 := by
  have hn : oneSidedSchwartzWindow (x / δ) ≠ 0 := by
    intro he
    apply hx
    rw [normalizedSchwartzScale_apply, he, smul_zero]
  obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero hn
  constructor
  · have h := (lt_div_iff₀ hδ).mp hlo
    linarith
  · have h := (div_lt_iff₀ hδ).mp hhi
    simpa only [zero_mul] using h

theorem oneSidedDirichletWindow_nonzero_witness (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) {δ y : ℝ} (hδ : 0 < δ)
    (hwindow : schwartzDirichletWindow S a σ
      (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y ≠ 0) :
    ∃ n ∈ S, Real.exp y < n ∧ (n : ℝ) < Real.exp (y + δ) := by
  rw [schwartzDirichletWindow_apply] at hwindow
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hwindow
  have hφ : normalizedSchwartzScale δ hδ oneSidedSchwartzWindow (y - Real.log n) ≠ 0 :=
    (mul_ne_zero_iff.mp hterm).2
  obtain ⟨hlo, hhi⟩ := normalized_oneSidedSchwartzWindow_nonzero hδ hφ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (hS n hn)
  refine ⟨n, hn, ?_, ?_⟩
  · have h := Real.exp_lt_exp.mpr (show y < Real.log n by linarith)
    rwa [Real.exp_log hnp] at h
  · have h := Real.exp_lt_exp.mpr (show Real.log n < y + δ by linarith)
    rwa [Real.exp_log hnp] at h

end Erdos421

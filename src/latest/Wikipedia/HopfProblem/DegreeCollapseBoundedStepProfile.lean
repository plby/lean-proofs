import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith

/-!
# A smooth time step with a constructed derivative bound

The actual step is stationary before one third and after two thirds.
Its derivative has compact support, hence a proved uniform bound. No
quantitative cutoff estimate is supplied as a premise.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

/-- Construct the smooth time step and its global derivative bound. -/
theorem exists_bounded_step_profile :
    ∃ (τ : ℝ → ℝ) (L : ℝ), ContDiff ℝ ∞ τ ∧ 0 < L ∧
      (∀ t, τ t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t, t ≤ 1 / 3 → τ t = 0) ∧ (∀ t, 2 / 3 ≤ t → τ t = 1) ∧
      (∀ t, t ∉ Icc (1 / 3 : ℝ) (2 / 3) → deriv τ t = 0) ∧
      ∀ t, |deriv τ t| ≤ L := by
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτ : ContDiff ℝ ∞ τ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hzero (t : ℝ) (ht : t ≤ 1 / 3) : τ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hone (t : ℝ) (ht : 2 / 3 ≤ t) : τ t = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hout (t : ℝ) (ht : t ∉ Icc (1 / 3 : ℝ) (2 / 3)) : deriv τ t = 0 := by
    by_cases hlo : t < 1 / 3
    · have hg : τ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_lt_nhds hlo] with s hs
        exact hzero s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
    · have hhi : 2 / 3 < t := by
        by_contra hn
        exact ht ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      have hg : τ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds hhi] with s hs
        exact hone s hs.le
      rw [hg.deriv_eq]
      exact deriv_const _ _
  have hcomp : HasCompactSupport (deriv τ) :=
    HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 / 3 : ℝ) (2 / 3))) hout
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous (hτ.continuous_deriv (by simp))
  let L : ℝ := max C 0 + 1
  refine ⟨τ, L, hτ, by dsimp [L]; positivity, ?_, hzero, hone, hout, ?_⟩
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t
    have hh : |deriv τ t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
    exact hh.trans (by dsimp [L]; linarith [le_max_left C 0])

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

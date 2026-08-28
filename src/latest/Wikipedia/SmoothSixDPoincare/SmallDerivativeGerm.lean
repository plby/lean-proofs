import Wikipedia.SmoothSixDPoincare.CutoffLipschitz
import Mathlib.Analysis.Calculus.MeanValue

/-! # A zero derivative gives arbitrarily small Lipschitz constants on a closed neighborhood -/

noncomputable section

open Set Function Filter Topology Metric
open scoped ContDiff NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Choose a closed ball on which the original smooth germ has any positive Lipschitz bound. -/
theorem exists_closedBall_small_lipschitz_of_fderiv_zero {u : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hu : ContDiffOn ℝ ∞ u U)
    (hdu : fderiv ℝ u 0 = 0) {a : ℝ≥0} (ha : 0 < a) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : P) ρ ⊆ U ∧
      LipschitzOnWith a u (closedBall (0 : P) ρ) := by
  have hd : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hzero)
  have hsmall : ∀ᶠ x in 𝓝 (0 : P), ‖fderiv ℝ u x‖ < (a : ℝ) := by
    have h : ∀ᶠ x in 𝓝 (0 : P), fderiv ℝ u x ∈ ball (fderiv ℝ u 0) (a : ℝ) :=
      hd.preimage_mem_nhds (ball_mem_nhds (fderiv ℝ u 0) (show (0 : ℝ) < a from ha))
    simpa only [hdu, mem_ball_zero_iff] using h
  have hnear : ∀ᶠ x in 𝓝 (0 : P), x ∈ U := hU.mem_nhds hzero
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hnear.and hsmall)
  refine ⟨ρ, hρ, fun x hx => (hball hx).1, ?_⟩
  apply (convex_closedBall (0 : P) ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hball hx).1)).differentiableAt (by simp)
  · intro x hx
    exact (hball hx).2.le

end Wikipedia.SmoothSixDPoincare.SmallPerturbation

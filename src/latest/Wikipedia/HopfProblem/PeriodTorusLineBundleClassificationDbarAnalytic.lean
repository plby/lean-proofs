import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarOperations
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticOpen

/-!
# The actual two-variable Cauchy–Riemann criterion

Vanishing of both coordinate antiholomorphic derivatives gives joint
analyticity on an open set.  The proof uses the separately holomorphic
double-Cauchy theorem, not an assumed identification of real smoothness
with complex analyticity.
-/

noncomputable section

open Complex Set

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

theorem analyticOnNhd_of_coordinate_dbar_zero {f : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (h₁ : ∀ q ∈ U, dbarFirst f q = 0) (h₂ : ∀ q ∈ U, dbarSecond f q = 0) :
    AnalyticOnNhd ℂ f U := by
  apply PeriodTorusLineBundleClassificationPolydiscAnalytic.analyticOnNhd_of_continuousOn_of_slices
    hU hf.continuousOn
  · intro w z hz
    have hreal : DifferentiableAt ℝ (fun v => f (v, w)) z :=
      ((hf (z, w) hz).differentiableAt (hU.mem_nhds hz)).comp z
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) z w).differentiableAt
    exact (differentiableAt_complex_iff_dbar.mpr ⟨hreal, h₁ (z, w) hz⟩).differentiableWithinAt
  · intro z w hw
    have hreal : DifferentiableAt ℝ (fun v => f (z, v)) w :=
      ((hf (z, w) hw).differentiableAt (hU.mem_nhds hw)).comp w
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) z w).differentiableAt
    exact (differentiableAt_complex_iff_dbar.mpr ⟨hreal, h₂ (z, w) hw⟩).differentiableWithinAt

theorem coordinate_dbar_zero_of_analyticAt {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : AnalyticAt ℂ f q) : dbarFirst f q = 0 ∧ dbarSecond f q = 0 := by
  constructor
  · have hslice : DifferentiableAt ℂ (fun z => f (z, q.2)) q.1 :=
      hf.differentiableAt.comp q.1
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) q.1 q.2).differentiableAt
    exact dbar_eq_zero_of_differentiableAt hslice
  · have hslice : DifferentiableAt ℂ (fun w => f (q.1, w)) q.2 :=
      hf.differentiableAt.comp q.2
        (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2).differentiableAt
    exact dbar_eq_zero_of_differentiableAt hslice

/-- Two actual real differentiable primitives of the same antiholomorphic
form differ by a genuinely analytic function on their common open domain. -/
theorem analyticOnNhd_sub_of_coordinate_dbar_eq {f g : ℂ × ℂ → ℂ}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (hg : DifferentiableOn ℝ g U)
    (h₁ : ∀ q ∈ U, dbarFirst f q = dbarFirst g q)
    (h₂ : ∀ q ∈ U, dbarSecond f q = dbarSecond g q) :
    AnalyticOnNhd ℂ (fun q => f q - g q) U := by
  apply analyticOnNhd_of_coordinate_dbar_zero (f := fun q => f q - g q) hU (hf.sub hg)
  · intro q hq
    rw [dbarFirst_sub ((hf q hq).differentiableAt (hU.mem_nhds hq))
      ((hg q hq).differentiableAt (hU.mem_nhds hq)), h₁ q hq, sub_self]
  · intro q hq
    rw [dbarSecond_sub ((hf q hq).differentiableAt (hU.mem_nhds hq))
      ((hg q hq).differentiableAt (hU.mem_nhds hq)), h₂ q hq, sub_self]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

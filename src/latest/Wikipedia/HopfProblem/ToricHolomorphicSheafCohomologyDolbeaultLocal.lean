import Wikipedia.HopfProblem.HolomorphicCousinConvolutionSolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Actual local exactness of the one-dimensional antiholomorphic derivative

A smooth function defined near a point is multiplied by an explicitly
constructed smooth cutoff. The resulting compactly supported smooth
function agrees with the original germ. Its actual Cauchy–Green integral
therefore supplies an actual local smooth primitive. The kernel is
identified with genuine holomorphic functions by the Cauchy–Riemann
criterion. These are local analytic facts used by the sheaf resolution.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

open HolomorphicCousin

/-- An actual smooth germ on an open subset of the plane has a globally
smooth compactly supported representative with the same germ. -/
theorem exists_compact_smooth_representative {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) {x : ℂ} (hx : x ∈ U) :
    ∃ v : ℂ → ℂ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ v =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let v : ℂ → ℂ := fun z => (b z : ℂ) * g z
  have hbU : tsupport b ⊆ U := by
    intro z hz
    rw [b.tsupport_eq] at hz
    apply hrU
    exact lt_of_le_of_lt hz (by change r / 2 < r; linarith)
  have hb : ContDiff ℝ ∞ (fun z => (b z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hv : ContDiff ℝ ∞ v := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport b
    · exact hb.contDiffAt.mul ((hg z (hbU hz)).contDiffAt (hU.mem_nhds (hbU hz)))
    · have he : v =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hz] with w hw
        simp only [v, image_eq_zero_of_notMem_tsupport hw, Complex.ofReal_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hc : HasCompactSupport v :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  refine ⟨v, hv, hc, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x b.rIn_pos] with z hz
  simp only [v, b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz),
    Complex.ofReal_one, one_mul]

/-- The actual convergent Cauchy–Green integral gives a smooth primitive
of every smooth function germ in one complex variable. -/
theorem exists_smooth_dbar_primitive_germ {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) {x : ℂ} (hx : x ∈ U) :
    ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ dbar u =ᶠ[𝓝 x] g := by
  obtain ⟨v, hv, hcv, he⟩ := exists_compact_smooth_representative hU hg hx
  obtain ⟨hu, hd⟩ := cauchyGreen_smooth_dbar_solution hv hcv
  exact ⟨cauchyGreen v, hu, (Filter.EventuallyEq.of_eq (funext hd)).trans he⟩

/-- The kernel of the actual antiholomorphic derivative on a smooth
open set consists exactly of actual holomorphic functions there. -/
theorem analyticOnNhd_iff_dbar_zero {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) :
    AnalyticOnNhd ℂ g U ↔ ∀ z ∈ U, dbar g z = 0 := by
  constructor
  · intro h z hz
    exact dbar_eq_zero_of_differentiableAt (h z hz).differentiableAt
  · intro h
    exact analyticOnNhd_of_dbar_eq_zero hU (hg.differentiableOn (by simp)) h

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

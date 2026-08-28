import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Global smooth representatives of local smooth function germs

In a finite-dimensional real normed space, an actual smooth bump supported
inside the given open domain equals one on a smaller closed ball. Its
product with the original function is globally smooth: on the bump support
the original function is smooth, and outside that support the product is
locally zero. No regularity of the original function outside its given
domain is required.
-/

open Set Filter Topology Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A locally smooth real function has a globally smooth compactly
supported representative, supported in the original open set and agreeing
with the original function on an actual closed ball around the point. -/
theorem exists_contDiff_compactlySupported_eqOn_closedBall
    {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ U ∧ EqOn g f (closedBall a r) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let β : ContDiffBump a :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβU : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    exact hrU
  have hg : ContDiff ℝ ∞ (fun x => β x * f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (β : E → ℝ)
    · exact β.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hβU hx)))
    · have hzero : (β : E → ℝ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hconst : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) x := contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
  refine ⟨fun x => β x * f x, hg, β.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans hβU, β.rIn, β.rIn_pos, ?_, ?_⟩
  · exact (closedBall_subset_closedBall β.rIn_lt_rOut.le).trans hrU
  · intro x hx
    change β x * f x = f x
    rw [β.one_of_mem_closedBall hx, one_mul]

/-- Every smooth germ on an open finite-dimensional real domain is
represented by a genuinely globally smooth function. -/
theorem exists_contDiff_extension {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨g, hg, _, _, r, hr, _, he⟩ :=
    exists_contDiff_compactlySupported_eqOn_closedBall hf hU ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [ball_mem_nhds a hr] with x hx
  exact he (ball_subset_closedBall hx)

/-- The localization preserves the actual value, derivative, and curried
Hessian at the chosen point, as well as every iterated derivative germ. -/
theorem exists_contDiff_extension_preserving_derivatives
    {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f ∧ g a = f a ∧
      fderiv ℝ g a = fderiv ℝ f a ∧
      fderiv ℝ (fderiv ℝ g) a = fderiv ℝ (fderiv ℝ f) a ∧
      ∀ n : ℕ, iteratedFDeriv ℝ n g =ᶠ[𝓝 a] iteratedFDeriv ℝ n f := by
  obtain ⟨g, hg, he⟩ := exists_contDiff_extension hf hU ha
  exact ⟨g, hg, he, he.self_of_nhds, he.fderiv_eq, he.fderiv.fderiv_eq,
    fun n => he.iteratedFDeriv ℝ n⟩

end Wikipedia.HopfProblem.SmoothMorseLemma

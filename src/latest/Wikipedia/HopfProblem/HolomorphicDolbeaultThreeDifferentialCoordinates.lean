import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialBasic

/-!
# The native cotangent differential in every original chart

The equality below uses the actual inverse tangent trivialization and
the actual manifold chain rule.  It identifies the coordinate derivative
with the real Fréchet derivative of the literal original chart function.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "IR" => modelWithCornersSelf ℝ E
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- The actual smooth function written in an original chart. -/
def chartFunction (U : Opens M) (s : Functions.SmoothSection E M U) (x₀ : M) :
    E → ℂ := Functions.extend E M U s ∘ (chartAt E x₀).symm

/-- The native inverse tangent trivialization is the derivative of the
inverse original chart, with no tangent-space identification hypothesis. -/
theorem symmL_eq_chart_mfderiv (x₀ x : M) (hx : x ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace IR : M → Type) x₀).symmL ℝ x =
      mfderiv IR IR (chartAt E x₀).symm (chartAt E x₀ x) := by
  simpa only [mfld_simps, mfderivWithin_univ] using
    (TangentBundle.symmL_trivializationAt (I := IR) hx)

/-- Genuine derivative coefficients in any original chart are exactly
the derivative of the original scalar chart function. -/
theorem realSection_coordinates_eq_fderiv (U : Opens M)
    (s : Functions.SmoothSection E M U) (x₀ : M) (x : U)
    (hx : (x : M) ∈ (chartAt E x₀).source) :
    Forms.inCoordinates E M (realSection E M U s) x₀ x =
      fderiv ℝ (chartFunction E M U s x₀) (chartAt E x₀ (x : M)) := by
  have hchart : MDifferentiableAt IR IR (chartAt E x₀).symm
      (chartAt E x₀ (x : M)) :=
    mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x₀)
      ((chartAt E x₀).map_source hx)
  have hf := (Functions.extend_contMDiffAt E M U s x x.property).mdifferentiableAt
    (show ∞ ≠ (0 : ℕ∞ω) by simp)
  have hf' : MDifferentiableAt IR IR₁ (Functions.extend E M U s)
      ((chartAt E x₀).symm (chartAt E x₀ (x : M))) := by
    rw [(chartAt E x₀).left_inv hx]
    exact hf
  have hc := mfderiv_comp (chartAt E x₀ (x : M)) hf' hchart
  rw [mfderiv_eq_fderiv, (chartAt E x₀).left_inv hx] at hc
  ext v
  rw [Forms.inCoordinates_apply, symmL_eq_chart_mfderiv E M x₀ x hx]
  exact (congrArg (fun L : E →L[ℝ] ℂ => L v) hc).symm

/-- Chart representatives are smooth at all actual chart-domain points. -/
theorem chartFunction_contDiffAt (U : Opens M) (s : Functions.SmoothSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ (chartAt E x₀).target)
    (hU : (chartAt E x₀).symm z ∈ U) :
    ContDiffAt ℝ ∞ (chartFunction E M U s x₀) z := by
  have hc : ContMDiffAt IR IR ∞ (chartAt E x₀).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hz
  exact ((Functions.extend_contMDiffAt E M U s _ hU).comp z hc).contDiffAt

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

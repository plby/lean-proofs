import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferential
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyMixed

/-!
# The actual native differential satisfies the closed-form PDE

The original cotangent coordinates of `∂bar s` agree with the actual
Fréchet derivative of the original chart function on the actual chart
domain.  Their germs therefore have the genuine symmetric second
antiholomorphic derivatives, in every original preferred chart.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem coordinateForm_differentialSection (U : Opens M)
    (s : Functions.SmoothSection E M U) (x₀ : M) (z : E)
    (hz : z ∈ ClosedForms.coordinateDomain E M U x₀) :
    ClosedForms.coordinateForm E M U (differentialSection E M U s).val x₀ z =
      dbar (chartFunction E M U s x₀) z := by
  rw [ClosedForms.coordinateForm_eq_inCoordinates E M U _ x₀ z hz,
    differentialSection_inCoordinates E M U s x₀
      ⟨(chartAt E x₀).symm z, hz.2⟩ ((chartAt E x₀).map_target hz.1),
    (chartAt E x₀).right_inv hz.1]

/-- The equality is an actual entire coefficient germ, so its scalar
coefficient derivatives can be compared without a differentiability assumption. -/
theorem coordinateForm_differentialSection_germ (U : Opens M)
    (s : Functions.SmoothSection E M U) (x₀ : M) (z : E)
    (hz : z ∈ ClosedForms.coordinateDomain E M U x₀) :
    ClosedForms.coordinateForm E M U (differentialSection E M U s).val x₀ =ᶠ[𝓝 z]
      dbar (chartFunction E M U s x₀) := by
  filter_upwards [(ClosedForms.coordinateDomain E M U x₀).isOpen.mem_nhds hz] with y hy
  exact coordinateForm_differentialSection E M U s x₀ y hy

/-- The actual differential of an actual smooth function is closed in
every original chart, by the true real Schwarz theorem. -/
theorem differentialSection_isClosed (U : Opens M) (s : Functions.SmoothSection E M U) :
    ClosedForms.IsClosed E M U (differentialSection E M U s).val := by
  intro x₀ z hz v w
  have he := coordinateForm_differentialSection_germ E M U s x₀ z hz
  have hw : dbar (fun y => ClosedForms.coordinateForm E M U
        (differentialSection E M U s).val x₀ y w) z =
      dbar (fun y => dbar (chartFunction E M U s x₀) y w) z :=
    dbar_congr (he.fun_comp (fun L : E →L[ℝ] ℂ => L w))
  have hv : dbar (fun y => ClosedForms.coordinateForm E M U
        (differentialSection E M U s).val x₀ y v) z =
      dbar (fun y => dbar (chartFunction E M U s x₀) y v) z :=
    dbar_congr (he.fun_comp (fun L : E →L[ℝ] ℂ => L v))
  rw [hw, hv]
  apply dbar_dbar_of_contDiffAt
  exact (chartFunction_contDiffAt E M U s x₀ z hz.1 hz.2).of_le (by
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)

/-- The original differential with its proved genuine closedness, not a
definition of closedness by the existence of a primitive. -/
def closedSection (U : Opens M) (s : Functions.SmoothSection E M U) :
    ClosedForms.ClosedFormSection E M U :=
  ClosedForms.sectionMk E M U (differentialSection E M U s)
    (differentialSection_isClosed E M U s)

@[simp] theorem closedSection_toForm (U : Opens M) (s : Functions.SmoothSection E M U) :
    ClosedForms.ClosedFormSection.toForm E M (closedSection E M U s) =
      differentialSection E M U s := rfl

theorem closedSection_restrict {U V : Opens M} (h : U ≤ V)
    (s : Functions.SmoothSection E M V) :
    closedSection E M U (Functions.restriction E M h s) =
      ClosedForms.restriction E M h (closedSection E M V s) := by
  apply ClosedForms.ClosedFormSection.ext E M
  intro x
  exact congrArg (fun a : Forms.FormSection E M U => a x)
    (differentialSection_restrict E M h s)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

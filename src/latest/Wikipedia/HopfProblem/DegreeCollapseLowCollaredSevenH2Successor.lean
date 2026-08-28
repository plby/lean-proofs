import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenTwoSphereSurgery
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveTwoCore

/-!

# Every integral half-H2 class has an actual native killing surgery

Simple connectivity supplies the exact integral two-sphere representative.
The proved positive embedded perturbation and framed attachment construction
then give a native surgery successor with the exact quotient kernel. Neither
an embedded representative nor a surgery pair is supplied as an extra input.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  [SimplyConnectedSpace S.PositiveHalf]

theorem exists_h2_killing_step (c : SingularHomology S.PositiveHalf 2) :
    ∃ U : LowCollaredSevenState B, S.Step U ∧ SimplyConnectedSpace U.PositiveHalf ∧
      ∃ φ : SingularHomology S.PositiveHalf 2 →ₗ[ℤ] SingularHomology U.PositiveHalf 2,
        Surjective φ ∧ LinearMap.ker φ = Submodule.span ℤ {c} := by
  obtain ⟨g, hg, hi, hd, hc⟩ := S.collar.exists_interior_twoSphere_representative
    S.embedding S.normalFrame c
  obtain ⟨U, hSU, hU, φ, hφ, hker⟩ := S.exists_twoSphere_step_of_embedded_representative
    g hg hi.injective hd c hc
  exact ⟨U, hSU, hU.mpr inferInstance, φ, hφ, hker⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

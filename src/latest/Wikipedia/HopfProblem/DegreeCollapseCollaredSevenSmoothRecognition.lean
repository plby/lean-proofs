import Wikipedia.HopfProblem.DegreeCollapseMinimalThreeFourElimination
import Wikipedia.HopfProblem.DegreeCollapseReflectedAcyclicFramedFilling

/-!

# Smooth standard-sphere recognition for the supplied original collared state

The proved finite surgery path clears the actual filling's middle homology
and preserves its original native zero-boundary atlas. Complete middle
handle elimination recognizes the terminal half as a native smooth disk.
Compose the actual boundary diffeomorphisms to identify the INITIAL zero
fiber with the literal standard sphere. The initial collared state and
finite ambient H3 remain explicit hypotheses.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]

theorem nonempty_zero_sphere_diffeomorph_of_finite_third
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Finite (SingularHomology S.Space 3)] :
    letI := S.zeroAtlas;
    Nonempty (Diffeomorph (𝓡 6) (𝓡 6) S.Zero (Sphere 6) ∞) := by
  let _ := S.zeroAtlas
  obtain ⟨U, h, _, hdata⟩ := S.exists_acyclic_framedFilling eBoundary
  change SimplyConnectedSpace U.Half ∧
    (∀ k : ℕ, k ≠ 0 → Subsingleton (SingularHomology U.Half k)) at hdata
  let _ : Subsingleton (SingularHomology U.Half 3) := hdata.2 3 (by decide)
  let _ : Subsingleton (SingularHomology U.Half 4) := hdata.2 4 (by decide)
  let _ := U.zeroAtlas
  obtain ⟨D⟩ := h.zero_diffeomorphic
  obtain ⟨E⟩ := U.nonempty_zero_sphere_diffeomorph_of_middle_homology_zero eBoundary
  exact ⟨D.trans E.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

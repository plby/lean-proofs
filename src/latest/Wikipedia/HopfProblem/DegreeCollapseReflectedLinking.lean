import Wikipedia.HopfProblem.DegreeCollapseReflectedFillingFourthHomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenLinkingSymmetry

/-!
# The supplied reflected filling's original closed linking pairing

All connectivity and finite-homology hypotheses of the original closed
pairing are proved from the actual half and the original endpoint sphere.
The pairing below is definitionally the previously constructed original
cap/torsion-evaluation pairing with the original reflected fiber atlas.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (eBoundary : EndpointFiber d ≃ₜ Sphere 6)

include eBoundary

theorem endpoint_homology_of_sphere (k : ℕ) (hk : k ≠ 0) (h6 : k ≠ 6) :
    Subsingleton (SingularHomology (EndpointFiber d) k) := by
  let : Subsingleton (SingularHomology (Sphere 6) k) :=
    SphereHomology.unitSphere_homology_subsingleton 5 k hk h6
  exact (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    eBoundary.toHomotopyEquiv k).injective.subsingleton

theorem fiber_second_homology_of_endpoint_sphere
    [Subsingleton (SingularHomology (NonnegativeHalf d) 2)] :
    Subsingleton (SingularHomology (Fiber d) 2) := by
  let := endpoint_homology_of_sphere d eBoundary 1 (by decide) (by decide)
  exact fiber_homology_succ_subsingleton d 1

theorem fiber_third_homology_finite_of_endpoint_sphere
    [Finite (SingularHomology (NonnegativeHalf d) 3)] :
    Finite (SingularHomology (Fiber d) 3) := by
  let := endpoint_homology_of_sphere d eBoundary 2 (by decide) (by decide)
  exact fiber_homology_succ_finite d 2

variable (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6)
  [SimplyConnectedSpace (NonnegativeHalf d)]
  [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]
  [Finite (SingularHomology (NonnegativeHalf d) 3)]

def referenceLinking :
    SingularHomology (Fiber d) 3 →ₗ[ℤ]
      (SingularHomology (Fiber d) 3 →ₗ[ℤ] RationalResidue.Value) := by
  let := fiberAtlas d 6 hdim
  let := fiber_isManifold d 6 hdim
  let := compactSpace_fiber d hmiss
  let : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
  let : SimplyConnectedSpace (EndpointFiber d) := simplyConnectedSpace_of_homeomorph eBoundary
  let : SimplyConnectedSpace (Fiber d) := fiber_simplyConnected_of_half d
  let := fiber_second_homology_of_endpoint_sphere d eBoundary
  let := fiber_third_homology_finite_of_endpoint_sphere d eBoundary
  exact IntegralSevenLinking.linking (E := Vector 7) (Fiber d)

theorem referenceLinking_symmetry (x y : SingularHomology (Fiber d) 3) :
    referenceLinking d eBoundary hmiss hdim x y = referenceLinking d eBoundary hmiss hdim y x := by
  let := fiberAtlas d 6 hdim
  let := fiber_isManifold d 6 hdim
  let := compactSpace_fiber d hmiss
  let : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
  let : SimplyConnectedSpace (EndpointFiber d) := simplyConnectedSpace_of_homeomorph eBoundary
  let : SimplyConnectedSpace (Fiber d) := fiber_simplyConnected_of_half d
  let := fiber_second_homology_of_endpoint_sphere d eBoundary
  let := fiber_third_homology_finite_of_endpoint_sphere d eBoundary
  exact IntegralSevenLinking.linking_symmetry (E := Vector 7) (Fiber d) x y

theorem referenceLinking_left_nondegenerate (x : SingularHomology (Fiber d) 3)
    (hx : ∀ y, referenceLinking d eBoundary hmiss hdim x y = 0) : x = 0 := by
  let := fiberAtlas d 6 hdim
  let := fiber_isManifold d 6 hdim
  let := compactSpace_fiber d hmiss
  let : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
  let : SimplyConnectedSpace (EndpointFiber d) := simplyConnectedSpace_of_homeomorph eBoundary
  let : SimplyConnectedSpace (Fiber d) := fiber_simplyConnected_of_half d
  let := fiber_second_homology_of_endpoint_sphere d eBoundary
  let := fiber_third_homology_finite_of_endpoint_sphere d eBoundary
  exact IntegralSevenLinking.linking_left_nondegenerate (E := Vector 7) (Fiber d) x hx

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

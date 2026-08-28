import Wikipedia.HopfProblem.DegreeCollapseReflectedDoubleHomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenFourthHomology
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.NoExoticSixSphere.SimplyConnected

/-!
# Fourth homology vanishing for the supplied original seven-dimensional filling

The double's original atlas, compactness, simple connectivity and low
integral homology have all been constructed. Closed integral cap duality
therefore applies to that double. The original absolute-time retraction
then gives fourth-homology vanishing on the actual filling half, and the
coordinate-preserving original slab homeomorphism gives the same result
for the original slab. No closed-manifold theorem is applied to a boundary
atlas. A supplied cylinder, low connectivity and finite third homology
remain explicit inputs; the original threefold's initial filling is not
asserted to exist.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris PeriodTorusHigherHomology

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem fiber_fourth_homology_subsingleton (hmiss : ∀ x, d.rightMap x ≠ b)
    (hd : m = n + 6) [SimplyConnectedSpace (NonnegativeHalf d)]
    [PathConnectedSpace (EndpointFiber d)]
    [Subsingleton (SingularHomology (EndpointFiber d) 1)]
    [Subsingleton (SingularHomology (EndpointFiber d) 2)]
    [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]
    [Finite (SingularHomology (NonnegativeHalf d) 3)] :
    Subsingleton (SingularHomology (Fiber d) 4) := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := compactSpace_fiber d hmiss
  let : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
  let : SimplyConnectedSpace (Fiber d) := fiber_simplyConnected_of_half d
  let : Subsingleton (SingularHomology (Fiber d) 2) :=
    fiber_homology_succ_subsingleton d 1
  let : Finite (SingularHomology (Fiber d) 3) := fiber_homology_succ_finite d 2
  exact IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) (Fiber d)

theorem half_fourth_homology_of_endpoint_sphere (hmiss : ∀ x, d.rightMap x ≠ b)
    (hd : m = n + 6) (e : EndpointFiber d ≃ₜ Sphere 6)
    [SimplyConnectedSpace (NonnegativeHalf d)]
    [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]
    [Finite (SingularHomology (NonnegativeHalf d) 3)] :
    Subsingleton (SingularHomology (NonnegativeHalf d) 4) := by
  let : SimplyConnectedSpace (EndpointFiber d) := simplyConnectedSpace_of_homeomorph e
  let : Subsingleton (SingularHomology (Sphere 6) 1) :=
    SphereHomology.unitSphere_homology_subsingleton 5 1 (by decide) (by decide)
  let : Subsingleton (SingularHomology (Sphere 6) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 5 2 (by decide) (by decide)
  let : Subsingleton (SingularHomology (EndpointFiber d) 1) :=
    (homotopyEquivHomologyEquiv e.toHomotopyEquiv 1).injective.subsingleton
  let : Subsingleton (SingularHomology (EndpointFiber d) 2) :=
    (homotopyEquivHomologyEquiv e.toHomotopyEquiv 2).injective.subsingleton
  let : Subsingleton (SingularHomology (Fiber d) 4) :=
    fiber_fourth_homology_subsingleton d hmiss hd
  exact half_homology_subsingleton d 4

theorem originalSlab_fourth_homology_of_endpoint_sphere (hmiss : ∀ x, d.rightMap x ≠ b)
    (hd : m = n + 6) (e : EndpointFiber d ≃ₜ Sphere 6)
    [SimplyConnectedSpace (CylinderFiberSlab.slab d.map b 0 1)]
    [Subsingleton (SingularHomology (CylinderFiberSlab.slab d.map b 0 1) 2)]
    [Finite (SingularHomology (CylinderFiberSlab.slab d.map b 0 1) 3)] :
    Subsingleton (SingularHomology (CylinderFiberSlab.slab d.map b 0 1) 4) := by
  let q := (originalHalfHomeomorph d hmiss).toHomotopyEquiv
  let : SimplyConnectedSpace (NonnegativeHalf d) := q.symm.simplyConnectedSpace
  let : Subsingleton (SingularHomology (NonnegativeHalf d) 2) :=
    (homotopyEquivHomologyEquiv q.symm 2).injective.subsingleton
  let : Finite (SingularHomology (NonnegativeHalf d) 3) :=
    Finite.of_injective _ (homotopyEquivHomologyEquiv q.symm 3).injective
  let : Subsingleton (SingularHomology (NonnegativeHalf d) 4) :=
    half_fourth_homology_of_endpoint_sphere d hmiss hd e
  exact (homotopyEquivHomologyEquiv q 4).injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

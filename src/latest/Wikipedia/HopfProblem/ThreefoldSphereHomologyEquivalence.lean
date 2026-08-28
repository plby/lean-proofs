import Wikipedia.HopfProblem.ThreefoldHomotopySix
import Wikipedia.HopfProblem.ThreefoldSphereHomologyMap
import Wikipedia.HopfProblem.SixSphereCubeHurewicz

/-!
# An actual continuous homology equivalence from the standard six-sphere

The original based six-cube realizing the threefold's marked top class
factors through the literal Euclidean unit six-sphere. This gives a genuine
continuous map whose original singular-homology maps are isomorphisms in
every degree. The top-class argument does not stipulate an orientation or
the homology class of the collapsed-boundary cube.

Neither the map nor its homology-isomorphism property has a recognition,
Whitehead, CW, or gluing-classification premise. This theorem does not yet
assert a homotopy equivalence, a homeomorphism, or a diffeomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereHomologyEquivalence

open SingularMayerVietoris

/-- The genuine singular class of the original cube-boundary collapse onto the sphere. -/
def sourceCubeClass : SingularHomology SixSphere 6 :=
  SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop

/-- An actual continuous map from the literal standard sphere, at each original base point. -/
def sphereMap (x : Space) : C(SixSphere, Space) :=
  SixSphereCube.factorMap (HomotopySix.generatingCube x)

@[simp] theorem sphereMap_basePoint (x : Space) :
    sphereMap x SixSphereCube.sphereBasePoint = x :=
  SixSphereCube.factorMap_basePoint (HomotopySix.generatingCube x)

/-- The continuous map recovers the actual original generating cube pointwise. -/
@[simp] theorem sphereMap_cubeSphereMap (x : Space) (u : Fin 6 → unitInterval) :
    sphereMap x (SixSphereCube.cubeSphereMap u) = HomotopySix.generatingCube x u :=
  SixSphereCube.factorMap_cubeSphereMap (HomotopySix.generatingCube x) u

/-- Its original induced map sends the actual quotient-cube class to the original top class. -/
@[simp] theorem sphereMap_sourceCubeClass (x : Space) :
    singularHomologyMap (sphereMap x) 6 sourceCubeClass = Homology.TopDegree.topClass :=
  (SixSphereCube.factor_cubeHomologyClass (HomotopySix.generatingCube x)).trans
    (HomotopySix.generatingCube_homologyClass x)

/-- The actual map, not merely a groupwise comparison, induces isomorphisms in every degree. -/
theorem homologyMap_bijective (x : Space) (n : ℕ) :
    Function.Bijective (singularHomologyMap (sphereMap x) n) :=
  SphereHomologyMap.homologyMap_bijective_of_topClass_preimage
    (sphereMap x) sourceCubeClass (sphereMap_sourceCubeClass x) n

/-- The inverse on homology belongs to the original induced map of this actual continuous map. -/
def homologyEquiv (x : Space) (n : ℕ) :
    SingularHomology SixSphere n ≃ₗ[ℤ] SingularHomology Space n :=
  SphereHomologyMap.homologyEquivOfTopClassPreimage
    (sphereMap x) sourceCubeClass (sphereMap_sourceCubeClass x) n

@[simp] theorem homologyEquiv_toLinearMap (x : Space) (n : ℕ) :
    (homologyEquiv x n).toLinearMap = singularHomologyMap (sphereMap x) n := rfl

/-- In particular, the literal quotient-cube class is genuinely nonzero. -/
theorem sourceCubeClass_ne_zero : sourceCubeClass ≠ 0 := by
  intro h
  have he := congrArg (singularHomologyMap (sphereMap PiOne.basepoint) 6) h
  rw [sphereMap_sourceCubeClass, map_zero] at he
  exact Homology.TopDegree.topClass_ne_zero he

/-- No construction-specific hypothesis is left in this based existence statement. -/
theorem exists_based_homology_equivalence (x : Space) :
    ∃ f : C(SixSphere, Space), f SixSphereCube.sphereBasePoint = x ∧
      ∀ n : ℕ, Function.Bijective (singularHomologyMap f n) :=
  ⟨sphereMap x, sphereMap_basePoint x, homologyMap_bijective x⟩

/-- The original constructed threefold is the target of a genuine sphere homology equivalence. -/
theorem exists_homology_equivalence :
    ∃ f : C(SixSphere, Space),
      ∀ n : ℕ, Function.Bijective (singularHomologyMap f n) :=
  ⟨sphereMap PiOne.basepoint, homologyMap_bijective PiOne.basepoint⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereHomologyEquivalence

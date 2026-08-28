import Wikipedia.HopfProblem.ThreefoldHomologySphere
import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# A top-class preimage detects an actual sphere homology equivalence

For an actual continuous map from the standard six-sphere to the constructed
threefold, one preimage of the original marked top class suffices to make all
of its native singular-homology maps isomorphisms. In degree six this uses
surjectivity between the genuine infinite cyclic groups; it does not assume
that the proposed preimage has a specified orientation or is a generator.

This is a criterion for a supplied continuous map and supplied preimage. It
does not construct that map, infer a homotopy equivalence, or recognize the
smooth manifold. Those are separate geometric tasks.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereHomologyMap

open SingularMayerVietoris

variable (f : C(SixSphere, Space))

/-- One actual preimage of the original primitive top class makes the top map surjective. -/
theorem six_surjective_of_topClass_preimage (a : SingularHomology SixSphere 6)
    (ha : singularHomologyMap f 6 a = Homology.TopDegree.topClass) :
    Function.Surjective (singularHomologyMap f 6) := by
  intro b
  refine ⟨Homology.TopDegree.homologySixEquiv b • a, ?_⟩
  rw [map_zsmul, ha]
  exact (Homology.TopDegree.eq_smul_topClass b).symm

/-- The original top homology map is then bijective, not merely a rank comparison. -/
theorem six_bijective_of_topClass_preimage (a : SingularHomology SixSphere 6)
    (ha : singularHomologyMap f 6 a = Homology.TopDegree.topClass) :
    Function.Bijective (singularHomologyMap f 6) := by
  let : IsNoetherian ℤ (SingularHomology Space 6) :=
    isNoetherian_of_injective Homology.TopDegree.homologySixEquiv.toLinearMap
      Homology.TopDegree.homologySixEquiv.injective
  have hsurj := six_surjective_of_topClass_preimage f a ha
  refine ⟨?_, hsurj⟩
  exact IsNoetherian.injective_of_surjective_of_injective
    HomologySphere.homologySixEquivSixSphere.symm.toLinearMap
    (singularHomologyMap f 6) HomologySphere.homologySixEquivSixSphere.symm.injective hsurj

/-- Every original singular-homology map is an isomorphism once that actual preimage exists. -/
theorem homologyMap_bijective_of_topClass_preimage (a : SingularHomology SixSphere 6)
    (ha : singularHomologyMap f 6 a = Homology.TopDegree.topClass) (n : ℕ) :
    Function.Bijective (singularHomologyMap f n) := by
  by_cases hn0 : n = 0
  · subst n
    let := space_pathConnected
    exact SphereHomology.singularHomologyMap_zero_bijective f
  by_cases hn6 : n = 6
  · subst n
    exact six_bijective_of_topClass_preimage f a ha
  let := HomologySphere.homology_subsingleton n hn0 hn6
  let := SixSphereHomology.homology_subsingleton n hn0 hn6
  exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

/-- The equivalence has exactly the original induced homology map as its forward map. -/
def homologyEquivOfTopClassPreimage (a : SingularHomology SixSphere 6)
    (ha : singularHomologyMap f 6 a = Homology.TopDegree.topClass) (n : ℕ) :
    SingularHomology SixSphere n ≃ₗ[ℤ] SingularHomology Space n :=
  LinearEquiv.ofBijective (singularHomologyMap f n)
    (homologyMap_bijective_of_topClass_preimage f a ha n)

@[simp] theorem homologyEquivOfTopClassPreimage_toLinearMap
    (a : SingularHomology SixSphere 6)
    (ha : singularHomologyMap f 6 a = Homology.TopDegree.topClass) (n : ℕ) :
    (homologyEquivOfTopClassPreimage f a ha n).toLinearMap = singularHomologyMap f n := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereHomologyMap

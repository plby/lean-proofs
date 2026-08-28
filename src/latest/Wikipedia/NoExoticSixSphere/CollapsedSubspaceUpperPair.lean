import Wikipedia.NoExoticSixSphere.CollapsedSubspacePushout
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderOverlapEquivalence
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison
import Wikipedia.NoExoticSixSphere.RelativeSingularExcision

/-!
# The actual upper-cylinder pair retracts onto the original subspace pair

The ambient retraction is the checked upper-cylinder retraction. On the
overlap it lands in the actual collapsed subspace, and its composite
with the midpoint equivalence is literally the identity there. Thus the
actual map of pairs induces relative-homology isomorphisms in every degree.
-/

noncomputable section

open CategoryTheory Set
open scoped ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.CollapsedSubspaceCylinder

open CollapsedSubspacePushout DoubleMappingCylinder

variable {X : Type} [TopologicalSpace X] (A : Set X)

abbrev Cylinder := space (inclusion A) (toPoint A)

abbrev upperSet : Set (Cylinder A) := upper (inclusion A) (toPoint A)

abbrev lowerSet : Set (Cylinder A) := lower (inclusion A) (toPoint A)

abbrev overlapSet : Set (upperSet A) :=
  RelativeSingularHomology.overlapIn (upperSet A) (lowerSet A)

def upperMap : C(upperSet A, X) := upperRetraction (inclusion A) (toPoint A)

theorem upperMap_mapsTo : Set.MapsTo (upperMap A) (overlapSet A) A := by
  intro p hp
  obtain ⟨t, a, he, _, _⟩ := overlap_representative (inclusion A) (toPoint A)
    ⟨p.val, hp, p.property⟩
  change upperRetraction (inclusion A) (toPoint A) p ∈ A
  rw [upperRetraction_tube (inclusion A) (toPoint A) p t a he.symm]
  exact a.property

def overlapPresentation : overlap (inclusion A) (toPoint A) ≃ₜ overlapSet A where
  toFun p := ⟨⟨p.val, p.property.2⟩, p.property.1⟩
  invFun p := ⟨p.val.val, p.property, p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def midpointEquiv : A ≃ₕ overlapSet A :=
  (overlapEquiv (inclusion A) (toPoint A)).trans (overlapPresentation A).toHomotopyEquiv

theorem upperMap_midpoint :
    (RelativeSingularHomology.restrictedMap (upperMap A) (upperMap_mapsTo A)).comp
      (midpointEquiv A).toFun = ContinuousMap.id A := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  exact upperRetraction_tube (inclusion A) (toPoint A) _ middlePoint.val a rfl

theorem upperMap_homology_bijective (d : ℕ) :
    Function.Bijective (singularHomologyMap (upperMap A) d) :=
  (homotopyEquivHomologyEquiv (upperEquiv (inclusion A) (toPoint A)).symm d).bijective

theorem upperMap_restriction_homology_bijective (d : ℕ) :
    Function.Bijective (singularHomologyMap
      (RelativeSingularHomology.restrictedMap (upperMap A) (upperMap_mapsTo A)) d) := by
  let E := homotopyEquivHomologyEquiv (midpointEquiv A) d
  have hc := congrArg (fun f ↦ singularHomologyMap f d) (upperMap_midpoint A)
  rw [singularHomologyMap_comp, singularHomologyMap_id] at hc
  have hb : Function.Bijective
      ((singularHomologyMap
        (RelativeSingularHomology.restrictedMap (upperMap A) (upperMap_mapsTo A)) d).comp
          (singularHomologyMap (midpointEquiv A).toFun d)) := by
    rw [hc]
    exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ E.bijective).mp hb

theorem upperMap_relative_bijective (d : ℕ) : Function.Bijective
    (RelativeSingularHomology.map (upperMap A) (upperMap_mapsTo A) d) :=
  RelativeSingularHomology.map_bijective_of_absolute (upperMap A) (upperMap_mapsTo A)
    (upperMap_homology_bijective A) (upperMap_restriction_homology_bijective A) d

end NoExoticSixSphere.CollapsedSubspaceCylinder

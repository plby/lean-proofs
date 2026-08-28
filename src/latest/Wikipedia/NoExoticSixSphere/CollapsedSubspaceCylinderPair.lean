import Wikipedia.NoExoticSixSphere.CollapsedSubspaceUpperPair
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderHomologyRange

/-!
# The original cylinder collapse as a map of actual pairs

The lower open piece maps to the collapsed point. Its restriction is a
homology equivalence because this piece retracts to the point. Homotopy
extension gives the ambient collapse equivalence. On the upper piece,
collapse is exactly the original quotient after the actual retraction.
-/

noncomputable section

open CategoryTheory Set
open scoped ContinuousMap unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.CollapsedSubspaceCylinder

open CollapsedSubspacePushout DoubleMappingCylinder

variable {X : Type} [TopologicalSpace X] (A : Set X) (a : A)

def pointSet : Set (CollapsedSubspace.Space A) := {CollapsedSubspace.quotientMap A a.val}

def collapseMap : C(Cylinder A, CollapsedSubspace.Space A) :=
  (collapse (inclusion A) (toPoint A) (isPushout A a)).hom

theorem collapseMap_left (x : X) :
    collapseMap A a (left (inclusion A) (toPoint A) x) = CollapsedSubspace.quotientMap A x :=
  congrArg (fun g ↦ g x) (left_collapse (inclusion A) (toPoint A) (isPushout A a))

theorem collapseMap_right (u : Unit) :
    collapseMap A a (right (inclusion A) (toPoint A) u) =
      CollapsedSubspace.quotientMap A a.val :=
  congrArg (fun g ↦ g u) (right_collapse (inclusion A) (toPoint A) (isPushout A a))

theorem collapseMap_tube (t : I) (b : A) :
    collapseMap A a (tube (inclusion A) (toPoint A) (t, b)) =
      CollapsedSubspace.quotientMap A a.val :=
  congrArg (fun g ↦ g (t, b)) (tube_collapse (inclusion A) (toPoint A) (isPushout A a))

theorem collapseMap_mapsTo : Set.MapsTo (collapseMap A a) (lowerSet A) (pointSet A a) := by
  intro p hp
  change collapseMap A a p = CollapsedSubspace.quotientMap A a.val
  rcases jointly_surjective (inclusion A) (toPoint A) p with
    ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨t, b, rfl⟩
  · exact ((left_notMem_lower (inclusion A) (toPoint A) x) hp).elim
  · exact collapseMap_right A a u
  · exact collapseMap_tube A a t b

def pointHomeomorph : Unit ≃ₜ pointSet A a where
  toFun _ := ⟨CollapsedSubspace.quotientMap A a.val, rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := Subtype.ext p.property.symm
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

theorem collapseMap_restriction_homology_bijective (d : ℕ) :
    Function.Bijective (singularHomologyMap
      (RelativeSingularHomology.restrictedMap (collapseMap A a) (collapseMap_mapsTo A a)) d) := by
  let : Subsingleton (pointSet A a) :=
    ⟨fun p q ↦ Subtype.ext (p.property.trans q.property.symm)⟩
  let E : lowerSet A ≃ₕ pointSet A a :=
    (lowerEquiv (inclusion A) (toPoint A)).symm.trans (pointHomeomorph A a).toHomotopyEquiv
  have he : RelativeSingularHomology.restrictedMap (collapseMap A a) (collapseMap_mapsTo A a) =
      E.toFun := ContinuousMap.ext (fun _ ↦ Subsingleton.elim _ _)
  rw [he]
  exact (homotopyEquivHomologyEquiv E d).bijective

theorem collapseMap_homology_bijective
    (hA : HomotopyExtension.HasHomotopyExtension (inclusion A)) (d : ℕ) :
    Function.Bijective (singularHomologyMap (collapseMap A a) d) :=
  collapse_homology_bijective (inclusion A) (toPoint A) (isPushout A a) hA d

theorem collapseMap_relative_bijective
    (hA : HomotopyExtension.HasHomotopyExtension (inclusion A)) (d : ℕ) :
    Function.Bijective (RelativeSingularHomology.map
      (collapseMap A a) (collapseMap_mapsTo A a) d) :=
  RelativeSingularHomology.map_bijective_of_absolute
    (collapseMap A a) (collapseMap_mapsTo A a)
    (collapseMap_homology_bijective A a hA) (collapseMap_restriction_homology_bijective A a) d

theorem quotientMap_mapsTo :
    Set.MapsTo (CollapsedSubspace.quotientMap A) A (pointSet A a) := by
  intro x hx
  exact (CollapsedSubspace.quotientMap_eq_iff A x a.val).mpr (Or.inr ⟨hx, a.property⟩)

theorem collapse_upper_factor :
    (collapseMap A a).comp (subtypeInclusion (upperSet A)) =
      (CollapsedSubspace.quotientMap A).comp (upperMap A) := by
  apply ContinuousMap.ext
  rintro ⟨p, hp⟩
  rcases jointly_surjective (inclusion A) (toPoint A) p with
    ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨t, b, rfl⟩
  · change collapseMap A a (left (inclusion A) (toPoint A) x) =
      CollapsedSubspace.quotientMap A
        (upperRetraction (inclusion A) (toPoint A) (upperInclusion (inclusion A) (toPoint A) x))
    rw [collapseMap_left, upperRetraction_inclusion]
  · exact ((right_notMem_upper (inclusion A) (toPoint A) u) hp).elim
  · change collapseMap A a (tube (inclusion A) (toPoint A) (t, b)) =
      CollapsedSubspace.quotientMap A
        (upperRetraction (inclusion A) (toPoint A) ⟨tube (inclusion A) (toPoint A) (t, b), hp⟩)
    rw [collapseMap_tube, upperRetraction_tube (inclusion A) (toPoint A) _ t b rfl]
    exact (CollapsedSubspace.quotientMap_eq_iff A a.val b.val).mpr
      (Or.inr ⟨a.property, b.property⟩)

end NoExoticSixSphere.CollapsedSubspaceCylinder

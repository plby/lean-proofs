import Wikipedia.NoExoticSixSphere.PartialFrameIntegerPresentation
import Wikipedia.NoExoticSixSphere.PartialFrameBaseFactorRange

/-!
# The actual integer relations, with their base image computed

The product Hurewicz coordinates turn the genuine reduced inclusion map
into `(a,b) ↦ (b, -(A a + B b))`. The base map `A` has image exactly the
even integers, by the proved reflection calculation. The fiber map `B`
is retained as its actual induced map; no orientation choice is needed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization ColumnBundle ProductThirdHomology
open Wikipedia.HopfProblem.SingularMayerVietoris

def fiberBase : Space 4 1 := baseFrame 3 1

local instance fiberSimplyConnected : SimplyConnectedSpace (Space 4 1) :=
  Stiefel.simplyConnectedSpace (c := 3) (by decide) 1

local instance fiberPiTwo : Subsingleton (HomotopyGroup (Fin 2) (Space 4 1) fiberBase) :=
  Stiefel.subsingleton_homotopyGroup_of_lt (c := 3) (by decide : 2 < 3) 1 fiberBase

local instance sphereSecondGroup :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) (spherePole 3)) :=
  subsingleton_sphereHomotopyGroup (by decide) (spherePole 3)

def baseThirdHomologyEquiv : SingularHomology (Sphere 3) 3 ≃ₗ[ℤ] ℤ :=
  Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2

def overlapIntegerEquiv : SingularHomology (Sphere 3 × Space 4 1) 3 ≃ₗ[ℤ] ℤ × ℤ := by
  let f : (SingularHomology (Sphere 3) 3 × SingularHomology (Space 4 1) 3) ≃ₗ[ℤ] ℤ × ℤ :=
    (baseThirdHomologyEquiv.toAddEquiv.prodCongr
      fiberThirdHomologyEquiv.toAddEquiv).toIntLinearEquiv
  exact (ProductThirdHomology.equivalence (spherePole 3) fiberBase).trans f

variable (v : UnitSphere (Vector 2))

def baseIntegerMap : ℤ →ₗ[ℤ] ℤ :=
  fiberThirdHomologyEquiv.toLinearMap.comp
    ((singularHomologyMap ((equatorialTransition 3 v).comp (leftSection fiberBase)) 3).comp
      baseThirdHomologyEquiv.symm.toLinearMap)

def fiberIntegerMap : ℤ →ₗ[ℤ] ℤ :=
  fiberThirdHomologyEquiv.toLinearMap.comp
    ((singularHomologyMap ((equatorialTransition 3 v).comp (rightSection (spherePole 3))) 3).comp
      fiberThirdHomologyEquiv.symm.toLinearMap)

def integerRelationMap : (ℤ × ℤ) →ₗ[ℤ] ℤ × ℤ :=
  pairThirdHomologyEquiv.toLinearMap.comp
    ((reducedLeftMap 3 v 3).comp overlapIntegerEquiv.symm.toLinearMap)

theorem integerRelationMap_apply (a b : ℤ) :
    integerRelationMap v (a, b) = (b, -(baseIntegerMap v a + fiberIntegerMap v b)) := by
  apply Prod.ext
  · change fiberThirdHomologyEquiv
      (singularHomologyMap ContinuousMap.snd 3 (overlapIntegerEquiv.symm (a, b))) = b
    have h := congrArg Prod.snd (overlapIntegerEquiv.apply_symm_apply (a, b))
    change fiberThirdHomologyEquiv
      ((ProductThirdHomology.equivalence (spherePole 3) fiberBase
        (overlapIntegerEquiv.symm (a, b))).2) = b at h
    rw [ProductThirdHomology.equivalence_snd] at h
    exact h
  · change fiberThirdHomologyEquiv
      (-singularHomologyMap (equatorialTransition 3 v) 3 (overlapIntegerEquiv.symm (a, b))) = _
    rw [map_neg]
    change -fiberThirdHomologyEquiv
      (singularHomologyMap (equatorialTransition 3 v) 3
        ((ProductThirdHomology.equivalence (spherePole 3) fiberBase).symm
          (baseThirdHomologyEquiv.symm a, fiberThirdHomologyEquiv.symm b))) = _
    rw [map_product_class (X := Sphere 3) (Y := Space 4 1)
      (spherePole 3) fiberBase (equatorialTransition 3 v), map_add]
    rfl

theorem baseIntegerMap_range : Set.range (baseIntegerMap v) = Set.range (fun z : ℤ ↦ 2 * z) := by
  have hf : (baseIntegerMap v : ℤ → ℤ) =
      (fun a ↦ fiberThirdHomologyEquiv
        (singularHomologyMap ((equatorialTransition 3 v).comp (leftSection fiberBase)) 3 a)) ∘
          baseThirdHomologyEquiv.symm := rfl
  rw [hf, Set.range_comp, baseThirdHomologyEquiv.symm.surjective.range_eq, Set.image_univ]
  exact equatorialTransition_base_homology_range v fiberBase fiberThirdHomologyEquiv

theorem integerRelations_eq_range :
    integerRelations v = LinearMap.range (integerRelationMap v) := by
  ext z
  constructor
  · rintro ⟨b, ⟨a, ha⟩, hb⟩
    refine ⟨overlapIntegerEquiv a, ?_⟩
    change pairThirdHomologyEquiv
      (reducedLeftMap 3 v 3 (overlapIntegerEquiv.symm (overlapIntegerEquiv a))) = z
    rw [LinearEquiv.symm_apply_apply, ha]
    exact hb
  · rintro ⟨a, rfl⟩
    exact ⟨reducedLeftMap 3 v 3 (overlapIntegerEquiv.symm a),
      ⟨overlapIntegerEquiv.symm a, rfl⟩, rfl⟩

end NoExoticSixSphere.Stiefel.ColumnHomology

import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.ModHomologyModule
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# Actual mod-two third homology of a product of two-connected spaces

The maps are the original homology maps of the projections and factor
inclusions. Coefficient reduction and the proved integral product splitting
show that they are inverse. For the product of three-spheres this gives
actual two-dimensional coefficient coordinates, with the factor classes
in the two separate summands.
-/

noncomputable section

namespace NoExoticSixSphere.ProductThirdHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

section General

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def modProjection : ModHomology 2 (X × Y) 3 →+
    (ModHomology 2 X 3 × ModHomology 2 Y 3) :=
  (((modHomologyMap 2 (ContinuousMap.fst : C(X × Y, X)) 3).toAddMonoidHom).prod
    ((modHomologyMap 2 (ContinuousMap.snd : C(X × Y, Y)) 3).toAddMonoidHom))

def modAssembly (x : X) (y : Y) :
    (ModHomology 2 X 3 × ModHomology 2 Y 3) →+ ModHomology 2 (X × Y) 3 :=
  (((modHomologyMap 2 (leftSection y) 3).toAddMonoidHom).coprod
    ((modHomologyMap 2 (rightSection x) 3).toAddMonoidHom))

theorem modAssembly_apply (x : X) (y : Y) (a : ModHomology 2 X 3)
    (b : ModHomology 2 Y 3) : modAssembly x y (a, b) =
      modHomologyMap 2 (leftSection y) 3 a + modHomologyMap 2 (rightSection x) 3 b := rfl

variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X) (y : Y)
  [Subsingleton (HomotopyGroup (Fin 2) X x)] [Subsingleton (HomotopyGroup (Fin 2) Y y)]

local instance modProductSimplyConnected : SimplyConnectedSpace (X × Y) :=
  HigherHomotopy.simplyConnected_product

local instance modProductPiTwo : Subsingleton (HomotopyGroup (Fin 2) (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

theorem modProjection_reduction (a : SingularHomology (X × Y) 3) :
    modProjection (reductionHomologyMap 2 (X × Y) 3 a) =
      (reductionHomologyMap 2 X 3 (equivalence x y a).1,
        reductionHomologyMap 2 Y 3 (equivalence x y a).2) := by
  apply Prod.ext
  · change modHomologyMap 2 ContinuousMap.fst 3 (reductionHomologyMap 2 (X × Y) 3 a) = _
    rw [modHomologyMap_reduction, equivalence_fst]
  · change modHomologyMap 2 ContinuousMap.snd 3 (reductionHomologyMap 2 (X × Y) 3 a) = _
    rw [modHomologyMap_reduction, equivalence_snd]

theorem modAssembly_reduction (a : SingularHomology X 3) (b : SingularHomology Y 3) :
    modAssembly x y (reductionHomologyMap 2 X 3 a, reductionHomologyMap 2 Y 3 b) =
      reductionHomologyMap 2 (X × Y) 3 ((equivalence x y).symm (a, b)) := by
  rw [modAssembly_apply, modHomologyMap_reduction, modHomologyMap_reduction,
    equivalence_symm_pair, map_add]

theorem modAssembly_modProjection (a : ModHomology 2 (X × Y) 3) :
    modAssembly x y (modProjection a) = a := by
  obtain ⟨b, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective (x, y) a
  rw [modProjection_reduction x y, modAssembly_reduction]
  change reductionHomologyMap 2 (X × Y) 3 ((equivalence x y).symm (equivalence x y b)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem modProjection_modAssembly (a : ModHomology 2 X 3 × ModHomology 2 Y 3) :
    modProjection (modAssembly x y a) = a := by
  rcases a with ⟨a, b⟩
  obtain ⟨c, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective x a
  obtain ⟨d, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective y b
  rw [modAssembly_reduction, modProjection_reduction x y, LinearEquiv.apply_symm_apply]

def modEquivalence : ModHomology 2 (X × Y) 3 ≃+
    (ModHomology 2 X 3 × ModHomology 2 Y 3) where
  toFun := modProjection
  map_add' := modProjection.map_add
  invFun := modAssembly x y
  left_inv := modAssembly_modProjection x y
  right_inv := modProjection_modAssembly x y

theorem modEquivalence_left (a : ModHomology 2 X 3) :
    modEquivalence x y (modHomologyMap 2 (leftSection y) 3 a) = (a, 0) := by
  have h := modProjection_modAssembly x y (a, 0)
  rw [modAssembly_apply, map_zero, add_zero] at h
  exact h

theorem modEquivalence_right (b : ModHomology 2 Y 3) :
    modEquivalence x y (modHomologyMap 2 (rightSection x) 3 b) = (0, b) := by
  have h := modProjection_modAssembly x y (0, b)
  rw [modAssembly_apply, map_zero, zero_add] at h
  exact h

end General

local instance modSpherePiTwo :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) (spherePole 3)) :=
  subsingleton_sphereHomotopyGroup (by decide) (spherePole 3)

def modSphereEquivalence : ModHomology 2 (Sphere 3 × Sphere 3) 3 ≃+ ZMod 2 × ZMod 2 :=
  (modEquivalence (spherePole 3) (spherePole 3)).trans
    (((unitSphereModHomologyTopEquiv 2 (by decide) 2).toAddEquiv.prodCongr
      (unitSphereModHomologyTopEquiv 2 (by decide) 2).toAddEquiv))

attribute [local instance] modHomologyModule

def modSphereLinearEquivalence :
    ModHomology 2 (Sphere 3 × Sphere 3) 3 ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 where
  toEquiv := modSphereEquivalence.toEquiv
  map_add' := modSphereEquivalence.map_add
  map_smul' c a := by
    change modSphereEquivalence (c • a) = c • modSphereEquivalence a
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) c with rfl | rfl
    · simp only [zero_smul, map_zero]
    · simp only [one_smul]

theorem modSphereLinearEquivalence_left (a : ModHomology 2 (Sphere 3) 3) :
    modSphereLinearEquivalence (modHomologyMap 2 (leftSection (spherePole 3)) 3 a) =
      (unitSphereModHomologyTopEquiv 2 (by decide) 2 a, 0) := by
  change ((unitSphereModHomologyTopEquiv 2 (by decide) 2)
    (modEquivalence (spherePole 3) (spherePole 3)
      (modHomologyMap 2 (leftSection (spherePole 3)) 3 a)).1,
    (unitSphereModHomologyTopEquiv 2 (by decide) 2)
      (modEquivalence (spherePole 3) (spherePole 3)
        (modHomologyMap 2 (leftSection (spherePole 3)) 3 a)).2) = _
  rw [modEquivalence_left, map_zero]

theorem modSphereLinearEquivalence_right (a : ModHomology 2 (Sphere 3) 3) :
    modSphereLinearEquivalence (modHomologyMap 2 (rightSection (spherePole 3)) 3 a) =
      (0, unitSphereModHomologyTopEquiv 2 (by decide) 2 a) := by
  change ((unitSphereModHomologyTopEquiv 2 (by decide) 2)
    (modEquivalence (spherePole 3) (spherePole 3)
      (modHomologyMap 2 (rightSection (spherePole 3)) 3 a)).1,
    (unitSphereModHomologyTopEquiv 2 (by decide) 2)
      (modEquivalence (spherePole 3) (spherePole 3)
        (modHomologyMap 2 (rightSection (spherePole 3)) 3 a)).2) = _
  rw [modEquivalence_right, map_zero]

end NoExoticSixSphere.ProductThirdHomology

import Wikipedia.NoExoticSixSphere.ProductHomotopyEquiv
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Wikipedia.HopfProblem.ThirdHurewiczIso
import Wikipedia.HopfProblem.ThirdHurewiczNaturality
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# The actual third homology of a product of two-connected spaces

The native product homotopy-group equivalence and the constructed third
Hurewicz maps give a product homology equivalence. Naturality identifies
its two components with the actual singular projection maps. In particular
this marks the third homology of the actual product `S³ × S³` by `ℤ × ℤ`.
-/

noncomputable section

namespace NoExoticSixSphere.ProductThirdHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.ThirdHurewicz

section General

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X) (y : Y)
  [Subsingleton (HomotopyGroup (Fin 2) X x)] [Subsingleton (HomotopyGroup (Fin 2) Y y)]

local instance productSimplyConnected : SimplyConnectedSpace (X × Y) :=
  HigherHomotopy.simplyConnected_product

local instance productPiTwo : Subsingleton (HomotopyGroup (Fin 2) (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

def equivalence : SingularHomology (X × Y) 3 ≃ₗ[ℤ]
    (SingularHomology X 3 × SingularHomology Y 3) := by
  let e₁ : Additive (HomotopyGroup (Fin 3) (X × Y) (x, y)) ≃ₗ[ℤ]
      (Additive (HomotopyGroup (Fin 3) X x) × Additive (HomotopyGroup (Fin 3) Y y)) :=
    ((HigherHomotopy.productMulEquiv (N := Fin 3) (x := x) (y := y)).toAdditive.trans
      (AddEquiv.prodAdditive _ _)).toIntLinearEquiv
  let e₂ : (Additive (HomotopyGroup (Fin 3) X x) × Additive (HomotopyGroup (Fin 3) Y y)) ≃ₗ[ℤ]
      (SingularHomology X 3 × SingularHomology Y 3) :=
    ((hurewiczLinearEquiv x).toAddEquiv.prodCongr
      (hurewiczLinearEquiv y).toAddEquiv).toIntLinearEquiv
  exact (hurewiczLinearEquiv (x, y)).symm.trans (e₁.trans e₂)

theorem equivalence_fst (a : SingularHomology (X × Y) 3) :
    (equivalence x y a).1 = singularHomologyMap ContinuousMap.fst 3 a := by
  let b := (hurewiczLinearEquiv (x, y)).symm a
  have hb : hurewiczLinearEquiv (x, y) b = a := (hurewiczLinearEquiv (x, y)).apply_symm_apply a
  calc
    (equivalence x y a).1 = hurewiczMap x
        ((homotopyMap ContinuousMap.fst (x, y)).toAdditive b) := rfl
    _ = singularHomologyMap ContinuousMap.fst 3 (hurewiczLinearEquiv (x, y) b) :=
      (hurewiczMap_natural ContinuousMap.fst (x, y) b).symm
    _ = singularHomologyMap ContinuousMap.fst 3 a := by rw [hb]

theorem equivalence_snd (a : SingularHomology (X × Y) 3) :
    (equivalence x y a).2 = singularHomologyMap ContinuousMap.snd 3 a := by
  let b := (hurewiczLinearEquiv (x, y)).symm a
  have hb : hurewiczLinearEquiv (x, y) b = a := (hurewiczLinearEquiv (x, y)).apply_symm_apply a
  calc
    (equivalence x y a).2 = hurewiczMap y
        ((homotopyMap ContinuousMap.snd (x, y)).toAdditive b) := rfl
    _ = singularHomologyMap ContinuousMap.snd 3 (hurewiczLinearEquiv (x, y) b) :=
      (hurewiczMap_natural ContinuousMap.snd (x, y) b).symm
    _ = singularHomologyMap ContinuousMap.snd 3 a := by rw [hb]

end General

local instance spherePiTwo : Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) (spherePole 3)) :=
  subsingleton_sphereHomotopyGroup (by decide) (spherePole 3)

def sphereEquivalence : SingularHomology (Sphere 3 × Sphere 3) 3 ≃ₗ[ℤ] ℤ × ℤ :=
  (equivalence (spherePole 3) (spherePole 3)).trans
    ((Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2).toAddEquiv.prodCongr
      (Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2).toAddEquiv
        ).toIntLinearEquiv

theorem sphereEquivalence_fst (a : SingularHomology (Sphere 3 × Sphere 3) 3) :
    (sphereEquivalence a).1 = Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2
      (singularHomologyMap ContinuousMap.fst 3 a) := by
  change Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2
    ((equivalence (spherePole 3) (spherePole 3) a).1) = _
  rw [equivalence_fst]

theorem sphereEquivalence_snd (a : SingularHomology (Sphere 3 × Sphere 3) 3) :
    (sphereEquivalence a).2 = Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2
      (singularHomologyMap ContinuousMap.snd 3 a) := by
  change Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2
    ((equivalence (spherePole 3) (spherePole 3) a).2) = _
  rw [equivalence_snd]

end NoExoticSixSphere.ProductThirdHomology

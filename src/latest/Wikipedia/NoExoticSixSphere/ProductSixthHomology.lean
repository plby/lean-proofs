import Wikipedia.NoExoticSixSphere.ProductHomotopyEquiv
import Wikipedia.NoExoticSixSphere.SixthHurewiczNativeNaturality
import Wikipedia.HopfProblem.SixthHurewiczIso

/-!
# Actual sixth homology of products of five-connected spaces

The native product homotopy equivalence and the genuine sixth Hurewicz
isomorphisms give a homology splitting whose coordinates are the actual
singular projection maps. This will separate the six sphere-valued
letters in the explicit James--Hopf word calculation.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SixthHurewicz PeriodTorusHigherHomology

namespace NoExoticSixSphere.ProductSixthHomology

def leftSection {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    C(X, X × Y) := (ContinuousMap.id X).prodMk (ContinuousMap.const X y)

def rightSection {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    C(Y, X × Y) := (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X) (y : Y)
  [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 2 Y y)]
  [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 3 Y y)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 4 Y y)]
  [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 5 Y y)]

local instance productSimplyConnected : SimplyConnectedSpace (X × Y) :=
  HigherHomotopy.simplyConnected_product

local instance productPiTwo : Subsingleton (π_ 2 (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

local instance productPiThree : Subsingleton (π_ 3 (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

local instance productPiFour : Subsingleton (π_ 4 (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

local instance productPiFive : Subsingleton (π_ 5 (X × Y) (x, y)) :=
  HigherHomotopy.subsingleton_product x y

def equivalence : SingularHomology (X × Y) 6 ≃ₗ[ℤ]
    (SingularHomology X 6 × SingularHomology Y 6) := by
  let e₁ : Additive (π_ 6 (X × Y) (x, y)) ≃ₗ[ℤ]
      (Additive (π_ 6 X x) × Additive (π_ 6 Y y)) :=
    ((HigherHomotopy.productMulEquiv (N := Fin 6) (x := x) (y := y)).toAdditive.trans
      (AddEquiv.prodAdditive _ _)).toIntLinearEquiv
  let e₂ : (Additive (π_ 6 X x) × Additive (π_ 6 Y y)) ≃ₗ[ℤ]
      (SingularHomology X 6 × SingularHomology Y 6) :=
    ((hurewiczLinearEquiv x).toAddEquiv.prodCongr
      (hurewiczLinearEquiv y).toAddEquiv).toIntLinearEquiv
  exact (hurewiczLinearEquiv (x, y)).symm.trans (e₁.trans e₂)

theorem equivalence_fst (a : SingularHomology (X × Y) 6) :
    (equivalence x y a).1 = singularHomologyMap ContinuousMap.fst 6 a := by
  let b := (hurewiczLinearEquiv (x, y)).symm a
  have hb : hurewiczLinearEquiv (x, y) b = a := (hurewiczLinearEquiv (x, y)).apply_symm_apply a
  calc
    (equivalence x y a).1 = hurewiczMap x
        ((homotopyMap ContinuousMap.fst (x, y)).toAdditive b) := rfl
    _ = singularHomologyMap ContinuousMap.fst 6 (hurewiczLinearEquiv (x, y) b) :=
      (hurewiczMap_natural ContinuousMap.fst (x, y) b).symm
    _ = singularHomologyMap ContinuousMap.fst 6 a := by rw [hb]

theorem equivalence_snd (a : SingularHomology (X × Y) 6) :
    (equivalence x y a).2 = singularHomologyMap ContinuousMap.snd 6 a := by
  let b := (hurewiczLinearEquiv (x, y)).symm a
  have hb : hurewiczLinearEquiv (x, y) b = a := (hurewiczLinearEquiv (x, y)).apply_symm_apply a
  calc
    (equivalence x y a).2 = hurewiczMap y
        ((homotopyMap ContinuousMap.snd (x, y)).toAdditive b) := rfl
    _ = singularHomologyMap ContinuousMap.snd 6 (hurewiczLinearEquiv (x, y) b) :=
      (hurewiczMap_natural ContinuousMap.snd (x, y) b).symm
    _ = singularHomologyMap ContinuousMap.snd 6 a := by rw [hb]

omit [SimplyConnectedSpace Y] [Subsingleton (π_ 2 Y y)] [Subsingleton (π_ 3 Y y)]
  [Subsingleton (π_ 4 Y y)] [Subsingleton (π_ 5 Y y)] in
include x in
theorem constant_map_zero (a : SingularHomology X 6) :
    singularHomologyMap (ContinuousMap.const X y) 6 a = 0 := by
  obtain ⟨b, rfl⟩ := (hurewiczLinearEquiv x).surjective a
  change singularHomologyMap (ContinuousMap.const X y) 6 (hurewiczMap x b) = 0
  rw [hurewiczMap_natural, homotopyMap_const]
  exact map_zero (hurewiczMap y)

theorem equivalence_left (a : SingularHomology X 6) :
    equivalence x y (singularHomologyMap (leftSection y) 6 a) = (a, 0) := by
  apply Prod.ext
  · rw [equivalence_fst, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id X) 6 a = a
    rw [singularHomologyMap_id]
    rfl
  · rw [equivalence_snd, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact constant_map_zero x y a

theorem equivalence_right (b : SingularHomology Y 6) :
    equivalence x y (singularHomologyMap (rightSection x) 6 b) = (0, b) := by
  apply Prod.ext
  · rw [equivalence_fst, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact constant_map_zero y x b
  · rw [equivalence_snd, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id Y) 6 b = b
    rw [singularHomologyMap_id]
    rfl

theorem decompose (a : SingularHomology (X × Y) 6) :
    a = singularHomologyMap (leftSection y) 6
        (singularHomologyMap ContinuousMap.fst 6 a) +
      singularHomologyMap (rightSection x) 6
        (singularHomologyMap ContinuousMap.snd 6 a) := by
  apply (equivalence x y).injective
  rw [map_add, equivalence_left, equivalence_right]
  apply Prod.ext
  · simpa only [Prod.fst_add, add_zero] using equivalence_fst x y a
  · simpa only [Prod.snd_add, zero_add] using equivalence_snd x y a

theorem map_product {Z : Type} [TopologicalSpace Z] (f : C(X × Y, Z))
    (a : SingularHomology (X × Y) 6) :
    singularHomologyMap f 6 a =
      singularHomologyMap (f.comp (leftSection y)) 6
        (singularHomologyMap ContinuousMap.fst 6 a) +
      singularHomologyMap (f.comp (rightSection x)) 6
        (singularHomologyMap ContinuousMap.snd 6 a) := by
  conv_lhs => rw [decompose x y a]
  rw [map_add, singularHomologyMap_comp, singularHomologyMap_comp]
  rfl

end NoExoticSixSphere.ProductSixthHomology

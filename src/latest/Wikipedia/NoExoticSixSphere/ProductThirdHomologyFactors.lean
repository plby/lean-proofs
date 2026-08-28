import Wikipedia.NoExoticSixSphere.ProductThirdHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Factor inclusions in the actual third-homology product coordinates

The two actual factor inclusions map to the two summands. Hence any map
out of the product acts on third homology as the sum of its restrictions
to those factors. All maps are the native singular functor maps.
-/

noncomputable section

namespace NoExoticSixSphere.ProductThirdHomology

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.ThirdHurewicz

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def leftSection (y : Y) : C(X, X × Y) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X y)

def rightSection (x : X) : C(Y, X × Y) :=
  (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y)

theorem constant_map_zero [SimplyConnectedSpace X] (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] (y : Y) (a : SingularHomology X 3) :
    singularHomologyMap (ContinuousMap.const X y) 3 a = 0 := by
  obtain ⟨b, rfl⟩ := (hurewiczLinearEquiv x).surjective a
  change singularHomologyMap (ContinuousMap.const X y) 3 (hurewiczMap x b) = 0
  rw [hurewiczMap_natural, homotopyMap_const]
  exact map_zero (hurewiczMap y)

variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X) (y : Y)
  [Subsingleton (HomotopyGroup (Fin 2) X x)] [Subsingleton (HomotopyGroup (Fin 2) Y y)]

theorem equivalence_left (a : SingularHomology X 3) :
    equivalence x y (singularHomologyMap (leftSection y) 3 a) = (a, 0) := by
  apply Prod.ext
  · rw [equivalence_fst, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id X) 3 a = a
    rw [singularHomologyMap_id]
    rfl
  · rw [equivalence_snd, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact constant_map_zero x y a

theorem equivalence_right (b : SingularHomology Y 3) :
    equivalence x y (singularHomologyMap (rightSection x) 3 b) = (0, b) := by
  apply Prod.ext
  · rw [equivalence_fst, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact constant_map_zero y x b
  · rw [equivalence_snd, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id Y) 3 b = b
    rw [singularHomologyMap_id]
    rfl

theorem equivalence_symm_pair (a : SingularHomology X 3) (b : SingularHomology Y 3) :
    (equivalence x y).symm (a, b) =
      singularHomologyMap (leftSection y) 3 a + singularHomologyMap (rightSection x) 3 b := by
  apply (equivalence x y).injective
  rw [LinearEquiv.apply_symm_apply, map_add, equivalence_left, equivalence_right]
  simp

theorem map_product_class (f : C(X × Y, Z)) (a : SingularHomology X 3)
    (b : SingularHomology Y 3) :
    singularHomologyMap f 3 ((equivalence x y).symm (a, b)) =
      singularHomologyMap (f.comp (leftSection y)) 3 a +
        singularHomologyMap (f.comp (rightSection x)) 3 b := by
  rw [equivalence_symm_pair, map_add, singularHomologyMap_comp, singularHomologyMap_comp]
  rfl

end NoExoticSixSphere.ProductThirdHomology

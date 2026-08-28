import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso
import Wikipedia.NoExoticSixSphere.ProductHomotopyEquiv
import Wikipedia.NoExoticSixSphere.ProductHomotopyConnectivity

/-!
# Second homology of products of simply connected spaces

The equivalence is obtained from the native second Hurewicz maps and
the actual product projections on based homotopy groups.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.ProductSecondHomology

open SingularMayerVietoris SecondHurewicz.SimplyConnected
open NoExoticSixSphere

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X) (y : Y)

local instance : SimplyConnectedSpace (X × Y) := HigherHomotopy.simplyConnected_product

def equivalence : SingularHomology (X × Y) 2 ≃ₗ[ℤ]
    (SingularHomology X 2 × SingularHomology Y 2) := by
  let e₁ : Additive (HomotopyGroup (Fin 2) (X × Y) (x, y)) ≃ₗ[ℤ]
      (Additive (HomotopyGroup (Fin 2) X x) × Additive (HomotopyGroup (Fin 2) Y y)) :=
    ((HigherHomotopy.productMulEquiv (N := Fin 2) (x := x) (y := y)).toAdditive.trans
      (AddEquiv.prodAdditive _ _)).toIntLinearEquiv
  let e₂ : (Additive (HomotopyGroup (Fin 2) X x) × Additive (HomotopyGroup (Fin 2) Y y)) ≃ₗ[ℤ]
      (SingularHomology X 2 × SingularHomology Y 2) :=
    ((hurewiczLinearEquiv x).toAddEquiv.prodCongr
      (hurewiczLinearEquiv y).toAddEquiv).toIntLinearEquiv
  exact (hurewiczLinearEquiv (x, y)).symm.trans (e₁.trans e₂)

end Wikipedia.HopfProblem.OrbitPair.ProductSecondHomology

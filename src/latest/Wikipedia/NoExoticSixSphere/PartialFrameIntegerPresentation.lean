import Wikipedia.NoExoticSixSphere.PartialFrameThirdHomologyPresentation
import Wikipedia.NoExoticSixSphere.PartialFrameThirdHurewicz
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# Integral-coordinate presentations of the actual third frame groups

The actual sphere-fiber top homology is marked by the proved singular sphere
calculation. Thus the third homology of `Space 5 2` is a quotient of `ℤ × ℤ`
by the image of the actual reduced Mayer–Vietoris map. The native third
homotopy group has the same presentation through the proved Hurewicz map.
The relation submodule is defined from those actual maps, not by its expected
index; computing that index is a remaining obligation.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

def fiberThirdHomologyEquiv : SingularHomology (Space 4 1) 3 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv (OneColumn.homeomorph (n := 4) (spherePole 0)) 3).trans
    (Wikipedia.HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2)

def pairThirdHomologyEquiv :
    (SingularHomology (Space 4 1) 3 × SingularHomology (Space 4 1) 3) ≃ₗ[ℤ] ℤ × ℤ :=
  (fiberThirdHomologyEquiv.toAddEquiv.prodCongr
    fiberThirdHomologyEquiv.toAddEquiv).toIntLinearEquiv

variable (v : UnitSphere (Vector 2))

def integerRelations : Submodule ℤ (ℤ × ℤ) :=
  (LinearMap.range (reducedLeftMap 3 v 3)).map pairThirdHomologyEquiv.toLinearMap

def integerThirdHomologyPresentation :
    ((ℤ × ℤ) ⧸ integerRelations v) ≃ₗ[ℤ] SingularHomology (Space 5 2) 3 :=
  (Submodule.Quotient.equiv (LinearMap.range (reducedLeftMap 3 v 3))
    (integerRelations v) pairThirdHomologyEquiv rfl).symm.trans (thirdHomologyPresentation v)

theorem integerThirdHomologyPresentation_mk (b : ℤ × ℤ) :
    integerThirdHomologyPresentation v (Submodule.Quotient.mk b) =
      reducedRightMap 3 v 3 (pairThirdHomologyEquiv.symm b) := by
  change thirdHomologyPresentation v
    (Submodule.Quotient.mk (pairThirdHomologyEquiv.symm b)) = _
  exact thirdHomologyPresentation_mk v _

def thirdHomotopyPresentation (a : Space 5 2) :
    Additive (HomotopyGroup (Fin 3) (Space 5 2) a) ≃ₗ[ℤ] ((ℤ × ℤ) ⧸ integerRelations v) :=
  (thirdHurewiczLinearEquiv (c := 3) (by decide) 2 a).trans
    (integerThirdHomologyPresentation v).symm

end NoExoticSixSphere.Stiefel.ColumnHomology

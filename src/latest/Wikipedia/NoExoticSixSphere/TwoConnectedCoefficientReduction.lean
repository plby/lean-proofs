import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSequence

/-!
# Actual coefficient reduction in middle degree for a two-connected space

The native second Hurewicz isomorphism proves that the preceding integral
homology group is zero. The already constructed coefficient exact sequence
then identifies actual mod-two third homology with the quotient of actual
integral third homology by twice that group.
-/

noncomputable section

open Function
open scoped Topology

namespace NoExoticSixSphere.TwoConnectedCoefficients

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] Submodule.Quotient.module

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (x : X) [hπ₂ : Subsingleton (π_ 2 X x)]

include x hπ₂

theorem secondHomology_subsingleton : Subsingleton (SingularHomology X 2) := by
  let e := Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected.hurewiczLinearEquiv x
  exact e.surjective.subsingleton

theorem secondHomology_torsionFree : Module.IsTorsionFree ℤ (SingularHomology X 2) := by
  let : Subsingleton (SingularHomology X 2) := secondHomology_subsingleton x
  infer_instance

def middleQuotientEquiv :
    (SingularHomology X 3 ⧸ scalarImage 2 (SingularHomology X 3)) ≃ₗ[ℤ] ModHomology 2 X 3 := by
  let : Module.IsTorsionFree ℤ (SingularHomology X (3 - 1)) := secondHomology_torsionFree x
  exact modHomologyQuotientEquiv 2 (by decide) X 3

theorem middleQuotientEquiv_mk (a : SingularHomology X 3) :
    middleQuotientEquiv x (Submodule.Quotient.mk a) = reductionHomologyMap 2 X 3 a := rfl

theorem middleQuotientEquiv_symm_reduction (a : SingularHomology X 3) :
    (middleQuotientEquiv x).symm (reductionHomologyMap 2 X 3 a) = Submodule.Quotient.mk a := by
  apply (middleQuotientEquiv x).injective
  rw [LinearEquiv.apply_symm_apply, middleQuotientEquiv_mk]

theorem middleReduction_surjective : Surjective (reductionHomologyMap 2 X 3) := by
  let : Module.IsTorsionFree ℤ (SingularHomology X 2) := secondHomology_torsionFree x
  exact reductionHomologyMap_surjective_succ 2 (by decide) X 2

end NoExoticSixSphere.TwoConnectedCoefficients

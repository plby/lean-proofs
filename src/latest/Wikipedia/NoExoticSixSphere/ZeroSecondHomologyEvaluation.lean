import Wikipedia.NoExoticSixSphere.NativeModTwoMiddleEvaluation

/-!
# Native middle evaluation without a connectedness assumption

Vanishing of the actual second integral homology suffices for the
coefficient quotient and cochain evaluation comparisons. In particular
the construction applies to a disjoint union of two-connected spaces.
Its values are the original cochain evaluations, and it agrees with the
previous basepoint-based construction whenever that construction applies.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients
open scoped Topology

namespace NoExoticSixSphere.ZeroSecondHomologyEvaluation

attribute [local instance] Submodule.Quotient.module

variable (X : Type) [TopologicalSpace X] [Subsingleton (SingularHomology X 2)]

def quotientEquiv :
    (SingularHomology X 3 ⧸ scalarImage 2 (SingularHomology X 3)) ≃ₗ[ℤ] ModHomology 2 X 3 :=
  modHomologyQuotientEquiv 2 (by decide) X 3

theorem quotientEquiv_mk (b : SingularHomology X 3) :
    quotientEquiv X (Submodule.Quotient.mk b) = reductionHomologyMap 2 X 3 b := rfl

theorem reduction_surjective : Function.Surjective (reductionHomologyMap 2 X 3) :=
  reductionHomologyMap_surjective_succ 2 (by decide) X 2

def evaluation : ModTwoCapProduct.Cohomology X 3 →ₗ[ℤ] (ModHomology 2 X 3 →ₗ[ℤ] ZMod 2) :=
  (ModTwoFunctional.transportEquiv (SingularHomology X 3) (quotientEquiv X)).toLinearMap.comp
    (SingularModTwoEvaluation.evaluation X 3)

theorem evaluation_reduction (a : ModTwoCapProduct.Cohomology X 3)
    (b : SingularHomology X 3) :
    evaluation X a (reductionHomologyMap 2 X 3 b) = SingularModTwoEvaluation.evaluation X 3 a b :=
  ModTwoFunctional.transportEquiv_mk (SingularHomology X 3) (quotientEquiv X)
    (SingularModTwoEvaluation.evaluation X 3 a) b

def evaluationEquiv : ModTwoCapProduct.Cohomology X 3 ≃ₗ[ℤ]
    (ModHomology 2 X 3 →ₗ[ℤ] ZMod 2) :=
  (SingularModTwoEvaluation.evaluationSuccEquiv X 2).trans
    (ModTwoFunctional.transportEquiv (SingularHomology X 3) (quotientEquiv X))

theorem evaluationEquiv_toLinearMap : (evaluationEquiv X).toLinearMap = evaluation X := rfl

theorem evaluation_bijective : Function.Bijective (evaluation X) := (evaluationEquiv X).bijective

theorem evaluation_cocycle_reduction (a : ModTwoCapProduct.Cocycle X 3)
    (b : ModuleHomology.Cycle (singularComplex X) 3) :
    evaluation X (SingularCohomologyFree.cocycleClass (ModTwoCapProduct.cochainComplex X) 3 a)
        (reductionHomologyMap 2 X 3 (ModuleHomology.cycleClass (singularComplex X) 3 b)) =
      ModTwoCohomologyEvaluation.cochainValue (singularComplex X) 3 a b.val :=
  (evaluation_reduction X _ _).trans
    (ModTwoCohomologyEvaluation.evaluation_cocycle_cycle (singularComplex X) 3 a b)

theorem evaluation_eq_connected [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] : evaluation X = NativeModTwoMiddleEvaluation.evaluation x := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := reduction_surjective X b
  exact (evaluation_reduction X a b).trans
    (NativeModTwoMiddleEvaluation.evaluation_reduction x a b).symm

variable {Y : Type} [TopologicalSpace Y] [Subsingleton (SingularHomology Y 2)]

theorem evaluation_naturality (f : C(X, Y)) (a : ModTwoCapProduct.Cohomology Y 3)
    (b : ModHomology 2 X 3) :
    evaluation X (ModTwoCapProduct.cohomologyPullback f 3 a) b =
      evaluation Y a (modHomologyMap 2 f 3 b) := by
  obtain ⟨b, rfl⟩ := reduction_surjective X b
  rw [evaluation_reduction, modHomologyMap_reduction, evaluation_reduction]
  exact ModTwoCohomologyEvaluation.evaluation_naturality
    (K := singularComplex X) (L := singularComplex Y) 3
    (RelativeCoefficients.spaceMap (ModuleCat.of ℤ ℤ) f) a b

end NoExoticSixSphere.ZeroSecondHomologyEvaluation

import Wikipedia.NoExoticSixSphere.ModTwoFunctionalQuotient
import Wikipedia.NoExoticSixSphere.SingularModTwoEvaluation
import Wikipedia.NoExoticSixSphere.ModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.RelativeCoefficientPairMaps
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality

/-!
# Actual cohomology evaluation on native mod-two middle homology

The original coefficient exact sequence identifies native middle
homology with the integral scalar quotient. Original mod-two-valued
cochain evaluation factors uniquely through this actual quotient.
Its evaluation formula, bijectivity, basepoint independence, and
naturality retain the original cochains and coefficient reduction.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients
open scoped Topology

namespace NoExoticSixSphere.NativeModTwoMiddleEvaluation

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (x : X) [Subsingleton (π_ 2 X x)]

/-- Original cochain evaluation, descended through the actual coefficient reduction quotient. -/
def evaluation : ModTwoCapProduct.Cohomology X 3 →ₗ[ℤ] (ModHomology 2 X 3 →ₗ[ℤ] ZMod 2) :=
  (ModTwoFunctional.transportEquiv (SingularHomology X 3)
    (TwoConnectedCoefficients.middleQuotientEquiv x)).toLinearMap.comp
      (SingularModTwoEvaluation.evaluation X 3)

/-- On an actual reduced integral class, the value is its original cochain evaluation. -/
theorem evaluation_reduction (a : ModTwoCapProduct.Cohomology X 3)
    (b : SingularHomology X 3) :
    evaluation x a (reductionHomologyMap 2 X 3 b) = SingularModTwoEvaluation.evaluation X 3 a b :=
  ModTwoFunctional.transportEquiv_mk (SingularHomology X 3)
    (TwoConnectedCoefficients.middleQuotientEquiv x) (SingularModTwoEvaluation.evaluation X 3 a) b

/-- Both original representatives retain literal evaluation of the integral cocycle on its cycle. -/
theorem evaluation_cocycle_reduction (a : ModTwoCapProduct.Cocycle X 3)
    (b : ModuleHomology.Cycle (singularComplex X) 3) :
    evaluation x (SingularCohomologyFree.cocycleClass (ModTwoCapProduct.cochainComplex X) 3 a)
        (reductionHomologyMap 2 X 3 (ModuleHomology.cycleClass (singularComplex X) 3 b)) =
      ModTwoCohomologyEvaluation.cochainValue (singularComplex X) 3 a b.val :=
  (evaluation_reduction x _ _).trans
    (ModTwoCohomologyEvaluation.evaluation_cocycle_cycle (singularComplex X) 3 a b)

/-- The equivalence's forward map is precisely the original descended evaluation. -/
def evaluationEquiv : ModTwoCapProduct.Cohomology X 3 ≃ₗ[ℤ]
    (ModHomology 2 X 3 →ₗ[ℤ] ZMod 2) :=
  (SingularModTwoEvaluation.middleEquiv X x).trans
    (ModTwoFunctional.transportEquiv (SingularHomology X 3)
      (TwoConnectedCoefficients.middleQuotientEquiv x))

theorem evaluationEquiv_toLinearMap : (evaluationEquiv x).toLinearMap = evaluation x := rfl

/-- Original evaluation is bijective on the actual two-connected middle homology group. -/
theorem evaluation_bijective : Function.Bijective (evaluation x) := (evaluationEquiv x).bijective

/-- The auxiliary basepoint used to prove second homology vanishing does not change evaluation. -/
theorem evaluation_basepoint_independent (y : X) [Subsingleton (π_ 2 X y)] :
    evaluation x = evaluation y := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective x b
  exact (evaluation_reduction x a b).trans (evaluation_reduction y a b).symm

variable {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (y : Y) [Subsingleton (π_ 2 Y y)]

/-- Actual cohomology pullback and native homology pushforward preserve the descended pairing. -/
theorem evaluation_naturality (f : C(X, Y)) (a : ModTwoCapProduct.Cohomology Y 3)
    (b : ModHomology 2 X 3) :
    evaluation x (ModTwoCapProduct.cohomologyPullback f 3 a) b =
      evaluation y a (modHomologyMap 2 f 3 b) := by
  obtain ⟨b, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective x b
  rw [evaluation_reduction, modHomologyMap_reduction, evaluation_reduction]
  exact ModTwoCohomologyEvaluation.evaluation_naturality
    (K := singularComplex X) (L := singularComplex Y) 3
    (RelativeCoefficients.spaceMap (ModuleCat.of ℤ ℤ) f) a b

end NoExoticSixSphere.NativeModTwoMiddleEvaluation

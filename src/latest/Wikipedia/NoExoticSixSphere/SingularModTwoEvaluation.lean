import Wikipedia.NoExoticSixSphere.ModTwoCohomologyEvaluationInjective
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocal
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction

/-!
# Original singular mod-two evaluation in middle degree

The literal simplex basis proves projectivity of the outgoing images.
The actual mod-two cochain evaluation is consequently onto in every
degree and is injective when the preceding integral homology is
projective. For a two-connected space, native second Hurewicz proves
the required vanishing in degree two, giving the actual middle
evaluation equivalence without a homology or duality hypothesis.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris FirstHurewicz
open scoped Topology

namespace NoExoticSixSphere.SingularModTwoEvaluation

variable (X : Type) [TopologicalSpace X]

/-- Evaluation of the original mod-two cohomology on actual integral homology. -/
abbrev evaluation (p : ℕ) :
    ModTwoCapProduct.Cohomology X p →ₗ[ℤ] (SingularHomology X p →ₗ[ℤ] ZMod 2) :=
  ModTwoCohomologyEvaluation.evaluation (singularComplex X) p

/-- Freeness of the actual simplex chains proves surjectivity of the original evaluation. -/
theorem evaluation_surjective (p : ℕ) : Function.Surjective (evaluation X p) := by
  let (k : ℕ) : Module.Free ℤ ((singularComplex X).X k) :=
    Module.Free.of_basis (chainBasis X k)
  let := SingularCohomologyFree.LocalEvaluation.outgoingImage_projective (singularComplex X) p
  exact ModTwoCohomologyEvaluation.evaluation_surjective_of_outgoing_projective
    (singularComplex X) p

/-- Only projectivity of the actual preceding integral homology is needed for injectivity. -/
theorem evaluation_succ_injective (p : ℕ) [Module.Projective ℤ (SingularHomology X p)] :
    Function.Injective (evaluation X (p + 1)) := by
  let (k : ℕ) : Module.Free ℤ ((singularComplex X).X k) :=
    Module.Free.of_basis (chainBasis X k)
  let := SingularCohomologyFree.LocalEvaluation.outgoingImage_projective (singularComplex X) p
  exact ModTwoCohomologyEvaluation.evaluation_succ_injective_of_outgoing_projective
    (singularComplex X) p

/-- The actual evaluation equivalence with the preceding-degree hypothesis made explicit. -/
def evaluationSuccEquiv (p : ℕ) [Module.Projective ℤ (SingularHomology X p)] :
    ModTwoCapProduct.Cohomology X (p + 1) ≃ₗ[ℤ] (SingularHomology X (p + 1) →ₗ[ℤ] ZMod 2) :=
  LinearEquiv.ofBijective (evaluation X (p + 1))
    ⟨evaluation_succ_injective X p, evaluation_surjective X (p + 1)⟩

variable [SimplyConnectedSpace X] (x : X) [h₂ : Subsingleton (π_ 2 X x)]

include x h₂ in
/-- Native second Hurewicz supplies the middle evaluation hypothesis, rather than assuming it. -/
theorem middle_bijective : Function.Bijective (evaluation X 3) := by
  let := TwoConnectedCoefficients.secondHomology_subsingleton x
  exact ⟨evaluation_succ_injective X 2, evaluation_surjective X 3⟩

/-- Genuine middle cohomology is the actual mod-two-valued evaluation dual of integral homology. -/
def middleEquiv : ModTwoCapProduct.Cohomology X 3 ≃ₗ[ℤ]
    (SingularHomology X 3 →ₗ[ℤ] ZMod 2) :=
  LinearEquiv.ofBijective (evaluation X 3) (middle_bijective X x)

theorem middleEquiv_toLinearMap : (middleEquiv X x).toLinearMap = evaluation X 3 := rfl

end NoExoticSixSphere.SingularModTwoEvaluation

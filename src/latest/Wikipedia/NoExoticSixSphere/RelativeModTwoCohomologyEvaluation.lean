import Wikipedia.NoExoticSixSphere.ModTwoCohomologyEvaluationInjective
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainSequence

/-!
# Universal-coefficient evaluation on actual relative mod-two cohomology

Freeness of the native relative chains is proved, not assumed. Original
evaluation is therefore surjective in every degree. In degree `n + 1`
its injectivity uses only projectivity of the actual preceding integral
relative homology group. The equivalence retains this evaluation map.
-/

noncomputable section

open Wikipedia.HopfProblem

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The canonical evaluation of actual relative cohomology on original integral homology. -/
abbrev evaluation (p : ℕ) : Cohomology U p →ₗ[ℤ]
    (RelativeSingularHomology.Homology U p →ₗ[ℤ] ZMod 2) :=
  ModTwoCohomologyEvaluation.evaluation (RelativeSingularHomology.complex U) p

/-- Every functional is realized; no relative-chain freeness hypothesis is supplied. -/
theorem evaluation_surjective (p : ℕ) : Function.Surjective (evaluation U p) := by
  let := RelativeSingularHomology.outgoingImage_projective U p
  exact ModTwoCohomologyEvaluation.evaluation_surjective_of_outgoing_projective
    (RelativeSingularHomology.complex U) p

theorem evaluation_succ_injective (p : ℕ)
    [Module.Projective ℤ (RelativeSingularHomology.Homology U p)] :
    Function.Injective (evaluation U (p + 1)) := by
  let := RelativeSingularHomology.outgoingImage_projective U p
  exact ModTwoCohomologyEvaluation.evaluation_succ_injective_of_outgoing_projective
    (RelativeSingularHomology.complex U) p

/-- The degree-zero equivalence requires no homology hypothesis. -/
def evaluationZeroEquiv : Cohomology U 0 ≃ₗ[ℤ]
    (RelativeSingularHomology.Homology U 0 →ₗ[ℤ] ZMod 2) :=
  ModTwoCohomologyEvaluation.evaluationZeroEquiv (RelativeSingularHomology.complex U)

/-- Local universal coefficients, with the original evaluation as its forward map. -/
def evaluationSuccEquiv (p : ℕ)
    [Module.Projective ℤ (RelativeSingularHomology.Homology U p)] :
    Cohomology U (p + 1) ≃ₗ[ℤ] (RelativeSingularHomology.Homology U (p + 1) →ₗ[ℤ] ZMod 2) :=
  LinearEquiv.ofBijective (evaluation U (p + 1))
    ⟨evaluation_succ_injective U p, evaluation_surjective U (p + 1)⟩

theorem evaluationSuccEquiv_toLinearMap (p : ℕ)
    [Module.Projective ℤ (RelativeSingularHomology.Homology U p)] :
    (evaluationSuccEquiv U p).toLinearMap = evaluation U (p + 1) := rfl

end NoExoticSixSphere.RelativeModTwoCochains

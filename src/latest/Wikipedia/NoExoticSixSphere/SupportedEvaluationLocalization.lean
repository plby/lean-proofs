import Wikipedia.NoExoticSixSphere.FiniteSupportEvaluation
import Wikipedia.NoExoticSixSphere.RelativeModTwoEvaluationReduction

/-!
# Original support localization and evaluation commute with coefficient reduction

The native coefficient-change square commutes with the original
absolute-to-relative projection. Dual evaluation naturality then says
that evaluating a supported cohomology class on an absolute integral
class is the same as evaluating on its actual relative localization.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {X : Type} [TopologicalSpace X]

/-- Original absolute-to-relative homology localization commutes with native coefficient change. -/
theorem fromAbsolute_reduction (p : ℕ) (K : Set X) (k : ℕ) (b : SingularHomology X k) :
    fromAbsolute (ModuleCat.of ℤ (ZMod p)) K k (reductionHomologyMap p X k b) =
      RelativeCoefficients.reductionMap p Kᶜ k (fromAbsolute (ModuleCat.of ℤ ℤ) K k b) := by
  have he := congrArg (fun f => homologyLinearMap f k)
    (RelativeCoefficients.projection_change (reductionCoefficient p) Kᶜ)
  rw [homologyLinearMap_comp, homologyLinearMap_comp] at he
  exact (LinearMap.congr_fun he b).symm

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- Original evaluation can be computed after localizing the actual integral homology class. -/
theorem value_eq_relative (K : Set X) (p : ℕ) (b : SingularHomology X p)
    (a : Cohomology K p) : value K p b a = RelativeModTwoCochains.evaluation Kᶜ p a
      (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) K p b) :=
  ModTwoCohomologyEvaluation.evaluation_naturality
    (K := singularComplex X) (L := RelativeSingularHomology.complex Kᶜ) p
    (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) Kᶜ) a b

end NoExoticSixSphere.SupportedModTwoCohomology

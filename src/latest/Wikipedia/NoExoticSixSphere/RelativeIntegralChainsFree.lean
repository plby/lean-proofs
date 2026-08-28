import Wikipedia.NoExoticSixSphere.RelativeIntegralChainSplitting
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocal

/-!
# Freeness of the actual relative integral chain groups

The constructed section embeds the original relative chain group in the
original free ambient chain group. Its image is an actual integral
submodule, so the proved arbitrary-rank submodule theorem gives freeness.
The images of the relative differential are consequently projective.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The native relative integral chain module is free in every degree. -/
theorem chains_free (n : ℕ) : Module.Free ℤ ((complex U).X n) := by
  let : Module.Free ℤ (Chains X n) := Module.Free.of_basis (chainBasis X n)
  let s := quotientSection U n
  let : Module ℤ (LinearMap.range s) := (LinearMap.range s).module
  let : Module.Free ℤ (LinearMap.range s) :=
    SingularCohomologyFreeEvaluation.submodule_free_int (LinearMap.range s)
  exact Module.Free.of_equiv (LinearEquiv.ofInjective s (quotientSection_injective U n)).symm

/-- Actual relative boundary images are projective, without a homology assumption. -/
theorem outgoingImage_projective (n : ℕ) :
    Module.Projective ℤ (SingularCohomologyFree.LocalEvaluation.OutgoingImage (complex U) n) := by
  let (k : ℕ) : Module.Free ℤ ((complex U).X k) := chains_free U k
  exact SingularCohomologyFree.LocalEvaluation.outgoingImage_projective (complex U) n

end NoExoticSixSphere.RelativeSingularHomology

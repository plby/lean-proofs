import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalFree
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSurjective
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalInjective

/-!
# Local universal coefficients for actual integral cohomology

For a chain complex of free integral modules, canonical cohomology
evaluation is always surjective.  In degree `n + 1` it is bijective if
the actual homology in degree `n` alone is projective.  Degree zero
requires neither freeness of chains nor any homology hypothesis.

Every equivalence below has the original `cohomologyEvaluation` as its
literal forward linear map.  These are not independent identifications
of abstract groups by rank or a globally assumed formality theorem.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- Degree-zero actual cohomology is its canonical evaluation dual, with no extra hypotheses. -/
def cohomologyEvaluationZeroEquiv : Cohomology K 0 ≃ₗ[ℤ] (K.homology 0 →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (cohomologyEvaluation K 0)
    ⟨cohomologyEvaluation_zero_injective K, cohomologyEvaluation_zero_surjective K⟩

@[simp] theorem cohomologyEvaluationZeroEquiv_toLinearMap :
    (cohomologyEvaluationZeroEquiv K).toLinearMap = cohomologyEvaluation K 0 := rfl

@[simp] theorem cohomologyEvaluationZeroEquiv_apply (a : Cohomology K 0) :
    cohomologyEvaluationZeroEquiv K a = cohomologyEvaluation K 0 a := rfl

section FreeChains

variable [∀ k, Module.Free ℤ (K.X k)]

/-- An actual outgoing image is projective because it is a submodule
of a free integral chain module. -/
theorem outgoingImage_projective (n : ℕ) : Module.Projective ℤ (OutgoingImage K n) :=
  SingularCohomologyFreeEvaluation.submodule_projective_int (OutgoingImage K n)

/-- Every actual homology functional is represented by a genuine cocycle. -/
theorem cohomologyEvaluation_surjective (n : ℕ) :
    Function.Surjective (cohomologyEvaluation K n) := by
  have := outgoingImage_projective K n
  exact cohomologyEvaluation_surjective_of_outgoing_projective K n

/-- Only the preceding homology needs to be projective for injective evaluation. -/
theorem cohomologyEvaluation_succ_injective (n : ℕ) [Module.Projective ℤ (K.homology n)] :
    Function.Injective (cohomologyEvaluation K (n + 1)) := by
  have := outgoingImage_projective K n
  exact cohomologyEvaluation_succ_injective_of_outgoing_projective K n

/-- The local integral universal-coefficient theorem for the original evaluation map. -/
theorem cohomologyEvaluation_succ_bijective (n : ℕ) [Module.Projective ℤ (K.homology n)] :
    Function.Bijective (cohomologyEvaluation K (n + 1)) :=
  ⟨cohomologyEvaluation_succ_injective K n, cohomologyEvaluation_surjective K (n + 1)⟩

/-- The actual evaluation equivalence, assuming projectivity of just the preceding homology. -/
def cohomologyEvaluationSuccEquiv (n : ℕ) [Module.Projective ℤ (K.homology n)] :
    Cohomology K (n + 1) ≃ₗ[ℤ] (K.homology (n + 1) →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (cohomologyEvaluation K (n + 1))
    (cohomologyEvaluation_succ_bijective K n)

@[simp] theorem cohomologyEvaluationSuccEquiv_toLinearMap (n : ℕ)
    [Module.Projective ℤ (K.homology n)] :
    (cohomologyEvaluationSuccEquiv K n).toLinearMap = cohomologyEvaluation K (n + 1) := rfl

@[simp] theorem cohomologyEvaluationSuccEquiv_apply (n : ℕ)
    [Module.Projective ℤ (K.homology n)] (a : Cohomology K (n + 1)) :
    cohomologyEvaluationSuccEquiv K n a = cohomologyEvaluation K (n + 1) a := rfl

end FreeChains

section Naturality

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
  [∀ k, Module.Free ℤ (K.X k)] [∀ k, Module.Free ℤ (L.X k)]
  (f : K ⟶ L) (n : ℕ)
  [Module.Projective ℤ (K.homology n)] [Module.Projective ℤ (L.homology n)]

/-- The local equivalence still preserves the original pullback–pushforward pairing. -/
theorem cohomologyEvaluationSuccEquiv_naturality (a : Cohomology L (n + 1))
    (b : K.homology (n + 1)) :
    cohomologyEvaluationSuccEquiv K n
        ((HomologicalComplex.homologyMap (dualMap f) (n + 1)).hom a) b =
      cohomologyEvaluationSuccEquiv L n a
        ((HomologicalComplex.homologyMap f (n + 1)).hom b) :=
  cohomologyEvaluation_naturality f (n + 1) a b

end Naturality

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

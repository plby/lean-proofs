import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocal
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Native singular universal coefficients from the preceding homology only

The original singular evaluation map is surjective for every space in
every degree.  In degree `n + 1`, its injectivity needs projectivity of
`Hₙ(X; ℤ)` only.  Freeness of every actual singular-chain module is
supplied by its literal simplex basis, not imposed as a hypothesis.
Degree zero has its own completely unconditional equivalence.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

open SingularMayerVietoris

variable (X : Type) [TopologicalSpace X]

/-- Every integral homology functional has a genuine singular-cohomology representative. -/
theorem singularEvaluation_surjective (n : ℕ) :
    Function.Surjective (singularEvaluation X n) := by
  let (k : ℕ) : Module.Free ℤ ((FirstHurewicz.singularComplex X).X k) :=
    Module.Free.of_basis (FirstHurewicz.chainBasis X k)
  exact cohomologyEvaluation_surjective (FirstHurewicz.singularComplex X) n

/-- Degree-zero singular evaluation is unconditionally an equivalence. -/
def singularEvaluationZeroEquiv :
    SingularCohomology X 0 ≃ₗ[ℤ] (SingularHomology X 0 →ₗ[ℤ] ℤ) :=
  cohomologyEvaluationZeroEquiv (FirstHurewicz.singularComplex X)

@[simp] theorem singularEvaluationZeroEquiv_toLinearMap :
    (singularEvaluationZeroEquiv X).toLinearMap = singularEvaluation X 0 := rfl

@[simp] theorem singularEvaluationZeroEquiv_apply (a : SingularCohomology X 0) :
    singularEvaluationZeroEquiv X a = singularEvaluation X 0 a := rfl

/-- Local injectivity depends on the preceding singular homology and no other degree. -/
theorem singularEvaluation_succ_injective (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)] :
    Function.Injective (singularEvaluation X (n + 1)) := by
  let (k : ℕ) : Module.Free ℤ ((FirstHurewicz.singularComplex X).X k) :=
    Module.Free.of_basis (FirstHurewicz.chainBasis X k)
  exact cohomologyEvaluation_succ_injective (FirstHurewicz.singularComplex X) n

/-- The original singular evaluation is bijective under the single preceding-degree hypothesis. -/
theorem singularEvaluation_succ_bijective (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)] :
    Function.Bijective (singularEvaluation X (n + 1)) :=
  ⟨singularEvaluation_succ_injective X n, singularEvaluation_surjective X (n + 1)⟩

/-- The genuine singular-cohomology evaluation equivalence from local universal coefficients. -/
def singularEvaluationSuccEquiv (n : ℕ) [Module.Projective ℤ (SingularHomology X n)] :
    SingularCohomology X (n + 1) ≃ₗ[ℤ] (SingularHomology X (n + 1) →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (singularEvaluation X (n + 1))
    (singularEvaluation_succ_bijective X n)

@[simp] theorem singularEvaluationSuccEquiv_toLinearMap (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)] :
    (singularEvaluationSuccEquiv X n).toLinearMap = singularEvaluation X (n + 1) := rfl

@[simp] theorem singularEvaluationSuccEquiv_apply (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)] (a : SingularCohomology X (n + 1)) :
    singularEvaluationSuccEquiv X n a = singularEvaluation X (n + 1) a := rfl

/-- The inverse is characterized by its actual pairing with every homology class. -/
theorem singularEvaluationSuccEquiv_symm_evaluate (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)]
    (φ : SingularHomology X (n + 1) →ₗ[ℤ] ℤ) (b : SingularHomology X (n + 1)) :
    singularEvaluation X (n + 1) ((singularEvaluationSuccEquiv X n).symm φ) b = φ b :=
  LinearMap.congr_fun ((singularEvaluationSuccEquiv X n).apply_symm_apply φ) b

/-- Equality of actual cohomology classes can be detected by evaluation,
without hypotheses on any other homology degree. -/
theorem singularCohomology_succ_eq_iff_evaluation (n : ℕ)
    [Module.Projective ℤ (SingularHomology X n)]
    (a b : SingularCohomology X (n + 1)) :
    a = b ↔ ∀ z : SingularHomology X (n + 1),
      singularEvaluation X (n + 1) a z = singularEvaluation X (n + 1) b z := by
  constructor
  · rintro rfl z
    rfl
  · intro h
    exact (singularEvaluation_succ_injective X n) (LinearMap.ext h)

section Naturality

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (n : ℕ)
  [Module.Projective ℤ (SingularHomology X n)]
  [Module.Projective ℤ (SingularHomology Y n)]

/-- Local universal coefficients preserves the actual cohomological pullback pairing. -/
theorem singularEvaluationSuccEquiv_naturality (a : SingularCohomology Y (n + 1))
    (b : SingularHomology X (n + 1)) :
    singularEvaluationSuccEquiv X n (singularCohomologyPullback f (n + 1) a) b =
      singularEvaluationSuccEquiv Y n a (singularHomologyMap f (n + 1) b) :=
  singularEvaluation_naturality f (n + 1) a b

/-- The inverse sends precomposition with actual homology maps to the actual cohomology pullback. -/
theorem singularEvaluationSuccEquiv_symm_naturality
    (φ : SingularHomology Y (n + 1) →ₗ[ℤ] ℤ) :
    singularCohomologyPullback f (n + 1) ((singularEvaluationSuccEquiv Y n).symm φ) =
      (singularEvaluationSuccEquiv X n).symm (φ.comp (singularHomologyMap f (n + 1))) := by
  apply (singularEvaluationSuccEquiv X n).injective
  ext b
  rw [singularEvaluationSuccEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  rfl

end Naturality

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

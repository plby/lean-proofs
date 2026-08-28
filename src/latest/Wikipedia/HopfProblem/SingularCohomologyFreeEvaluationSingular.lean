import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationIso
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Native singular cohomology and the actual integral evaluation isomorphism

The pairing in this file is defined on the actual singular cochain
complex, the actual singular homology objects, and their actual maps.
It is natural for every continuous map.  When all actual integral
homology groups are projective, the already proved chain/cochain
homotopy comparison proves that this pairing is a linear equivalence.
Singular-chain projectivity follows from its genuine simplex basis and
is not an additional input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFree

open SingularMayerVietoris

variable (X : Type) [TopologicalSpace X]

/-- The canonical evaluation pairing for actual integral singular cohomology. -/
def singularEvaluation (n : ℕ) :
    SingularCohomology X n →ₗ[ℤ] (SingularHomology X n →ₗ[ℤ] ℤ) :=
  cohomologyEvaluation (FirstHurewicz.singularComplex X) n

/-- On actual cycle representatives the pairing is literal evaluation of the original cochain. -/
theorem singularEvaluation_cocycle_cycle (n : ℕ)
    (c : Cocycle (singularCochainComplex X) n)
    (z : ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    singularEvaluation X n (cocycleClass (singularCochainComplex X) n c)
      (ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n z) = c.val z.val :=
  cohomologyEvaluation_cocycle_cycle (FirstHurewicz.singularComplex X) n c z

section Naturality

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual cohomological pullback is the dual of actual homological pushforward under evaluation. -/
theorem singularEvaluation_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularCohomology Y n) (b : SingularHomology X n) :
    singularEvaluation X n (singularCohomologyPullback f n a) b =
      singularEvaluation Y n a (singularHomologyMap f n b) :=
  cohomologyEvaluation_naturality (FirstHurewicz.singularChainMap f) n a b

end Naturality

variable [∀ n, Module.Projective ℤ (SingularHomology X n)]

/-- The actual integral universal-coefficient equivalence in the projective-homology case. -/
def singularEvaluationEquiv (n : ℕ) :
    SingularCohomology X n ≃ₗ[ℤ] (SingularHomology X n →ₗ[ℤ] ℤ) := by
  letI (k : ℕ) : Module.Projective ℤ ((FirstHurewicz.singularComplex X).X k) :=
    Module.Projective.of_basis (FirstHurewicz.chainBasis X k)
  exact cohomologyEvaluationEquiv (FirstHurewicz.singularComplex X) n

@[simp] theorem singularEvaluationEquiv_apply (n : ℕ) (a : SingularCohomology X n) :
    singularEvaluationEquiv X n a = singularEvaluation X n a := rfl

@[simp] theorem singularEvaluationEquiv_toLinearMap (n : ℕ) :
    (singularEvaluationEquiv X n).toLinearMap = singularEvaluation X n := rfl

/-- Every integral homology functional is represented by an actual integral cohomology class. -/
theorem singularEvaluation_bijective (n : ℕ) :
    Function.Bijective (singularEvaluation X n) :=
  (singularEvaluationEquiv X n).bijective

/-- The constructed inverse is normalized by its value on every actual homology class. -/
theorem singularEvaluationEquiv_symm_evaluate (n : ℕ)
    (φ : SingularHomology X n →ₗ[ℤ] ℤ) (b : SingularHomology X n) :
    singularEvaluation X n ((singularEvaluationEquiv X n).symm φ) b = φ b :=
  DFunLike.congr_fun ((singularEvaluationEquiv X n).apply_symm_apply φ) b

/-- Actual cohomology classes are equal precisely when they evaluate
equally on all actual cycles. -/
theorem singularCohomology_eq_iff_evaluation (n : ℕ) (a b : SingularCohomology X n) :
    a = b ↔ ∀ z : SingularHomology X n, singularEvaluation X n a z =
      singularEvaluation X n b z := by
  constructor
  · rintro rfl z
    rfl
  · intro h
    apply (singularEvaluationEquiv X n).injective
    exact LinearMap.ext h

section EquivalenceNaturality

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [∀ n, Module.Projective ℤ (SingularHomology X n)]
  [∀ n, Module.Projective ℤ (SingularHomology Y n)]

/-- The proven equivalences, not only the unbundled pairings, preserve the actual induced maps. -/
theorem singularEvaluationEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularCohomology Y n) (b : SingularHomology X n) :
    singularEvaluationEquiv X n (singularCohomologyPullback f n a) b =
      singularEvaluationEquiv Y n a (singularHomologyMap f n b) :=
  singularEvaluation_naturality f n a b

/-- Inverting the evaluation equivalence still gives the literal cohomological pullback. -/
theorem singularEvaluationEquiv_symm_naturality (f : C(X, Y)) (n : ℕ)
    (φ : SingularHomology Y n →ₗ[ℤ] ℤ) :
    singularCohomologyPullback f n ((singularEvaluationEquiv Y n).symm φ) =
      (singularEvaluationEquiv X n).symm (φ.comp (singularHomologyMap f n)) := by
  apply (singularEvaluationEquiv X n).injective
  ext b
  rw [singularEvaluationEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  rfl

end EquivalenceNaturality

end Wikipedia.HopfProblem.SingularCohomologyFree

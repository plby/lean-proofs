import Wikipedia.HopfProblem.SingularCohomologyFree
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual cohomological fixed classes and homological coinvariants

The canonical evaluation equivalence identifies fixed integral singular
cohomology classes with functionals on the actual homology coinvariants.
This is an integral statement about the genuine cochain pullback and
singular pushforward, with no rationalization or duality assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFree

section Linear

variable {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup C] [Module R C]

/-- An evaluation equivalence restricts to the dual of an actual quotient
when membership is exactly annihilation of its defining submodule. -/
def evaluationDualQuotientEquiv (e : C ≃ₗ[R] Module.Dual R M)
    (V : Submodule R C) (W : Submodule R M)
    (h : ∀ a : C, a ∈ V ↔ e a ∈ W.dualAnnihilator) :
    V ≃ₗ[R] Module.Dual R (M ⧸ W) := by
  have he : V.map e.toLinearMap = W.dualAnnihilator := by
    ext φ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).mp ha
    · intro hφ
      refine ⟨e.symm φ, ?_, e.apply_symm_apply φ⟩
      exact (h _).mpr (by simpa only [e.apply_symm_apply] using hφ)
  exact (e.ofSubmodules V W.dualAnnihilator he).trans
    W.dualQuotEquivDualAnnihilator.symm

/-- The quotient functional evaluates on a represented class by the
original evaluation pairing, including its integral normalization. -/
@[simp] theorem evaluationDualQuotientEquiv_apply_mk
    (e : C ≃ₗ[R] Module.Dual R M) (V : Submodule R C) (W : Submodule R M)
    (h : ∀ a : C, a ∈ V ↔ e a ∈ W.dualAnnihilator) (a : V) (b : M) :
    evaluationDualQuotientEquiv e V W h a (Submodule.Quotient.mk b) = e a b := rfl

end Linear

section Integer

variable {M C : Type*} [AddCommGroup M] [modM : Module ℤ M]
  [AddCommGroup C] [Module ℤ C]

/-- Integer linear functionals are additive homomorphisms, also for an
inherited integer module structure on a quotient. -/
def intDualAddHomEquiv : (M →ₗ[ℤ] ℤ) ≃+ (M →+ ℤ) where
  toFun := LinearMap.toAddMonoidHom
  invFun φ :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r x => by
        change φ (modM.smul r x) = r * φ x
        rw [int_smul_eq_zsmul, map_zsmul]
        rfl }
  left_inv φ := by ext; rfl
  right_inv φ := by ext; rfl
  map_add' _ _ := rfl

/-- The integral quotient-dual equivalence uses the canonical integer
module on its target and therefore composes with actual integer homology maps. -/
def evaluationDualQuotientEquivInt (e : C ≃ₗ[ℤ] Module.Dual ℤ M)
    (V : Submodule ℤ C) (W : Submodule ℤ M)
    (h : ∀ a : C, a ∈ V ↔ e a ∈ W.dualAnnihilator) :
    V ≃ₗ[ℤ] Module.Dual ℤ (M ⧸ W) := by
  let eA : V ≃+ ((M ⧸ W) →+ ℤ) := by
    letI : Module ℤ V := V.module
    letI : Module ℤ (M ⧸ W) := Submodule.Quotient.module W
    exact (evaluationDualQuotientEquiv e V W h).toAddEquiv.trans intDualAddHomEquiv
  exact (eA.trans (addMonoidHomLequivInt (A := M ⧸ W) (B := ℤ) ℤ).toAddEquiv).toIntLinearEquiv

@[simp] theorem evaluationDualQuotientEquivInt_apply_mk
    (e : C ≃ₗ[ℤ] Module.Dual ℤ M) (V : Submodule ℤ C) (W : Submodule ℤ M)
    (h : ∀ a : C, a ∈ V ↔ e a ∈ W.dualAnnihilator) (a : V) (b : M) :
    evaluationDualQuotientEquivInt e V W h a (Submodule.Quotient.mk b) = e a b := rfl

end Integer

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The fixed submodule for the actual singular-cohomology pullback. -/
def singularCohomologyFixed (f : C(X, X)) (n : ℕ) :
    Submodule ℤ (SingularCohomology X n) :=
  LinearMap.ker (singularCohomologyPullback f n - LinearMap.id)

@[simp] theorem mem_singularCohomologyFixed_iff (f : C(X, X)) (n : ℕ)
    (a : SingularCohomology X n) :
    a ∈ singularCohomologyFixed f n ↔ singularCohomologyPullback f n a = a := by
  simp only [singularCohomologyFixed, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- The difference defining actual homological coinvariants. -/
def singularHomologyDifference (f : C(X, X)) (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology X n :=
  LinearMap.id - singularHomologyMap f n

/-- Coinvariants of the actual induced singular-homology map. -/
abbrev SingularHomologyCoinvariants (f : C(X, X)) (n : ℕ) :=
  SingularHomology X n ⧸ LinearMap.range (singularHomologyDifference f n)

variable [∀ k, Module.Projective ℤ (SingularHomology X k)]

/-- Naturality of the proved evaluation equivalence identifies the
literal fixed-class condition with annihilation of the actual difference. -/
theorem singularEvaluation_fixed_iff (f : C(X, X)) (n : ℕ)
    (a : SingularCohomology X n) :
    a ∈ singularCohomologyFixed f n ↔ singularEvaluationEquiv X n a ∈
      (LinearMap.range (singularHomologyDifference f n)).dualAnnihilator := by
  rw [mem_singularCohomologyFixed_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro ha b hb
    obtain ⟨x, rfl⟩ := hb
    change singularEvaluation X n a (x - singularHomologyMap f n x) = 0
    rw [map_sub, ← singularEvaluation_naturality, ha, sub_self]
  · intro ha
    apply (singularEvaluationEquiv X n).injective
    ext b
    have hb := ha (singularHomologyDifference f n b) ⟨b, rfl⟩
    change singularEvaluation X n a (b - singularHomologyMap f n b) = 0 at hb
    rw [map_sub, sub_eq_zero] at hb
    exact (singularEvaluation_naturality f n a b).trans hb.symm

/-- Genuine integral fixed cohomology is the dual of genuine integral
homology coinvariants.  The projectivity input is exactly the proved UCT input. -/
def singularFixedCohomologyEquivDualCoinvariants (f : C(X, X)) (n : ℕ) :
    singularCohomologyFixed f n ≃ₗ[ℤ] Module.Dual ℤ (SingularHomologyCoinvariants f n) :=
  evaluationDualQuotientEquivInt (singularEvaluationEquiv X n)
    (singularCohomologyFixed f n) (LinearMap.range (singularHomologyDifference f n))
    (singularEvaluation_fixed_iff f n)

/-- The fixed-class/coinvariant equivalence preserves every actual evaluation. -/
@[simp] theorem singularFixedCohomologyEquivDualCoinvariants_apply_mk
    (f : C(X, X)) (n : ℕ) (a : singularCohomologyFixed f n)
    (b : SingularHomology X n) :
    singularFixedCohomologyEquivDualCoinvariants f n a (Submodule.Quotient.mk b) =
      singularEvaluation X n a b := rfl

end Wikipedia.HopfProblem.SingularCohomologyFree

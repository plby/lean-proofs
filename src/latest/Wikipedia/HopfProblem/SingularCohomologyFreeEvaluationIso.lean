import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation
import Wikipedia.HopfProblem.SingularCohomologyFreeCyclesZero
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTensorSplitting

/-!
# The actual evaluation isomorphism for projective integral homology

The proved chain-formality homotopy equivalence induces an actual
cochain homotopy equivalence.  Its target has zero differential, so its
actual cohomology is the integral dual of the original actual homology.
The cycle-representative formula proves that this is precisely the
canonical evaluation map, not a separate rank-based identification.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

open ChainFormality

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The literal dual of the zero-differential actual homology complex also has zero differential. -/
theorem dualHomologyComplex_d_zero (i j : ℕ) :
    (dualComplex (homologyComplex K)).d i j = 0 := by
  apply ModuleCat.hom_ext
  ext φ x
  change φ (((homologyComplex K).d j i).hom x) = 0
  rw [homologyComplex_d]
  exact φ.map_zero

variable [∀ n, Module.Projective ℤ (K.homology n)]
  [∀ n, Module.Projective ℤ (K.X n)]

/-- The actual cochain homotopy equivalence gives a genuine linear equivalence in every degree. -/
def formalityCohomologyEquiv (n : ℕ) :
    Cohomology K n ≃ₗ[ℤ] (K.homology n →ₗ[ℤ] ℤ) :=
  (dualHomotopyEquiv_homologyEquiv (homologyHomotopyEquiv K) n).trans
    (zeroDifferentialHomologyEquiv (dualComplex (homologyComplex K))
      (dualHomologyComplex_d_zero K) n)

/-- This equivalence on an actual cocycle is precomposition with the actual cycle realization. -/
theorem formalityCohomologyEquiv_cocycleClass (n : ℕ)
    (c : Cocycle (dualComplex K) n) :
    formalityCohomologyEquiv K n (cocycleClass (dualComplex K) n c) =
      c.val.comp ((realization K).f n).hom := by
  change zeroDifferentialHomologyEquiv (dualComplex (homologyComplex K))
    (dualHomologyComplex_d_zero K) n
      (dualHomotopyEquiv_homologyEquiv (homologyHomotopyEquiv K) n
        (cocycleClass (dualComplex K) n c)) = _
  rw [dualHomotopyEquiv_homologyEquiv_apply, homologyHomotopyEquiv_hom,
    homologyMap_cocycleClass, zeroDifferentialHomologyEquiv_cocycleClass,
    mapCocycles_val, dualMap_f_apply]

/-- The chain-formality isomorphism is exactly canonical evaluation on actual homology. -/
theorem formalityCohomologyEquiv_toLinearMap (n : ℕ) :
    (formalityCohomologyEquiv K n).toLinearMap = cohomologyEvaluation K n := by
  ext a b
  obtain ⟨c, rfl⟩ := cocycleClass_surjective (dualComplex K) n a
  change formalityCohomologyEquiv K n (cocycleClass (dualComplex K) n c) b =
    cohomologyEvaluation K n (cocycleClass (dualComplex K) n c) b
  rw [formalityCohomologyEquiv_cocycleClass, cohomologyEvaluation_cocycleClass]
  change c.val (((realization K).f n).hom b) = cocycleEvaluation K n c b
  rw [realization_f_apply]
  have h := cocycleEvaluation_cycleClass K n c (cycleSection K n b)
  rw [cycleClass_cycleSection] at h
  exact h.symm

/-- Canonical evaluation is bijective, proved from the actual chain/cochain homotopy equivalence. -/
theorem cohomologyEvaluation_bijective (n : ℕ) :
    Function.Bijective (cohomologyEvaluation K n) := by
  rw [← formalityCohomologyEquiv_toLinearMap K n]
  exact (formalityCohomologyEquiv K n).bijective

/-- The actual universal-coefficient identification in the projective, torsion-free case. -/
def cohomologyEvaluationEquiv (n : ℕ) :
    Cohomology K n ≃ₗ[ℤ] (K.homology n →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (cohomologyEvaluation K n) (cohomologyEvaluation_bijective K n)

@[simp] theorem cohomologyEvaluationEquiv_apply (n : ℕ) (a : Cohomology K n) :
    cohomologyEvaluationEquiv K n a = cohomologyEvaluation K n a := rfl

@[simp] theorem cohomologyEvaluationEquiv_toLinearMap (n : ℕ) :
    (cohomologyEvaluationEquiv K n).toLinearMap = cohomologyEvaluation K n := rfl

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
  [∀ n, Module.Projective ℤ (K.homology n)] [∀ n, Module.Projective ℤ (K.X n)]
  [∀ n, Module.Projective ℤ (L.homology n)] [∀ n, Module.Projective ℤ (L.X n)]

/-- The genuine cohomology equivalences preserve the actual
pullback–pushforward evaluation pairing. -/
theorem cohomologyEvaluationEquiv_naturality (f : K ⟶ L) (n : ℕ)
    (a : Cohomology L n) (b : K.homology n) :
    cohomologyEvaluationEquiv K n ((HomologicalComplex.homologyMap (dualMap f) n).hom a) b =
      cohomologyEvaluationEquiv L n a ((HomologicalComplex.homologyMap f n).hom b) :=
  cohomologyEvaluation_naturality f n a b

end Wikipedia.HopfProblem.SingularCohomologyFree

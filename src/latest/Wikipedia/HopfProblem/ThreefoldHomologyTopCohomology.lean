import Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyFreeness
import Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyDual
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular

/-!
# Native top integral cohomology and its actual top-cycle pairing

The genuine sixth homology is infinite cyclic, and the genuine fifth
homology is free.  Degree-local universal coefficients therefore
identify actual sixth singular cohomology with the integers, by
evaluation on the original top class.  No assumption about the
unfinished middle homology groups is needed.  The same argument proves
vanishing of all actual integral cohomology above degree six.

The generator is normalized by the actual cusp connecting and Wang
maps.  This does not assert a comparison with the complex orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopCohomology

open SingularMayerVietoris SingularCohomologyFree
open TopDegree Finiteness
open ThreefoldHomologyTopCohomologyAlgebra

/-- Actual top cohomology is the dual of actual top homology; the only
preceding-degree condition has already been proved from the star maps. -/
def evaluationSixEquiv :
    SingularCohomology Space 6 ≃ₗ[ℤ] (SingularHomology Space 6 →ₗ[ℤ] ℤ) := by
  letI := homologyFive_free
  exact LocalEvaluation.singularEvaluationSuccEquiv Space 5

@[simp] theorem evaluationSixEquiv_apply (a : SingularCohomology Space 6) :
    evaluationSixEquiv a = singularEvaluation Space 6 a := rfl

/-- Native sixth integral singular cohomology of the actual threefold. -/
def cohomologySixEquiv : SingularCohomology Space 6 ≃ₗ[ℤ] ℤ :=
  evaluationSixEquiv.trans (cyclicDualEquiv homologySixEquiv)

/-- Its marking is evaluation on the actual top generator, not a rank-only
identification with an abstract copy of the integers. -/
@[simp] theorem cohomologySixEquiv_apply (a : SingularCohomology Space 6) :
    cohomologySixEquiv a = singularEvaluation Space 6 a topClass := by
  rw [cohomologySixEquiv, LinearEquiv.trans_apply, cyclicDualEquiv_apply,
    evaluationSixEquiv_apply]
  rfl

/-- The genuine cohomology class dual to the original top homology class. -/
def topCohomologyClass : SingularCohomology Space 6 :=
  evaluationSixEquiv.symm homologySixEquiv.toLinearMap

@[simp] theorem topCohomologyClass_evaluate (a : SingularHomology Space 6) :
    singularEvaluation Space 6 topCohomologyClass a = homologySixEquiv a :=
  LinearMap.congr_fun (evaluationSixEquiv.apply_symm_apply homologySixEquiv.toLinearMap) a

@[simp] theorem topCohomologyClass_pairing :
    singularEvaluation Space 6 topCohomologyClass topClass = 1 := by
  rw [topCohomologyClass_evaluate, homologySixEquiv_topClass]

@[simp] theorem cohomologySixEquiv_topCohomologyClass :
    cohomologySixEquiv topCohomologyClass = 1 := by
  rw [cohomologySixEquiv_apply, topCohomologyClass_pairing]

theorem topCohomologyClass_ne_zero : topCohomologyClass ≠ 0 := by
  intro h
  have he := congrArg cohomologySixEquiv h
  rw [cohomologySixEquiv_topCohomologyClass, map_zero] at he
  exact one_ne_zero he

theorem eq_smul_topCohomologyClass (a : SingularCohomology Space 6) :
    a = cohomologySixEquiv a • topCohomologyClass := by
  apply cohomologySixEquiv.injective
  rw [map_zsmul, cohomologySixEquiv_topCohomologyClass]
  simp

theorem cohomologySix_free : Module.Free ℤ (SingularCohomology Space 6) :=
  Module.Free.of_equiv cohomologySixEquiv.symm

theorem cohomologySix_finrank : Module.finrank ℤ (SingularCohomology Space 6) = 1 := by
  rw [cohomologySixEquiv.finrank_eq]
  exact Module.finrank_self ℤ

/-- Actual integral cohomology vanishes above six.  At degree seven the
preceding homology is the proved free top group; in higher degrees it is
the proved zero group. -/
theorem cohomology_subsingleton_of_lt {n : ℕ} (hn : 6 < n) :
    Subsingleton (SingularCohomology Space n) := by
  cases n with
  | zero => omega
  | succ k =>
    have := homology_subsingleton_of_lt hn
    have : Module.Free ℤ (SingularHomology Space k) := by
      by_cases hk : k = 6
      · subst k
        exact homologySix_free
      · have := homology_subsingleton_of_lt (by omega : 6 < k)
        infer_instance
    exact ⟨fun a b => (LocalEvaluation.singularEvaluationSuccEquiv Space k).injective
      (Subsingleton.elim _ _)⟩

theorem cohomology_eq_zero_of_lt {n : ℕ} (hn : 6 < n)
    (a : SingularCohomology Space n) : a = 0 := by
  have := cohomology_subsingleton_of_lt hn
  exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopCohomology

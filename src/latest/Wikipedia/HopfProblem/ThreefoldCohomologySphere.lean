import Wikipedia.HopfProblem.ThreefoldHomologySphere
import Wikipedia.HopfProblem.ThreefoldHomologyMiddleCohomology
import Wikipedia.HopfProblem.ThreefoldHomologyTopCohomology
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Complete integral cohomology of the constructed threefold

The full, proved integral homology calculation makes the original singular
evaluation map an isomorphism in every degree. Thus actual integral cohomology
is infinite cyclic in degrees zero and six and zero otherwise. The degreewise
comparison with the standard sphere preserves actual cochain-cycle evaluation.
It is not asserted to arise from a map, let alone a diffeomorphism, of spaces.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CohomologySphere

open SingularMayerVietoris SingularCohomologyFree
open ThreefoldHomologyTopCohomologyAlgebra Homology

/-- The original singular evaluation pairing is an isomorphism in every degree. -/
def evaluationEquiv (n : ℕ) :
    SingularCohomology Space n ≃ₗ[ℤ] (SingularHomology Space n →ₗ[ℤ] ℤ) := by
  letI (j : ℕ) : Module.Projective ℤ (SingularHomology Space j) := by
    let := HomologySphere.homology_free j
    infer_instance
  exact singularEvaluationEquiv Space n

@[simp] theorem evaluationEquiv_apply (n : ℕ) (a : SingularCohomology Space n) :
    evaluationEquiv n a = singularEvaluation Space n a := rfl

/-- The genuine degree-zero cohomology marking uses the original positive augmentation. -/
def cohomologyZeroEquiv : SingularCohomology Space 0 ≃ₗ[ℤ] ℤ :=
  (evaluationEquiv 0).trans (cyclicDualEquiv LowDegrees.singularH0Equiv)

theorem cohomology_subsingleton (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6) :
    Subsingleton (SingularCohomology Space n) := by
  let := HomologySphere.homology_subsingleton n hn0 hn6
  exact (evaluationEquiv n).injective.subsingleton

theorem cohomology_eq_zero (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6)
    (a : SingularCohomology Space n) : a = 0 :=
  (cohomology_subsingleton n hn0 hn6).elim _ _

theorem cohomology_isZero (n : ℕ) (hn0 : n ≠ 0) (hn6 : n ≠ 6) :
    CategoryTheory.Limits.IsZero (SingularCohomology Space n) := by
  let := cohomology_subsingleton n hn0 hn6
  exact ModuleCat.isZero_of_subsingleton _

theorem cohomology_free (n : ℕ) : Module.Free ℤ (SingularCohomology Space n) := by
  by_cases hn0 : n = 0
  · subst n
    exact Module.Free.of_equiv cohomologyZeroEquiv.symm
  by_cases hn6 : n = 6
  · subst n
    exact TopCohomology.cohomologySix_free
  let := cohomology_subsingleton n hn0 hn6
  exact Module.Free.of_subsingleton ℤ _

theorem cohomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularCohomology Space n) =
      if n = 0 ∨ n = 6 then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simpa using cohomologyZeroEquiv.finrank_eq
  by_cases hn6 : n = 6
  · subst n
    simpa using TopCohomology.cohomologySix_finrank
  let := cohomology_subsingleton n hn0 hn6
  simp [hn0, hn6, Module.finrank_zero_of_subsingleton]

/-- Transport of actual integral duals along the already proved homology equivalence. -/
def homologyDualEquivSixSphere (n : ℕ) :
    (SingularHomology Space n →ₗ[ℤ] ℤ) ≃ₗ[ℤ]
      (SingularHomology SixSphere n →ₗ[ℤ] ℤ) :=
  LinearEquiv.arrowCongr (HomologySphere.homologyEquivSixSphere n) (LinearEquiv.refl ℤ ℤ)

/-- Degreewise comparison of native cohomology, obtained from the original evaluations. -/
def cohomologyEquivSixSphere (n : ℕ) :
    SingularCohomology Space n ≃ₗ[ℤ] SingularCohomology SixSphere n :=
  (evaluationEquiv n).trans ((homologyDualEquivSixSphere n).trans
    (SphereHomology.unitSphereEvaluationEquiv 5 n).symm)

/-- The actual evaluation after the comparison is its contravariant homology transport. -/
theorem cohomologyEquivSixSphere_evaluation (n : ℕ) (a : SingularCohomology Space n)
    (b : SingularHomology SixSphere n) :
    singularEvaluation SixSphere n (cohomologyEquivSixSphere n a) b =
      singularEvaluation Space n a ((HomologySphere.homologyEquivSixSphere n).symm b) := by
  change SphereHomology.unitSphereEvaluationEquiv 5 n (cohomologyEquivSixSphere n a) b = _
  rw [cohomologyEquivSixSphere, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, homologyDualEquivSixSphere, LinearEquiv.arrowCongr_apply,
    LinearEquiv.refl_apply, evaluationEquiv_apply]

/-- The degreewise native homology and cohomology comparisons preserve the full pairing. -/
theorem cohomologyEquivSixSphere_pairing (n : ℕ) (a : SingularCohomology Space n)
    (b : SingularHomology Space n) :
    singularEvaluation SixSphere n (cohomologyEquivSixSphere n a)
        (HomologySphere.homologyEquivSixSphere n b) = singularEvaluation Space n a b := by
  rw [cohomologyEquivSixSphere_evaluation, LinearEquiv.symm_apply_apply]

/-- In particular the original cusp-marked top cohomology still pairs to positive one. -/
theorem topClass_comparison_pairing :
    singularEvaluation SixSphere 6
        (cohomologyEquivSixSphere 6 TopCohomology.topCohomologyClass)
        SixSphereHomology.topClass = 1 := by
  have h := cohomologyEquivSixSphere_pairing 6
    TopCohomology.topCohomologyClass TopDegree.topClass
  rw [HomologySphere.homologyEquivSixSphere_six,
    HomologySphere.homologySixEquivSixSphere_topClass,
    TopCohomology.topCohomologyClass_pairing] at h
  exact h

/-- Complete integral cohomology, using genuine singular cochains in every degree. -/
theorem integralCohomologySphere :
    Nonempty (SingularCohomology Space 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularCohomology Space 6 ≃ₗ[ℤ] ℤ) ∧
      ∀ n, n ≠ 0 → n ≠ 6 → Subsingleton (SingularCohomology Space n) :=
  ⟨⟨cohomologyZeroEquiv⟩, ⟨TopCohomology.cohomologySixEquiv⟩, cohomology_subsingleton⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CohomologySphere

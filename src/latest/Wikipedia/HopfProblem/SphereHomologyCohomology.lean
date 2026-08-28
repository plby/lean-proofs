import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular
import Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyDual

/-!
# Native integral cohomology of the Euclidean spheres

The actual singular evaluation pairing is an isomorphism because all
the integral singular homology groups have now been proved free. This
computes cohomology without replacing it by an abstract graded group.
The top cohomology class pairs to one with the actual suspension-marked
top cycle; no comparison of that marking with an orientation is assumed.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris SingularCohomologyFree
open ThreefoldHomologyTopCohomologyAlgebra

/-- The genuine integral singular evaluation equivalence on each sphere. -/
def unitSphereEvaluationEquiv (n k : ℕ) :
    SingularCohomology (UnitSphere (n + 1)) k ≃ₗ[ℤ]
      (SingularHomology (UnitSphere (n + 1)) k →ₗ[ℤ] ℤ) := by
  letI (j : ℕ) : Module.Projective ℤ (SingularHomology (UnitSphere (n + 1)) j) :=
    inferInstance
  exact singularEvaluationEquiv (UnitSphere (n + 1)) k

@[simp] theorem unitSphereEvaluationEquiv_apply (n k : ℕ)
    (a : SingularCohomology (UnitSphere (n + 1)) k) :
    unitSphereEvaluationEquiv n k a = singularEvaluation (UnitSphere (n + 1)) k a := rfl

/-- The actual degree-zero integral cohomology marking. -/
def unitSphereCohomologyZeroEquiv (n : ℕ) :
    SingularCohomology (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ℤ :=
  (unitSphereEvaluationEquiv n 0).trans (cyclicDualEquiv (unitSphereHomologyZeroEquiv n))

/-- The actual top-degree integral cohomology marking. -/
def unitSphereCohomologyTopEquiv (n : ℕ) :
    SingularCohomology (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ℤ :=
  (unitSphereEvaluationEquiv n (n + 1)).trans
    (cyclicDualEquiv (unitSphereHomologyTopEquiv n))

/-- Its coordinate is the original evaluation on the constructed top cycle. -/
@[simp] theorem unitSphereCohomologyTopEquiv_apply (n : ℕ)
    (a : SingularCohomology (UnitSphere (n + 1)) (n + 1)) :
    unitSphereCohomologyTopEquiv n a =
      singularEvaluation (UnitSphere (n + 1)) (n + 1) a (unitSphereTopClass n) := rfl

/-- The native top cohomology class dual to the actual suspension-marked generator. -/
def unitSphereTopCohomologyClass (n : ℕ) :
    SingularCohomology (UnitSphere (n + 1)) (n + 1) :=
  (unitSphereCohomologyTopEquiv n).symm 1

@[simp] theorem unitSphereTopCohomologyClass_pairing (n : ℕ) :
    singularEvaluation (UnitSphere (n + 1)) (n + 1)
      (unitSphereTopCohomologyClass n) (unitSphereTopClass n) = 1 :=
  (unitSphereCohomologyTopEquiv n).apply_symm_apply 1

theorem unitSphereTopCohomologyClass_ne_zero (n : ℕ) :
    unitSphereTopCohomologyClass n ≠ 0 := by
  intro h
  have hh := unitSphereTopCohomologyClass_pairing n
  rw [h, map_zero, LinearMap.zero_apply] at hh
  exact zero_ne_one hh

/-- Every actual integral cohomology group other than the bottom and top ones is zero. -/
theorem unitSphere_cohomology_subsingleton (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (SingularCohomology (UnitSphere (n + 1)) k) := by
  let := unitSphere_homology_subsingleton n k hk hkn
  exact (unitSphereEvaluationEquiv n k).injective.subsingleton

theorem unitSphere_cohomology_isZero (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    IsZero (SingularCohomology (UnitSphere (n + 1)) k) := by
  let := unitSphere_cohomology_subsingleton n k hk hkn
  exact ModuleCat.isZero_of_subsingleton _

/-- The ranks refer to the original singular cohomology objects in every degree. -/
theorem unitSphere_cohomology_finrank (n k : ℕ) :
    Module.finrank ℤ (SingularCohomology (UnitSphere (n + 1)) k) =
      if k = 0 ∨ k = n + 1 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa using (unitSphereCohomologyZeroEquiv n).finrank_eq
  by_cases hkn : k = n + 1
  · subst k
    simpa using (unitSphereCohomologyTopEquiv n).finrank_eq
  let := unitSphere_cohomology_subsingleton n k hk hkn
  simp [hk, hkn, Module.finrank_zero_of_subsingleton]

end Wikipedia.HopfProblem.SphereHomology

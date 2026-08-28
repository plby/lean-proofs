import Wikipedia.HopfProblem.ThreefoldSphereHomologyEquivalence
import Wikipedia.HopfProblem.ThreefoldCohomologySphere
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The actual sphere map induces integral cohomology equivalences

The already constructed continuous map from the literal six-sphere to the
threefold induces isomorphisms on actual singular homology in every degree.
The proved evaluation equivalences construct an inverse to its original
singular-cohomology pullback. Both inverse identities are verified by the
native evaluation pairing and its naturality.

The forward map of the resulting equivalence is definitionally the original
cohomology pullback. No comparison of top-class markings or recognition of
the target as a sphere is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence

open SingularMayerVietoris SingularCohomologyFree
open SphereHomologyEquivalence

/-- The inverse is constructed from actual evaluation and the dual of the
inverse to the original homology map. -/
def cohomologyInverse (x : Space) (n : ℕ) :
    SingularCohomology SixSphere n →ₗ[ℤ] SingularCohomology Space n :=
  ((SphereHomology.unitSphereEvaluationEquiv 5 n).trans
    (((homologyEquiv x n).symm.dualMap).trans
      (CohomologySphere.evaluationEquiv n).symm)).toLinearMap

/-- Evaluation of the constructed inverse uses precisely the inverse of the
actual induced homology map. -/
theorem cohomologyInverse_evaluation (x : Space) (n : ℕ)
    (a : SingularCohomology SixSphere n) (b : SingularHomology Space n) :
    singularEvaluation Space n (cohomologyInverse x n a) b =
      singularEvaluation SixSphere n a ((homologyEquiv x n).symm b) := by
  change CohomologySphere.evaluationEquiv n (cohomologyInverse x n a) b = _
  simp only [cohomologyInverse, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply,
    SphereHomology.unitSphereEvaluationEquiv_apply]

/-- The constructed inverse recovers every original cohomology class. -/
@[simp] theorem cohomologyInverse_pullback (x : Space) (n : ℕ)
    (a : SingularCohomology Space n) :
    cohomologyInverse x n (singularCohomologyPullback (sphereMap x) n a) = a := by
  apply (CohomologySphere.evaluationEquiv n).injective
  ext b
  change singularEvaluation Space n _ b = singularEvaluation Space n a b
  rw [cohomologyInverse_evaluation, singularEvaluation_naturality]
  change singularEvaluation Space n a ((homologyEquiv x n) ((homologyEquiv x n).symm b)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Pulling back the constructed inverse recovers every actual sphere class. -/
@[simp] theorem pullback_cohomologyInverse (x : Space) (n : ℕ)
    (a : SingularCohomology SixSphere n) :
    singularCohomologyPullback (sphereMap x) n (cohomologyInverse x n a) = a := by
  apply (SphereHomology.unitSphereEvaluationEquiv 5 n).injective
  ext b
  change singularEvaluation SixSphere n _ b = singularEvaluation SixSphere n a b
  rw [singularEvaluation_naturality, cohomologyInverse_evaluation]
  change singularEvaluation SixSphere n a ((homologyEquiv x n).symm ((homologyEquiv x n) b)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem cohomologyInverse_comp_pullback (x : Space) (n : ℕ) :
    (cohomologyInverse x n).comp (singularCohomologyPullback (sphereMap x) n) =
      LinearMap.id := by
  ext a
  exact cohomologyInverse_pullback x n a

@[simp] theorem pullback_comp_cohomologyInverse (x : Space) (n : ℕ) :
    (singularCohomologyPullback (sphereMap x) n).comp (cohomologyInverse x n) =
      LinearMap.id := by
  ext a
  exact pullback_cohomologyInverse x n a

/-- The actual pullback, with its explicitly constructed evaluation-dual inverse. -/
def cohomologyEquiv (x : Space) (n : ℕ) :
    SingularCohomology Space n ≃ₗ[ℤ] SingularCohomology SixSphere n where
  __ := singularCohomologyPullback (sphereMap x) n
  invFun := cohomologyInverse x n
  left_inv := cohomologyInverse_pullback x n
  right_inv := pullback_cohomologyInverse x n

@[simp] theorem cohomologyEquiv_toLinearMap (x : Space) (n : ℕ) :
    (cohomologyEquiv x n).toLinearMap = singularCohomologyPullback (sphereMap x) n := rfl

@[simp] theorem cohomologyEquiv_apply (x : Space) (n : ℕ)
    (a : SingularCohomology Space n) :
    cohomologyEquiv x n a = singularCohomologyPullback (sphereMap x) n a := rfl

@[simp] theorem cohomologyEquiv_symm_toLinearMap (x : Space) (n : ℕ) :
    (cohomologyEquiv x n).symm.toLinearMap = cohomologyInverse x n := rfl

@[simp] theorem cohomologyEquiv_symm_apply (x : Space) (n : ℕ)
    (a : SingularCohomology SixSphere n) :
    (cohomologyEquiv x n).symm a = cohomologyInverse x n a := rfl

/-- All the original cohomology pullbacks of the actual map are bijective. -/
theorem cohomologyPullback_bijective (x : Space) (n : ℕ) :
    Function.Bijective (singularCohomologyPullback (sphereMap x) n) :=
  (cohomologyEquiv x n).bijective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence

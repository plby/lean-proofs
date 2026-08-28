import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralBallFundamentalClass
import Wikipedia.NoExoticSixSphere.ClosedBallIntegralVanishing
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocal

/-!
# Integral cohomology of an actual closed-ball support

The original universal-coefficient evaluation is an equivalence because
the preceding actual integral homology is projective. Evaluation on the
marked primitive therefore computes top cohomology. All off-dimension
cohomology groups vanish, including degree zero. The signed ball class
already constructed here agrees with the original integral marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open SingularCohomologyFree NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

abbrev evaluation (p : ℕ) : Cohomology U p →ₗ[ℤ] ((complex U).homology p →ₗ[ℤ] ℤ) :=
  cohomologyEvaluation (complex U) p

def evaluationZeroEquiv : Cohomology U 0 ≃ₗ[ℤ] ((complex U).homology 0 →ₗ[ℤ] ℤ) :=
  LocalEvaluation.cohomologyEvaluationZeroEquiv (complex U)

def evaluationSuccEquiv (p : ℕ) [Module.Projective ℤ ((complex U).homology p)] :
    Cohomology U (p + 1) ≃ₗ[ℤ] ((complex U).homology (p + 1) →ₗ[ℤ] ℤ) := by
  let (k : ℕ) : Module.Free ℤ ((complex U).X k) := chains_free U k
  exact LocalEvaluation.cohomologyEvaluationSuccEquiv (complex U) p

theorem evaluationSuccEquiv_toLinearMap (p : ℕ) [Module.Projective ℤ ((complex U).homology p)] :
    (evaluationSuccEquiv U p).toLinearMap = evaluation U (p + 1) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralClosedBallCohomology

open Metric NoExoticSixSphere ClosedBallLocalHomology

variable {H : Type} [AddCommGroup H] [Module ℤ H]

/-- The integral dual of an actual cyclic group, by evaluation on its marked primitive. -/
def cyclicFunctionalEquiv (e : H ≃ₗ[ℤ] ℤ) : (H →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ :=
  ((e.arrowCongrAddEquiv (LinearEquiv.refl ℤ ℤ)).trans
    (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).toAddEquiv).toIntLinearEquiv

theorem cyclicFunctionalEquiv_apply (e : H ≃ₗ[ℤ] ℤ) (φ : H →ₗ[ℤ] ℤ) :
    cyclicFunctionalEquiv e φ = φ (e.symm 1) := rfl

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Top cohomology is marked by actual evaluation on the actual integral primitive. -/
def topEquiv (R : ℝ) (hR : 0 ≤ R) :
    IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) (n + 3) ≃ₗ[ℤ] ℤ := by
  let := integral_projective E n R hR (n + 2)
  exact (RelativeIntegralCap.evaluationSuccEquiv (closedBall (0 : E) R)ᶜ (n + 2)).trans
    (cyclicFunctionalEquiv (integralTopEquiv E n R hR))

theorem topEquiv_apply (R : ℝ) (hR : 0 ≤ R)
    (a : IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
    topEquiv E n R hR a = RelativeIntegralCap.evaluation (closedBall (0 : E) R)ᶜ (n + 3) a
      (integralTopClass E n R hR) := rfl

/-- The independently constructed signed ball class is exactly the marked primitive. -/
theorem ballClass_eq_integralTopClass (R : ℝ) (hR : 0 ≤ R) :
    IntegralBallOrientation.fundamentalClass E (n + 1) R hR = integralTopClass E n R hR := by
  apply (integralTopEquiv E n R hR).injective
  rw [integralTopEquiv_class]
  change RelativeSingularHomology.localTopEquiv E (n + 1)
    (IntegralBallOrientation.evaluation R (0 : E) (mem_closedBall_self hR) (n + 3)
      (IntegralBallOrientation.fundamentalClass E (n + 1) R hR)) = 1
  rw [IntegralBallOrientation.fundamentalClass_evaluate_center]
  exact (RelativeSingularHomology.localTopEquiv E (n + 1)).apply_symm_apply 1

theorem topEquiv_apply_ballClass (R : ℝ) (hR : 0 ≤ R)
    (a : IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
    topEquiv E n R hR a = RelativeIntegralCap.evaluation (closedBall (0 : E) R)ᶜ (n + 3) a
      (IntegralBallOrientation.fundamentalClass E (n + 1) R hR) :=
  (topEquiv_apply E n R hR a).trans
    (congrArg (RelativeIntegralCap.evaluation (closedBall (0 : E) R)ᶜ (n + 3) a)
      (ballClass_eq_integralTopClass E n R hR).symm)

/-- The actual supported integral cohomology vanishes in every off-dimension degree. -/
theorem cohomology_subsingleton (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≠ n + 3) :
    Subsingleton (IntegralSupportedCohomology.Cohomology (closedBall (0 : E) R) k) := by
  let := integral_subsingleton E n R hR k hk
  cases k with
  | zero =>
      exact (RelativeIntegralCap.evaluationZeroEquiv (closedBall (0 : E) R)ᶜ).injective.subsingleton
  | succ k =>
      let := integral_projective E n R hR k
      exact (RelativeIntegralCap.evaluationSuccEquiv
        (closedBall (0 : E) R)ᶜ k).injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.IntegralClosedBallCohomology

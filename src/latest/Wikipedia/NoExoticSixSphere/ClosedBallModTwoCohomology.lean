import Wikipedia.NoExoticSixSphere.ClosedBallIntegralMarking
import Wikipedia.NoExoticSixSphere.RelativeModTwoCohomologyEvaluation
import Wikipedia.NoExoticSixSphere.CyclicModTwoEvaluation

/-!
# Actual top mod-two cohomology with closed-ball support

The preceding integral group is proved zero, so the original cohomology
evaluation is an isomorphism. The integral ball marking then identifies
this group with `ZMod 2` by evaluating on the actual primitive class.
The resulting cohomology generator has that literal evaluation equal to one.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Evaluation on the actual primitive computes top cohomology of the ball support. -/
def topCohomologyEquiv (R : ℝ) (hR : 0 ≤ R) :
    RelativeModTwoCochains.Cohomology (closedBall (0 : E) R)ᶜ (n + 3) ≃ₗ[ℤ] ZMod 2 := by
  let := integralPreceding_subsingleton E n R hR
  exact (RelativeModTwoCochains.evaluationSuccEquiv (closedBall (0 : E) R)ᶜ (n + 2)).trans
    (ModTwoCohomologyEvaluation.cyclicFunctionalEquiv (integralTopEquiv E n R hR))

/-- The isomorphism is the original evaluation on the constructed integral class. -/
theorem topCohomologyEquiv_apply (R : ℝ) (hR : 0 ≤ R)
    (a : RelativeModTwoCochains.Cohomology (closedBall (0 : E) R)ᶜ (n + 3)) :
    topCohomologyEquiv E n R hR a =
      RelativeModTwoCochains.evaluation (closedBall (0 : E) R)ᶜ (n + 3) a
        (integralTopClass E n R hR) := rfl

/-- The actual supported top cohomology class evaluating to one on the primitive. -/
def topCohomologyClass (R : ℝ) (hR : 0 ≤ R) :
    RelativeModTwoCochains.Cohomology (closedBall (0 : E) R)ᶜ (n + 3) :=
  (topCohomologyEquiv E n R hR).symm 1

theorem topCohomologyClass_evaluation (R : ℝ) (hR : 0 ≤ R) :
    RelativeModTwoCochains.evaluation (closedBall (0 : E) R)ᶜ (n + 3)
        (topCohomologyClass E n R hR) (integralTopClass E n R hR) = 1 :=
  (topCohomologyEquiv E n R hR).apply_symm_apply 1

theorem topCohomologyClass_ne_zero (R : ℝ) (hR : 0 ≤ R) :
    topCohomologyClass E n R hR ≠ 0 := by
  intro h
  have he := topCohomologyClass_evaluation E n R hR
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact zero_ne_one he

end NoExoticSixSphere.ClosedBallLocalHomology

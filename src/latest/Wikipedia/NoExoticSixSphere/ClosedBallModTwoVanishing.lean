import Wikipedia.NoExoticSixSphere.ClosedBallIntegralVanishing
import Wikipedia.NoExoticSixSphere.RelativeModTwoCohomologyEvaluation

/-!
# Actual closed-ball supported mod-two cohomology vanishes off the dimension

The original evaluation equivalence detects cohomology classes because
the preceding actual integral homology is proved projective. Its target
is zero in every off-dimension degree, including degree zero.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Off-dimension vanishing for the original supported cohomology, without extra assumptions. -/
theorem cohomology_subsingleton (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≠ n + 3) :
    Subsingleton (RelativeModTwoCochains.Cohomology (closedBall (0 : E) R)ᶜ k) := by
  let := integral_subsingleton E n R hR k hk
  cases k with
  | zero =>
    exact (RelativeModTwoCochains.evaluationZeroEquiv
      (closedBall (0 : E) R)ᶜ).injective.subsingleton
  | succ k =>
    let := integral_projective E n R hR k
    exact (RelativeModTwoCochains.evaluationSuccEquiv
      (closedBall (0 : E) R)ᶜ k).injective.subsingleton

end NoExoticSixSphere.ClosedBallLocalHomology

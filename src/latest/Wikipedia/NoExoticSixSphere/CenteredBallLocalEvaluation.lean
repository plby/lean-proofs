import Wikipedia.NoExoticSixSphere.ClosedBallLocalEvaluation
import Wikipedia.NoExoticSixSphere.SupportedEvaluationTransport

/-!
# Actual evaluation on a ball with arbitrary center

Translation carries the original supported and local relative complexes
to those of a ball centered at zero. The proved evaluation square, not
an arbitrary group identification, gives bijectivity at every point.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem translateBall_membership (a : E) (R : ℝ) (x : E) :
    x ∈ closedBall (0 : E) R ↔ Homeomorph.addRight a x ∈ closedBall a R := by
  change dist x 0 ≤ R ↔ dist (x + a) a ≤ R
  simp only [dist_eq_norm, sub_zero, add_sub_cancel_right]

/-- Every original point evaluation on a closed ball of nonnegative radius is bijective. -/
theorem evaluate_centered_bijective (p : ℕ) (hp : p ≠ 0) (a : E) (R : ℝ) (hR : 0 ≤ R)
    (x : E) (hx : x ∈ closedBall a R) (k : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) (closedBall a R) x hx k) := by
  obtain ⟨y, rfl⟩ := (Homeomorph.addRight a).surjective x
  have hy := (translateBall_membership a R y).mpr hx
  exact (evaluate_bijective_iff_homeomorph (ModuleCat.of ℤ (ZMod p))
    (Homeomorph.addRight a) (translateBall_membership a R) y hy k).mpr
    (evaluateEquiv p hp R hR y hy k).bijective

end NoExoticSixSphere.ClosedBallLocalHomology

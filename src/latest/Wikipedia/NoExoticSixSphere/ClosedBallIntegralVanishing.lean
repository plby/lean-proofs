import Wikipedia.NoExoticSixSphere.ClosedBallIntegralMarking
import Wikipedia.NoExoticSixSphere.RelativeConnectedLowHomology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Module.Projective

/-!
# Integral closed-ball supported homology in all off-dimension degrees

Path connectedness of the punctured model handles degrees zero and one
through the original pair sequence. The proved sphere calculation handles
the higher degrees. The actual center evaluation transports these results
to every closed ball of nonnegative radius.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

include n in
omit [FiniteDimensional ℝ E] in
/-- The punctured Euclidean model is path connected by its actual dimension. -/
theorem punctured_pathConnected : PathConnectedSpace ({(0 : E)}ᶜ : Set E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  apply Module.one_lt_rank_of_one_lt_finrank
  have hd := Fact.out (p := Module.finrank ℝ E = (n + 2) + 1)
  omega

/-- Every original off-dimension integral ball-supported group vanishes, including degrees 0, 1. -/
theorem integral_subsingleton (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≠ n + 3) :
    Subsingleton (RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ k) := by
  let := punctured_pathConnected E n
  have hlocal : Subsingleton (RelativeSingularHomology.LocalHomology (0 : E) k) := by
    rcases k with _ | _ | k
    · exact RelativeSingularHomology.connected_homologyZero_subsingleton ({(0 : E)}ᶜ : Set E)
    · exact RelativeSingularHomology.connected_homologyOne_subsingleton ({(0 : E)}ᶜ : Set E)
    · exact RelativeSingularHomology.localHomology_subsingleton E (n + 1) (k + 1)
        (Nat.succ_ne_zero k) (by omega)
  exact (evaluateIntegralEquiv (E := E) R hR k).injective.subsingleton

include n in
/-- Every integral ball-supported group is projective: cyclic at the dimension, zero off it. -/
theorem integral_projective (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    Module.Projective ℤ (RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ k) := by
  by_cases hk : k = n + 3
  · subst k
    exact Module.Projective.of_equiv (integralTopEquiv E n R hR).symm
  · let := integral_subsingleton E n R hR k hk
    infer_instance

end NoExoticSixSphere.ClosedBallLocalHomology

import Wikipedia.NoExoticSixSphere.ClosedBallLocalEvaluation
import Wikipedia.NoExoticSixSphere.EuclideanLocalHomology

/-!
# An integral marking of the original closed-ball supported homology

The original evaluation at the center is an integral homology
isomorphism. Composing it with the proved local sphere marking gives a
primitive class on the actual ball support. The preceding integral group
vanishes by the same original evaluation map.
-/

noncomputable section

open CategoryTheory Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original center evaluation, on actual integral relative homology in every degree. -/
def evaluateIntegralEquiv (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ k ≃ₗ[ℤ]
      RelativeSingularHomology.LocalHomology (0 : E) k := by
  let := evaluationChain_quasiIso R hR (0 : E) (mem_closedBall_self hR)
  exact (isoOfQuasiIsoAt (evaluationChain R (0 : E) (mem_closedBall_self hR)) k).toLinearEquiv

end NoExoticSixSphere.ClosedBallLocalHomology

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The actual integral ball-supported top homology, marked by the center and sphere maps. -/
def integralTopEquiv (R : ℝ) (hR : 0 ≤ R) :
    RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 3) ≃ₗ[ℤ] ℤ :=
  (evaluateIntegralEquiv R hR (n + 3)).trans (RelativeSingularHomology.localTopEquiv E (n + 1))

/-- A primitive in the original integral relative group of the ball. -/
def integralTopClass (R : ℝ) (hR : 0 ≤ R) :
    RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 3) :=
  (integralTopEquiv E n R hR).symm 1

theorem integralTopEquiv_class (R : ℝ) (hR : 0 ≤ R) :
    integralTopEquiv E n R hR (integralTopClass E n R hR) = 1 :=
  (integralTopEquiv E n R hR).apply_symm_apply 1

/-- The original preceding group vanishes, rather than being an assumed free module. -/
theorem integralPreceding_subsingleton (R : ℝ) (hR : 0 ≤ R) :
    Subsingleton (RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 2)) := by
  let := RelativeSingularHomology.localHomology_subsingleton E (n + 1) (n + 1)
    (Nat.succ_ne_zero n) (by omega)
  exact (evaluateIntegralEquiv (E := E) R hR (n + 2)).injective.subsingleton

end NoExoticSixSphere.ClosedBallLocalHomology

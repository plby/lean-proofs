import Wikipedia.NoExoticSixSphere.ClosedBallIntegralMarking
import Wikipedia.NoExoticSixSphere.ClosedBallFundamentalClass

/-!
# The original mod-two ball class is the reduction of the integral primitive

The actual relative coefficient sequence computes the two-element top
group and retains the reduction formula. Its constructed nonzero
fundamental class is therefore exactly the reduction of the actual
marked integral primitive, not an unrelated choice of generator.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Original coefficient reduction is onto, by the proved preceding integral vanishing. -/
theorem topReduction_surjective (R : ℝ) (hR : 0 ≤ R) :
    Function.Surjective
      (RelativeCoefficients.reductionMap 2 (closedBall (0 : E) R)ᶜ (n + 3)) := by
  let := integralPreceding_subsingleton E n R hR
  exact RelativeCoefficients.reductionMap_surjective_of_subsingleton 2 (by decide)
    (closedBall (0 : E) R)ᶜ (n + 2)

/-- The actual native mod-two group with the marking induced by its integral generator. -/
def topModHomologyEquiv (R : ℝ) (hR : 0 ≤ R) :
    RelativeCoefficients.ModHomology 2 (closedBall (0 : E) R)ᶜ (n + 3) ≃ₗ[ℤ] ZMod 2 :=
  RelativeCoefficients.markingEquiv 2 (by decide) (closedBall (0 : E) R)ᶜ (n + 3)
    (topReduction_surjective E n R hR) (integralTopEquiv E n R hR)

theorem topModHomologyEquiv_reduction (R : ℝ) (hR : 0 ≤ R)
    (a : RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 3)) :
    topModHomologyEquiv E n R hR
        (RelativeCoefficients.reductionMap 2 (closedBall (0 : E) R)ᶜ (n + 3) a) =
      (integralTopEquiv E n R hR a : ZMod 2) :=
  RelativeCoefficients.markingEquiv_reduction 2 (by decide)
    (closedBall (0 : E) R)ᶜ (n + 3) (topReduction_surjective E n R hR)
    (integralTopEquiv E n R hR) a

/-- Native reduction of the actual integral primitive is the constructed fundamental class. -/
theorem reduction_integralTopClass (R : ℝ) (hR : 0 ≤ R) :
    RelativeCoefficients.reductionMap 2 (closedBall (0 : E) R)ᶜ (n + 3)
        (integralTopClass E n R hR) = fundamentalClass E n R hR := by
  apply (topModHomologyEquiv E n R hR).injective
  rw [topModHomologyEquiv_reduction, integralTopEquiv_class, Int.cast_one]
  have hne : topModHomologyEquiv E n R hR (fundamentalClass E n R hR) ≠ 0 := by
    intro hz
    exact fundamentalClass_ne_zero E n R hR
      ((topModHomologyEquiv E n R hR).injective
        (hz.trans (topModHomologyEquiv E n R hR).map_zero.symm))
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact ((hz _).resolve_left hne).symm

end NoExoticSixSphere.ClosedBallLocalHomology

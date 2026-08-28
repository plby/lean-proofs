import Wikipedia.NoExoticSixSphere.RelativeModTwoCapEvaluation
import Wikipedia.NoExoticSixSphere.ClosedBallModTwoCohomology
import Wikipedia.NoExoticSixSphere.ClosedBallFundamentalReduction
import Wikipedia.NoExoticSixSphere.CompactSupportedCapMap

/-!
# Bijectivity of the actual top-degree cap map on a closed-ball support

The supported fundamental class equals the reduction of the constructed
integral primitive. The original cap-augmentation identity therefore
identifies the genuine cap map with the already proved top cohomology
marking. Since native augmentation is an isomorphism on the ambient
Euclidean space, this actual cap map is bijective.
-/

noncomputable section

open Metric
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.ClosedBallLocalHomology

open ModTwoCapProduct (Coefficient)

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Both constructions choose the same actual class with the prescribed local values. -/
theorem fundamentalClass_eq_compact (R : ℝ) (hR : 0 ≤ R) :
    fundamentalClass E n R hR =
      CompactSupportedFundamentalClass.fundamentalClass (E := E) n
        (closedBall (0 : E) R) (isCompact_closedBall (0 : E) R) :=
  CompactSupportedFundamentalClass.unique (E := E) n (closedBall (0 : E) R)
    (isCompact_closedBall (0 : E) R) _ (fundamentalClass_isFundamentalOn E n R hR)

/-- The original cap map has precisely the previously computed top evaluation. -/
theorem augmentation_topCap (R : ℝ) (hR : 0 ≤ R)
    (a : SupportedModTwoCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
    CoefficientChains.augmentation Coefficient E
        (CompactSupportedCapMap.dualityMap (E := E) n (closedBall (0 : E) R)
          (isCompact_closedBall (0 : E) R) (n + 3) 0 (Nat.add_zero (n + 3)) a) =
      topCohomologyEquiv E n R hR a := by
  rw [CompactSupportedCapMap.dualityMap_apply, ← fundamentalClass_eq_compact E n R hR,
    ← reduction_integralTopClass E n R hR]
  exact (RelativeModTwoCap.augmentation_capProduct_reduction (closedBall (0 : E) R)ᶜ
    (n + 3) a (integralTopClass E n R hR)).trans
    (topCohomologyEquiv_apply E n R hR a).symm

/-- Top-degree duality for this support, proved for the original cap map. -/
theorem topCap_bijective (R : ℝ) (hR : 0 ≤ R) :
    Function.Bijective (CompactSupportedCapMap.dualityMap (E := E) n
      (closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
      (n + 3) 0 (Nat.add_zero (n + 3))) := by
  let A := CoefficientChains.connectedZeroEquiv Coefficient E
  let C := topCohomologyEquiv E n R hR
  have he (a : SupportedModTwoCohomology.Cohomology (closedBall (0 : E) R) (n + 3)) :
      A (CompactSupportedCapMap.dualityMap (E := E) n (closedBall (0 : E) R)
        (isCompact_closedBall (0 : E) R) (n + 3) 0 (Nat.add_zero (n + 3)) a) = C a :=
    augmentation_topCap E n R hR a
  constructor
  · intro a b hab
    apply C.injective
    exact (he a).symm.trans ((congrArg A hab).trans (he b))
  · intro b
    refine ⟨C.symm (A b), A.injective ?_⟩
    exact (he _).trans (C.apply_symm_apply (A b))

/-- The equivalence whose forward map is literally the original supported cap. -/
def topCapEquiv (R : ℝ) (hR : 0 ≤ R) :
    SupportedModTwoCohomology.Cohomology (closedBall (0 : E) R) (n + 3) ≃ₗ[ℤ]
      ModHomology 2 E 0 :=
  LinearEquiv.ofBijective (CompactSupportedCapMap.dualityMap (E := E) n
    (closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
    (n + 3) 0 (Nat.add_zero (n + 3))) (topCap_bijective E n R hR)

theorem topCapEquiv_toLinearMap (R : ℝ) (hR : 0 ≤ R) :
    (topCapEquiv E n R hR).toLinearMap =
      CompactSupportedCapMap.dualityMap (E := E) n (closedBall (0 : E) R)
        (isCompact_closedBall (0 : E) R) (n + 3) 0 (Nat.add_zero (n + 3)) := rfl

end NoExoticSixSphere.ClosedBallLocalHomology

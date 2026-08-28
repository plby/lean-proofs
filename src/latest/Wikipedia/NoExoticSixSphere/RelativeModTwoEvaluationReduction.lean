import Wikipedia.NoExoticSixSphere.RelativeModTwoCohomologyEvaluation
import Wikipedia.NoExoticSixSphere.ModTwoFunctionalQuotient

/-!
# Original relative cohomology evaluation depends only on native mod-two reduction

The actual kernel of coefficient reduction is twice integral homology.
Every original mod-two-valued functional annihilates that kernel. Thus
equal native reductions give equal values of the original cohomology
class on the original integral homology classes.
-/

noncomputable section

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Actual relative evaluation factors through the proved original coefficient-reduction kernel. -/
theorem evaluation_eq_of_reduction_eq (p : ℕ) (a : Cohomology U p)
    (b c : RelativeSingularHomology.Homology U p)
    (hbc : RelativeCoefficients.reductionMap 2 U p b =
      RelativeCoefficients.reductionMap 2 U p c) : evaluation U p a b = evaluation U p a c := by
  have hk : b - c ∈ LinearMap.ker (RelativeCoefficients.reductionMap 2 U p) := by
    change RelativeCoefficients.reductionMap 2 U p (b - c) = 0
    rw [map_sub, hbc, sub_self]
  rw [RelativeCoefficients.reductionMap_ker 2 (by decide) U p] at hk
  have hz := ModTwoFunctional.scalarImage_le_ker (RelativeSingularHomology.Homology U p)
    (evaluation U p a) hk
  exact sub_eq_zero.mp ((map_sub (evaluation U p a) b c).symm.trans hz)

end NoExoticSixSphere.RelativeModTwoCochains

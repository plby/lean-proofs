import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtCyclesComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTruncation

/-!
# Native degree-two cycles and global sections under finite pushforward

The actual truncation morphism uses the canonical kernel comparison.
Its map on global cokernels agrees with the identity on the homology
of the literal global cochain complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward
open LowExt

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The global cokernel map of the actual truncation morphism is
precisely the one induced by the canonical kernel comparison. -/
theorem pushforwardTruncationMap_globalCokernelMap
    (R : CochainResolution (AbelianSheaf X)) :
    (pushforwardTruncationMap f hf hfinite R).globalCokernelMap =
      Cycles.iteratedCokernelMap₂ (pushforward f) (globalSectionsFunctor Y) R.K := rfl

/-- The degree-two cycle/cokernel square for actual finite closed
pushforward. Both full global-section complexes are literally equal,
and the map used here is the genuine truncation comparison. -/
@[reassoc] theorem pushforwardTruncationMap_globalSecondHomology
    (R : CochainResolution (AbelianSheaf X)) :
    (pushforwardTruncationMap f hf hfinite R).globalCokernelMap ≫
        (pushforwardResolution f hf hfinite R).globalSecondHomologyIso.hom =
      R.globalSecondHomologyIso.hom := by
  let := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  exact Cycles.iteratedCokernelMap₂_homology (pushforward f) (globalSectionsFunctor Y) R.K

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

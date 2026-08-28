import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsPullback
import Wikipedia.HopfProblem.CuspNormalizationSheafPullback

/-!
# The actual constant-to-holomorphic pullback square

For an actual holomorphic map whose image lies in a subset, the constants
map to the reduced holomorphic sheaf commutes with actual pullback to the
source manifold.  Both horizontal maps are the genuine constant-sheaf
maps, and the lower map is literal holomorphic composition, not an
abstract map assumed to preserve the normalization data.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G) (S : Set M)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, g x ∈ S)

/-- Naturality of the constants inclusion for the actual reduced-to-manifold
holomorphic pullback. -/
theorem reduced_holomorphic_naturality :
    reducedMap I S ≫ SheafPullback.pullback I J S g hg =
      pullbackMap (SheafPullback.topMap I J S g hg) ≫
        (TopCat.Sheaf.pushforward CommRingCat (SheafPullback.topMap I J S g hg)).map
          (holomorphicMap J N) := by
  apply pullback_naturality (SheafPullback.topMap I J S g hg)
    (HolomorphicFunctionSheaf.sheaf J N) (SheafReduced.sheaf I S)
    (holomorphicPresheafMap J N) (reducedPresheafMap I S)
    (SheafPullback.pullback I J S g hg)
  intro U c
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants

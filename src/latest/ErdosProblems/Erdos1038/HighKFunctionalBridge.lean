import ErdosProblems.Erdos1038.HighKLowerBridge
import ErdosProblems.Erdos1038.LowKPolynomial

/-!
# Exact residual-functional target for the high-ratio case

The platform argument is a real-variable lower bound for the normalized
main-component width plus twice the explicit residual radii.  This module
shows that this is exactly sufficient for `HighKEndpointStrictLowerBound`;
all component geometry, ENNReal coercions, and normalization back to the
original polynomial are discharged here.
-/

set_option warningAsError false

open scoped ENNReal BigOperators
open Polynomial

namespace Erdos1038

noncomputable section

/-- The sole real inequality which the platform/supporting argument must
prove for every endpoint-normalized high-ratio polynomial. -/
def HighKNormalizedFunctionalStrictLowerBound : Prop :=
  ∀ (g : Polynomial ℝ) (h : EndpointNormalizationHypotheses g),
    ∀ hres : endpointResidualRoots h.normalizedPolynomial ≠ 0,
      29 / 20 < normalizedEndpointResidualRatio h →
        L < normalizedMainComponentWidth h +
          2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
            (normalizedEndpointResidualRatio h)

/-- The exact normalized residual-functional inequality implies the
configuration-level high-`k` assertion used by final assembly. -/
theorem highKEndpointStrictLowerBound_of_normalizedFunctional
    (hfunctional : HighKNormalizedFunctionalStrictLowerBound) :
    HighKEndpointStrictLowerBound := by
  intro g h hres hk
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hstrict : L < normalizedMainComponentWidth h +
      2 * residualRadiusSum C k := by
    simpa only [C, k] using! hfunctional g h hres hk
  have hradiusSum : 0 ≤ residualRadiusSum C k := by
    exact Finset.sum_nonneg fun i _ ↦ (residualRadius_pos C k i).le
  have hfunctionalPos : 0 < normalizedMainComponentWidth h +
      2 * residualRadiusSum C k :=
    add_pos_of_pos_of_nonneg h.normalizedMainComponentWidth_pos
      (mul_nonneg (by norm_num) hradiusSum)
  have hofReal : ENNReal.ofReal L <
      ENNReal.ofReal (normalizedMainComponentWidth h +
        2 * residualRadiusSum C k) :=
    (ENNReal.ofReal_lt_ofReal_iff hfunctionalPos).2 hstrict
  exact hofReal.trans_le
    (h.ofReal_mainWidth_add_twice_radiusSum_le_sublevelVolume hres)

end

end Erdos1038

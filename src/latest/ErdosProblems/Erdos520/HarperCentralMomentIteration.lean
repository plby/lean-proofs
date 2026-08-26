import ErdosProblems.Erdos520.HarperTiltedPositiveLogBallot
import ErdosProblems.Erdos520.HarperPositiveLogDyadicRecursion
import ErdosProblems.Erdos520.HarperEconomicalMomentIteration

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Direct iteration on a shrinking central band

This is the analytic-to-numerical bridge for the central dyadic
decomposition.  It consumes the unconditional actual-law positive-log
recursion, preserves the small vertical volume in the good coefficient, and
also preserves it through the terminal Jensen step.
-/

/-- Universal slope in the actual tilted positive-log ballot estimate. -/
noncomputable def harperTiltedPositiveLogSlope : ℝ :=
  Real.exp 4 * 44000000

theorem harperTiltedPositiveLogSlope_nonneg :
    0 ≤ harperTiltedPositiveLogSlope := by
  unfold harperTiltedPositiveLogSlope
  positivity

/-- The complete iterated moment bound on any measurable set lying in one
central scale.  No probability premise remains. -/
theorem exists_integral_harperCentralBand_twoThird_le_iterated :
    ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ,
        J + d ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, (1 / 2 : ℝ) ^ (d + 1) < |t|) →
      (∀ t ∈ I, |t| ≤ (1 / 2 : ℝ) ^ d) →
      ∀ C : ℝ, Real.log 4 ≤ C → ∀ L : ℕ,
        harperDyadicMomentGap L * Real.sqrt (n : ℝ) ≤ 2 →
        (∫ omega, harperEulerSetEnergy y I omega ^ harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 *
            (2 *
                (harperPositiveLogDyadicSmallGoodConstant
                    (volume.real I) harperTiltedPositiveLogSlope
                    (harperExplicitPrefixPositiveLogOffset
                      start 1 0 E D + 3) C +
                  2 * Real.exp (-C)) +
              2 *
                ((harperExplicitMertensConstant * volume.real I) ^
                    harperTwoThird +
                  harperExplicitMertensConstant * volume.real I)) := by
  obtain ⟨E, hE, D, hD, J, hstep⟩ :=
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixCentralPositiveLog_unconditional
  refine ⟨E, hE, D, hD, J, ?_⟩
  intro d start n y hstart hn hyEndpoint hy I hI hIfinite
    htLower htUpper C hC L hstop
  let Z : Omega → ℝ := harperEulerSetEnergy y I
  let N : ℝ := Real.sqrt (n : ℝ)
  let V : ℝ := volume.real I
  let K : ℝ := harperTiltedPositiveLogSlope
  let X : ℝ :=
    harperExplicitPrefixPositiveLogOffset start 1 0 E D + 3
  let T : ℝ := harperExplicitMertensConstant * V
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < N := by
    dsimp only [N]
    exact Real.sqrt_pos.2 hnR
  have hV : 0 ≤ V := by
    dsimp only [V]
    exact measureReal_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact harperTiltedPositiveLogSlope_nonneg
  have hC0 : 0 ≤ C := by
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hX : 0 ≤ X := by
    dsimp only [X]
    have hoffset := harperExplicitPrefixPositiveLogOffset_nonneg
      start 1 (B := 0) (E := E) (D := D) (by norm_num) hE hD
    linarith
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg harperExplicitMertensConstant_pos.le hV
  have hA : 0 ≤
      harperPositiveLogDyadicSmallGoodConstant V K X C := by
    unfold harperPositiveLogDyadicSmallGoodConstant
    exact add_nonneg (Real.rpow_nonneg (by positivity) _)
      (by positivity)
  have hZ : Integrable Z μ := by
    dsimp only [Z]
    exact integrable_harperEulerSetEnergy y hI hIfinite
  have hZnonneg : ∀ omega, 0 ≤ Z omega := by
    dsimp only [Z]
    exact harperEulerSetEnergy_nonneg (by omega) hI
  have hrec : ∀ m, m < L →
      (∫ omega, Z omega ^ harperDyadicMomentExponent m ∂μ) ≤
        harperPositiveLogDyadicSmallGoodConstant V K X C *
            harperDyadicMomentWeight N m +
          (1 * Real.exp (-2 * C / harperDyadicMomentGap m)) ^
              harperDyadicBadHolderExponent m *
            (∫ omega,
                Z omega ^ harperDyadicMomentExponent (m + 1) ∂μ) ^
              (harperDyadicMomentExponent m /
                harperDyadicMomentExponent (m + 1)) := by
    intro m hm
    let B : ℝ := C / harperDyadicMomentGap m
    let x : ℝ := harperExplicitPrefixPositiveLogOffset start 1 B E D
    let H : ℝ := harperTiltedPositiveLogProbabilityBound n x
    have hB : 0 ≤ B := by
      dsimp only [B]
      exact div_nonneg hC0 (harperDyadicMomentGap_pos m).le
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact harperExplicitPrefixPositiveLogOffset_nonneg
        start 1 hB hE hD
    have hH0 : 0 ≤ H := by
      dsimp only [H]
      exact harperTiltedPositiveLogProbabilityBound_nonneg n hx
    have hH : H ≤ K *
        (X + C / harperDyadicMomentGap m) / N := by
      apply le_of_eq
      unfold H harperTiltedPositiveLogProbabilityBound
      dsimp only [K, X, N, x, B, harperTiltedPositiveLogSlope]
      unfold harperExplicitPrefixPositiveLogOffset
      ring
    have hraw := hstep d start n y hstart hn hyEndpoint hy
      I hI hIfinite htLower htUpper B hB
      (harperDyadicMomentExponent m)
      (harperDyadicMomentExponent (m + 1))
      (harperDyadicMomentExponent_pos m)
      (harperDyadicMomentExponent_strictMono (Nat.lt_succ_self m))
      (harperDyadicMomentExponent_lt_one (m + 1)).le
    have hraw' :
        (∫ omega, Z omega ^ harperDyadicMomentExponent m ∂μ) ≤
          (harperExplicitMertensConstant * (V * H)) ^
              harperDyadicMomentExponent m +
            Real.exp (-2 * C / harperDyadicMomentGap m) ^
                harperDyadicBadHolderExponent m *
              (∫ omega,
                  Z omega ^ harperDyadicMomentExponent (m + 1) ∂μ) ^
                (harperDyadicMomentExponent m /
                  harperDyadicMomentExponent (m + 1)) := by
      simpa only [Z, V, H, x, B, harperDyadicBadHolderExponent,
        div_eq_mul_inv, mul_assoc] using! hraw
    have hconverted :=
      harperDyadicRecurrence_of_explicitPositiveLogStep_preserving_small
        m hV hN hK hX hC0 hH0 hH hraw'
    simpa only [Z, V, K, X, N, H, x, B, one_mul] using! hconverted
  have hfirst : (∫ omega, Z omega ∂μ) ≤ T := by
    dsimp only [Z, T, V]
    exact integral_harperEulerSetEnergy_le_explicitMertens_mul_volume
      hy hI hIfinite
  have hdirect :=
    integral_rpow_twoThird_le_of_harperDyadicRecurrences_preserving_first
      Z (N := N) (C := C) (Kbad := 1)
      (A := harperPositiveLogDyadicSmallGoodConstant V K X C)
      (T := T) (L := L)
      hN (by norm_num) (by simpa using! hC) hA hT hZ hZnonneg
      hrec hfirst (by simpa only [N] using! hstop)
  simpa only [Z, N, V, K, X, T, max_self, one_mul, mul_one] using! hdirect

end Problem520
end Erdos

#print axioms Erdos.Problem520.exists_integral_harperCentralBand_twoThird_le_iterated

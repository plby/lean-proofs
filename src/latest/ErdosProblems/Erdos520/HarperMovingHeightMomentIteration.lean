import ErdosProblems.Erdos520.HarperCentralMomentIteration

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Direct iteration on growing noncentral height windows

This is the noncentral counterpart of the shrinking-band moment iterator.
It consumes the unconditional moving-height positive-log recursion with its
single absolute cutoff and explicit `clog 2 (M + 1)` shift, converts every
step to the standard Harper dyadic recurrence, and stops at the initial
`2/3` moment.  No abstract probability premise remains.
-/

/-- The complete iterated moment bound on a measurable set in a growing
noncentral height window.  One fixed `J` works simultaneously for every
natural height cutoff `M`. -/
theorem exists_integral_harperMovingHeight_twoThird_le_iterated :
    ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, 1 ≤ |t|) → (∀ t ∈ I, |t| ≤ M) →
      ∀ C : ℝ, Real.log 4 ≤ C → ∀ L : ℕ,
        harperDyadicMomentGap L * Real.sqrt (n : ℝ) ≤ 2 →
        (∫ omega, harperEulerSetEnergy y I omega ^ harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 *
            (2 *
                (harperPositiveLogDyadicGoodConstant
                    (volume.real I) harperTiltedPositiveLogSlope
                    (harperExplicitPrefixPositiveLogOffset
                      start M 0 E D + 3) C +
                  2 * Real.exp (-C)) +
              2 * max 1
                (harperExplicitMertensConstant * volume.real I)) := by
  obtain ⟨E, hE, D, hD, J, hstep⟩ :=
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixPositiveLog_unconditional
  refine ⟨E, hE, D, hD, J, ?_⟩
  intro M start n y hstart hn hyEndpoint hy I hI hIfinite
    htLower htUpper C hC L hstop
  let Z : Omega → ℝ := harperEulerSetEnergy y I
  let N : ℝ := Real.sqrt (n : ℝ)
  let V : ℝ := volume.real I
  let K : ℝ := harperTiltedPositiveLogSlope
  let X : ℝ :=
    harperExplicitPrefixPositiveLogOffset start M 0 E D + 3
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
      start M (B := 0) (E := E) (D := D) (by norm_num) hE hD
    linarith
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg harperExplicitMertensConstant_pos.le hV
  have hA : 0 ≤
      harperPositiveLogDyadicGoodConstant V K X C := by
    unfold harperPositiveLogDyadicGoodConstant
    exact le_max_of_le_left (by norm_num)
  have hZ : Integrable Z μ := by
    dsimp only [Z]
    exact integrable_harperEulerSetEnergy y hI hIfinite
  have hZnonneg : ∀ omega, 0 ≤ Z omega := by
    dsimp only [Z]
    exact harperEulerSetEnergy_nonneg (by omega) hI
  have hrec : ∀ m, m < L →
      (∫ omega, Z omega ^ harperDyadicMomentExponent m ∂μ) ≤
        harperPositiveLogDyadicGoodConstant V K X C *
            harperDyadicMomentWeight N m +
          (1 * Real.exp (-2 * C / harperDyadicMomentGap m)) ^
              harperDyadicBadHolderExponent m *
            (∫ omega,
                Z omega ^ harperDyadicMomentExponent (m + 1) ∂μ) ^
              (harperDyadicMomentExponent m /
                harperDyadicMomentExponent (m + 1)) := by
    intro m hm
    let B : ℝ := C / harperDyadicMomentGap m
    let x : ℝ := harperExplicitPrefixPositiveLogOffset start M B E D
    let H : ℝ := harperTiltedPositiveLogProbabilityBound n x
    have hB : 0 ≤ B := by
      dsimp only [B]
      exact div_nonneg hC0 (harperDyadicMomentGap_pos m).le
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact harperExplicitPrefixPositiveLogOffset_nonneg
        start M hB hE hD
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
    have hraw := hstep M start n y hstart hn hyEndpoint hy
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
      harperDyadicRecurrence_of_explicitPositiveLogStep
        m hV hN hK hX hC0 hH0 hH hraw'
    simpa only [Z, V, K, X, N, H, x, B, one_mul] using! hconverted
  have hfirst : (∫ omega, Z omega ∂μ) ≤ T := by
    dsimp only [Z, T, V]
    exact integral_harperEulerSetEnergy_le_explicitMertens_mul_volume
      hy hI hIfinite
  have hdirect := integral_rpow_twoThird_le_of_harperDyadicRecurrences
    Z (N := N) (C := C) (Kbad := 1)
      (A := harperPositiveLogDyadicGoodConstant V K X C)
      (T := T) (L := L)
      hN (by norm_num) (by simpa using! hC) hA hT hZ hZnonneg
      hrec hfirst (by simpa only [N] using! hstop)
  simpa only [Z, N, V, K, X, T, max_self, one_mul, mul_one] using! hdirect

end Problem520
end Erdos

#print axioms Erdos.Problem520.exists_integral_harperMovingHeight_twoThird_le_iterated

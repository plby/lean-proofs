import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProductBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProductWords

/-!
# Summable bounds for products with smooth polynomial multipliers

The actual local product rule and reverse induction on the original
direction words give compact-uniform summable majorants for every
derivative of a product. Each polynomial multiplier bound consumes only
finitely many of the available rapid-decay weights. The argument retains
the given word order and does not assume a bound for the final product.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification FourierParameter

variable {U : Opens ℂ}

/-- Finite Leibniz recursion produces an actual nonnegative summable
majorant for every original derivative word of the product. -/
theorem polynomial_mul_rapid_majorant (s : List ℂ) :
    ∀ (m c : Coefficients), SmoothPolynomiallyBoundedCoefficients U m →
      SmoothRapidCoefficients U c → ∀ (K : Set U), IsCompact K → ∀ r : ℕ,
      ∃ u : Frequency → ℝ, (∀ k, 0 ≤ u k) ∧ Summable u ∧
        ∀ b ∈ K, ∀ k, (1 + ‖integerFrequency k‖) ^ r *
          ‖iteratedDirectionalDerivativeList s (fun z => m k z * c k z) (b : ℂ)‖ ≤ u k := by
  induction s using List.reverseRecOn with
  | nil =>
    intro m c hm hc K hK r
    obtain ⟨C, n, hC, hboundm⟩ := hm.growth [] K hK
    obtain ⟨u, hu, hsum, hboundc⟩ := hc.majorant [] K hK (r + n)
    refine ⟨fun k => C * u k, fun k => mul_nonneg hC (hu k), hsum.mul_left C, ?_⟩
    intro b hb k
    change (1 + ‖integerFrequency k‖) ^ r * ‖m k (b : ℂ) * c k (b : ℂ)‖ ≤ C * u k
    rw [norm_mul]
    calc
      (1 + ‖integerFrequency k‖) ^ r * (‖m k (b : ℂ)‖ * ‖c k (b : ℂ)‖) ≤
        (1 + ‖integerFrequency k‖) ^ r *
          ((C * (1 + ‖integerFrequency k‖) ^ n) * ‖c k (b : ℂ)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hboundm b hb k) (norm_nonneg _)) (by positivity)
      _ = C * ((1 + ‖integerFrequency k‖) ^ (r + n) * ‖c k (b : ℂ)‖) := by
        rw [pow_add]
        ring
      _ ≤ C * u k := mul_le_mul_of_nonneg_left (hboundc b hb k) hC
  | append_singleton s v ih =>
    intro m c hm hc K hK r
    obtain ⟨u, hu, hsumu, hboundu⟩ :=
      ih (baseDiff v m) c (hm.baseDiff v) hc K hK r
    obtain ⟨w, hw, hsumw, hboundw⟩ :=
      ih m (baseDiff v c) hm (hc.baseDiff v) K hK r
    refine ⟨fun k => u k + w k, fun k => add_nonneg (hu k) (hw k),
      hsumu.add hsumw, ?_⟩
    intro b hb k
    rw [(word_append_mul_eqOn (hm.smooth k) (hc.smooth k) s v) b.property]
    calc
      (1 + ‖integerFrequency k‖) ^ r *
          ‖iteratedDirectionalDerivativeList s
              (fun z => fderiv ℝ (m k) z v * c k z) (b : ℂ) +
            iteratedDirectionalDerivativeList s
              (fun z => m k z * fderiv ℝ (c k) z v) (b : ℂ)‖ ≤
        (1 + ‖integerFrequency k‖) ^ r *
          (‖iteratedDirectionalDerivativeList s
              (fun z => fderiv ℝ (m k) z v * c k z) (b : ℂ)‖ +
            ‖iteratedDirectionalDerivativeList s
              (fun z => m k z * fderiv ℝ (c k) z v) (b : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = (1 + ‖integerFrequency k‖) ^ r *
            ‖iteratedDirectionalDerivativeList s
              (fun z => fderiv ℝ (m k) z v * c k z) (b : ℂ)‖ +
          (1 + ‖integerFrequency k‖) ^ r *
            ‖iteratedDirectionalDerivativeList s
              (fun z => m k z * fderiv ℝ (c k) z v) (b : ℂ)‖ := mul_add _ _ _
      _ ≤ u k + w k := add_le_add (hboundu b hb k) (hboundw b hb k)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

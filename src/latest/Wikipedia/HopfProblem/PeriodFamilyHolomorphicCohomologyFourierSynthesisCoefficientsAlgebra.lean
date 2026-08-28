import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsWords

/-!
# Algebra of smooth rapidly decreasing coefficient families

Addition and complex constant multiplication preserve the actual
compact-uniform derivative bounds. More generally, multiplication by a
frequency-only polynomially bounded sequence costs finitely many of the
available polynomial weights. In particular the exact coordinate
multiplier from real torus differentiation preserves the condition.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification FourierParameter

namespace SmoothRapidCoefficients

variable {U : Opens ℂ} {c d : Coefficients}

/-- The sum of two actual coefficient families has the sum of their majorants. -/
theorem add (hc : SmoothRapidCoefficients U c) (hd : SmoothRapidCoefficients U d) :
    SmoothRapidCoefficients U (c + d) where
  smooth k := (hc.smooth k).add (hd.smooth k)
  majorant := by
    intro s K hK r
    obtain ⟨u, hu, hsumu, hboundu⟩ := hc.majorant s K hK r
    obtain ⟨v, hv, hsumv, hboundv⟩ := hd.majorant s K hK r
    refine ⟨fun k => u k + v k, fun k => add_nonneg (hu k) (hv k),
      hsumu.add hsumv, ?_⟩
    intro b hb k
    change (1 + ‖integerFrequency k‖) ^ r *
      ‖iteratedDirectionalDerivativeList s (fun z => c k z + d k z) (b : ℂ)‖ ≤ _
    rw [(word_add_eqOn (hc.smooth k) (hd.smooth k) s) b.property]
    calc
      (1 + ‖integerFrequency k‖) ^ r *
          ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ) +
            iteratedDirectionalDerivativeList s (d k) (b : ℂ)‖ ≤
        (1 + ‖integerFrequency k‖) ^ r *
          (‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖ +
            ‖iteratedDirectionalDerivativeList s (d k) (b : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = (1 + ‖integerFrequency k‖) ^ r *
            ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖ +
          (1 + ‖integerFrequency k‖) ^ r *
            ‖iteratedDirectionalDerivativeList s (d k) (b : ℂ)‖ := mul_add _ _ _
      _ ≤ u k + v k := add_le_add (hboundu b hb k) (hboundv b hb k)

/-- A frequency-only polynomial multiplier consumes its polynomial degree
from the original bounds, without changing the base-derivative words. -/
theorem frequency_mul (hc : SmoothRapidCoefficients U c) (a : Frequency → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖integerFrequency k‖) ^ m) :
    SmoothRapidCoefficients U (fun k z => a k * c k z) where
  smooth k := contDiffOn_const.mul (hc.smooth k)
  majorant := by
    intro s K hK r
    obtain ⟨u, hu, hsum, hbound⟩ := hc.majorant s K hK (r + m)
    refine ⟨fun k => C * u k, fun k => mul_nonneg hC (hu k), hsum.mul_left C, ?_⟩
    intro b hb k
    rw [(word_const_mul_eqOn (hc.smooth k) (a k) s) b.property, norm_mul]
    calc
      (1 + ‖integerFrequency k‖) ^ r *
          (‖a k‖ * ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖) ≤
        (1 + ‖integerFrequency k‖) ^ r *
          ((C * (1 + ‖integerFrequency k‖) ^ m) *
            ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _)) (by positivity)
      _ = C * ((1 + ‖integerFrequency k‖) ^ (r + m) *
            ‖iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖) := by
        rw [pow_add]
        ring
      _ ≤ C * u k := mul_le_mul_of_nonneg_left (hbound b hb k) hC

/-- Multiplication by a fixed complex number preserves every original weighted bound. -/
theorem const_mul (hc : SmoothRapidCoefficients U c) (a : ℂ) :
    SmoothRapidCoefficients U (fun k z => a * c k z) := by
  apply hc.frequency_mul (fun _ => a) (norm_nonneg a) 0
  intro k
  simp only [pow_zero, mul_one, le_refl]

/-- The actual Fourier multiplier for one real coordinate derivative
costs one available polynomial weight. -/
theorem frequencyDiff (hc : SmoothRapidCoefficients U c) (j : Fin 4) :
    SmoothRapidCoefficients U (FourierSynthesis.frequencyDiff j c) := by
  unfold FourierSynthesis.frequencyDiff
  apply hc.frequency_mul (fun k => 2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ))
    (norm_nonneg (2 * (Real.pi : ℂ) * Complex.I)) 1
  intro k
  have hcoord : ‖(k j : ℂ)‖ ≤ 1 + ‖integerFrequency k‖ := by
    calc
      ‖(k j : ℂ)‖ = ‖(k j : ℝ)‖ := by
        rw [← Complex.ofReal_intCast, Complex.norm_real]
      _ ≤ ‖integerFrequency k‖ := norm_le_pi_norm (integerFrequency k) j
      _ ≤ 1 + ‖integerFrequency k‖ := le_add_of_nonneg_left zero_le_one
  rw [norm_mul, pow_one]
  exact mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)

end SmoothRapidCoefficients

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

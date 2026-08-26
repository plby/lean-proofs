import ErdosProblems.Erdos67b.MRExceptionalSelection
import ErdosProblems.Erdos67b.MRSparseCofactorSamples

/-!
# The small-additional-prime exceptional integral

Actual points selected from the small-prime part of the no-small-block
class satisfy both hypotheses of the proved sampled bound. The exact
complementary large-prime integral is retained as the remaining term.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

def mrSmallPrimeFrequencySet (E : Set ℝ) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ) : Set ℝ :=
  E ∩ {t | ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖ ≤ V}

def mrLargePrimeFrequencySet (E : Set ℝ) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ) : Set ℝ :=
  E ∩ {t | V < ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖}

theorem measurableSet_mrSmallPrimeFrequencySet
    {E : Set ℝ} (hE : MeasurableSet E) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ) :
    MeasurableSet (mrSmallPrimeFrequencySet E P f V) :=
  hE.inter (measurableSet_le (continuous_logarithmicDirichletPolynomial P _).norm.measurable measurable_const)

theorem measurableSet_mrLargePrimeFrequencySet
    {E : Set ℝ} (hE : MeasurableSet E) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ) :
    MeasurableSet (mrLargePrimeFrequencySet E P f V) :=
  hE.inter (measurableSet_lt measurable_const (continuous_logarithmicDirichletPolynomial P _).norm.measurable)

theorem measurableSet_mrArithmeticNoSmall
    (eta p₁ q₁ : ℝ) (f : ℕ → ℂ) (J : ℕ) :
    MeasurableSet (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :=
  measurableSet_mrNoSmallFrequencyClass
    (fun j ↦ measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _ j) J

/-- Exact partition at the prime threshold, including its equality case. -/
theorem mrPrimeThreshold_indicator_split
    (E : Set ℝ) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    E.indicator g t = (mrSmallPrimeFrequencySet E P f V).indicator g t +
      (mrLargePrimeFrequencySet E P f V).indicator g t := by
  classical
  by_cases ht : t ∈ E
  · by_cases hsmall : ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖ ≤ V
    · simp [mrSmallPrimeFrequencySet, mrLargePrimeFrequencySet, Set.indicator, ht, hsmall, not_lt.mpr hsmall]
    · have hlarge : V < ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖ := lt_of_not_ge hsmall
      simp [mrSmallPrimeFrequencySet, mrLargePrimeFrequencySet, Set.indicator, ht, hsmall, hlarge]
  · simp [mrSmallPrimeFrequencySet, mrLargePrimeFrequencySet, Set.indicator, ht]

theorem mrPrimeThreshold_integral_split
    {E : Set ℝ} (hE : MeasurableSet E) (P : Finset ℕ) (f : ℕ → ℂ) (V : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    (∫ t in a..b, E.indicator g t) =
      (∫ t in a..b, (mrSmallPrimeFrequencySet E P f V).indicator g t) +
      ∫ t in a..b, (mrLargePrimeFrequencySet E P f V).indicator g t := by
  have hint (A : Set ℝ) (hA : MeasurableSet A) : IntervalIntegrable (A.indicator g) volume a b := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hg.intervalIntegrable a b)).indicator hA
  calc
    _ = ∫ t in a..b, (mrSmallPrimeFrequencySet E P f V).indicator g t +
        (mrLargePrimeFrequencySet E P f V).indicator g t :=
      intervalIntegral.integral_congr (fun t _ ↦ mrPrimeThreshold_indicator_split E P f V g t)
    _ = _ := intervalIntegral.integral_add (hint _ (measurableSet_mrSmallPrimeFrequencySet hE P f V))
      (hint _ (measurableSet_mrLargePrimeFrequencySet hE P f V))

/-- The explicit optimized count bound at one selected original level. -/
def mrNoSmallOptimizedCountBudget (eta p₁ q₁ : ℝ) (j : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
    mrOptimizedPrimeSampleBudget T (mrScheduledParameter eta p₁ q₁ j r)
      (mrThresholdExponent eta (j : ℝ))

/-- The sampled cofactor budget, including the factor two from selection. -/
def mrExceptionalSmallPrimeEnergyBudget (eta p₁ q₁ : ℝ) (j U X : ℕ) (T V : ℝ) : ℝ :=
  2 * V ^ 2 * mrSparseCofactorSampleBudget (mrNoSmallOptimizedCountBudget eta p₁ q₁ j T) U X T

/-- The small-additional-prime integral on the actual no-small-block class. -/
theorem mrArithmetic_noSmall_smallPrime_integral_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J)
    (blocks : Finset (ℕ × ℕ)) (I Jaux : ℕ × ℕ) (P : Finset ℕ)
    (hL : 0 < Jaux.1) (hU : 0 < Jaux.2) (hUL : Jaux.2 ≤ 2 * Jaux.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T V : ℝ} (hT : 1 ≤ T) :
    (∫ t in -T..T,
      (mrSmallPrimeFrequencySet
        (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) P f V).indicator
        (fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
            (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) ≤
      mrExceptionalSmallPrimeEnergyBudget eta p₁ q₁ j Jaux.2 X T V := by
  let E := mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J
  let g : ℝ → ℝ := fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
    logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
      (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2
  have hg : Continuous g := ((continuous_logarithmicDirichletPolynomial _ _).mul
    (continuous_logarithmicDirichletPolynomial _ _)).norm.pow 2
  have hE : MeasurableSet E := measurableSet_mrArithmeticNoSmall eta p₁ q₁ f J
  obtain ⟨S, hS, hsep, hint⟩ := mrExists_separated_samples_ge_integral
    (measurableSet_mrSmallPrimeFrequencySet hE P f V) hg (fun t ↦ sq_nonneg _) (by linarith : 0 ≤ T)
  have hsample := mrArithmetic_noSmall_smallPrime_product_le heta0 heta1 hp hq hlogq hbudget
    hj hjJ blocks I Jaux P hL hU hUL hX hbound S hT
    (fun t ht ↦ (hS t ht).2) hsep
    (fun t ht ↦ (hS t ht).1.1) (fun t ht ↦ (hS t ht).1.2)
  calc
    _ ≤ 2 * ∑ t ∈ S, g t := hint
    _ ≤ 2 * (V ^ 2 * mrSparseCofactorSampleBudget
        (mrNoSmallOptimizedCountBudget eta p₁ q₁ j T) Jaux.2 X T) :=
      mul_le_mul_of_nonneg_left hsample (by norm_num)
    _ = _ := by unfold mrExceptionalSmallPrimeEnergyBudget; ring

/-- The exact large-additional-prime energy is the residual term after
paying the proved small-prime integral budget. -/
theorem mrArithmetic_noSmall_product_integral_le_small_add_large
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J)
    (blocks : Finset (ℕ × ℕ)) (I Jaux : ℕ × ℕ) (P : Finset ℕ)
    (hL : 0 < Jaux.1) (hU : 0 < Jaux.2) (hUL : Jaux.2 ≤ 2 * Jaux.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T V : ℝ} (hT : 1 ≤ T) :
    (∫ t in -T..T,
      (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J).indicator
        (fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
            (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) ≤
      mrExceptionalSmallPrimeEnergyBudget eta p₁ q₁ j Jaux.2 X T V +
        ∫ t in -T..T,
          (mrLargePrimeFrequencySet
            (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) P f V).indicator
            (fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
              logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
                (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t := by
  have hg : Continuous (fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
        (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) :=
    ((continuous_logarithmicDirichletPolynomial _ _).mul
      (continuous_logarithmicDirichletPolynomial _ _)).norm.pow 2
  rw [mrPrimeThreshold_integral_split (measurableSet_mrArithmeticNoSmall eta p₁ q₁ f J) P f V hg]
  exact add_le_add
    (mrArithmetic_noSmall_smallPrime_integral_le heta0 heta1 hp hq hlogq hbudget hj hjJ
      blocks I Jaux P hL hU hUL hX hbound hT) le_rfl

end

end Erdos67b

import ErdosProblems.Erdos67b.PrimeGraphFourier
import ErdosProblems.Erdos67b.LogGraphCorrelation

/-!
# Small and large Fourier frequencies in the prime graph

The exceptional frequencies depend only on the deterministic prime
multiplier. A finite first-moment hypothesis is kept explicit; the
substantial short-interval theorem supplying it is a separate obligation.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

/-- Frequencies at which the graph multiplier reaches the chosen cutoff. -/
def primeGraphLargeFrequencies (T h : ℕ) (s : Finset ℕ) (θ : ℝ) : Finset ℕ :=
  (Finset.range T).filter fun t ↦ θ ≤ ‖primeGraphMultiplier T h s (t : ℤ)‖

/-- Triangle inequality for the exact Fourier expansion. -/
theorem norm_primeGraphMean_le_fourier {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (hT : ∀ p ∈ s, H + p * h ≤ T) :
    ‖primeGraphMean b h s‖ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      ‖blockFourier T b (t : ℤ)‖ ^ 2 * ‖primeGraphMultiplier T h s (t : ℤ)‖ := by
  rw [primeGraphMean_eq_fourier b h s hs hT, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ t ∈ Finset.range T,
        ‖(‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * primeGraphMultiplier T h s (t : ℤ)‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]

/-- Parseval controls all small frequencies, while the large frequencies
need only first powers of the block transform. -/
theorem norm_primeGraphMean_le_largeFrequencies {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T) (hb : ∀ j, ‖b j‖ ≤ 1)
    {θ M : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hmult : ∀ t ∈ Finset.range T, ‖primeGraphMultiplier T h s (t : ℤ)‖ ≤ M) :
    ‖primeGraphMean b h s‖ ≤ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ primeGraphLargeFrequencies T h s θ, ‖blockFourier T b (t : ℤ)‖ := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hpoint (t : ℕ) (ht : t ∈ Finset.range T) :
      ‖blockFourier T b (t : ℤ)‖ ^ 2 * ‖primeGraphMultiplier T h s (t : ℤ)‖ ≤
        θ * ‖blockFourier T b (t : ℤ)‖ ^ 2 +
          if θ ≤ ‖primeGraphMultiplier T h s (t : ℤ)‖ then
            H * M * ‖blockFourier T b (t : ℤ)‖ else 0 := by
    have hx : ‖blockFourier T b (t : ℤ)‖ ≤ H := by
      simpa using norm_blockFourier_le T b t hb
    by_cases htlarge : θ ≤ ‖primeGraphMultiplier T h s (t : ℤ)‖
    · rw [if_pos htlarge]
      have hprod : ‖blockFourier T b (t : ℤ)‖ ^ 2 *
          ‖primeGraphMultiplier T h s (t : ℤ)‖ ≤ H * M * ‖blockFourier T b (t : ℤ)‖ := by
        calc
          _ ≤ ‖blockFourier T b (t : ℤ)‖ ^ 2 * M :=
            mul_le_mul_of_nonneg_left (hmult t ht) (sq_nonneg _)
          _ ≤ (H : ℝ) * M * ‖blockFourier T b (t : ℤ)‖ := by
            nlinarith [mul_nonneg hM (norm_nonneg (blockFourier T b (t : ℤ)))]
      linarith [mul_nonneg hθ (sq_nonneg ‖blockFourier T b (t : ℤ)‖)]
    · rw [if_neg htlarge, add_zero]
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge htlarge)
        (sq_nonneg ‖blockFourier T b (t : ℤ)‖)
      simpa only [mul_comm] using h
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
    ← Finset.mul_sum] at hsum
  have hparseval := sum_blockFourier_norm_sq_le b hHT hb
  have htotal := hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left hparseval hθ) le_rfl)
  calc
    _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ‖blockFourier T b (t : ℤ)‖ ^ 2 * ‖primeGraphMultiplier T h s (t : ℤ)‖ :=
      norm_primeGraphMean_le_fourier b h s hs hT
    _ ≤ (T : ℝ)⁻¹ * (θ * (T * H) + H * M *
        ∑ t ∈ primeGraphLargeFrequencies T h s θ, ‖blockFourier T b (t : ℤ)‖) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by field_simp

/-- Finite expectation is monotone for real-valued observables. -/
theorem logProbExpectation_mono {L U : ℕ} (F G : ℕ → ℝ)
    (hFG : ∀ n ∈ logProbWindow L U, F n ≤ G n) :
    logProbExpectation L U F ≤ logProbExpectation L U G := by
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left (hFG n.1 n.2) (by positivity)

/-- Finite Jensen for the norm under logarithmic sampling. -/
theorem norm_logProbExpectation_le_expectation_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L U : ℕ) (F : ℕ → E) :
    ‖logProbExpectation L U F‖ ≤ logProbExpectation L U (fun n ↦ ‖F n‖) := by
  calc
    _ ≤ ∑ n : LogProbIndex L U, ‖(logProbWeightNN L U n : ℝ) • F n.1‖ := norm_sum_le _ _
    _ = _ := by
      simp only [logProbExpectation, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg _), smul_eq_mul]

/-- Average the deterministic large-frequency bound. The first-moment
assumption is only needed on the fixed exceptional frequency set. -/
theorem norm_logProb_primeGraphMean_le_of_fourier_first_moment
    {L U H T : ℕ} [NeZero T] (hL : 0 < L) (hLU : L ≤ U)
    (F : ℕ → ℂ) (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hF : ∀ n, 0 < n → ‖F n‖ ≤ 1)
    {θ M Z : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hmult : ∀ t ∈ Finset.range T, ‖primeGraphMultiplier T h s (t : ℤ)‖ ≤ M)
    (hfirst : ∀ t ∈ primeGraphLargeFrequencies T h s θ,
      logProbExpectation L U (fun n ↦ ‖blockFourier T (finiteSequenceBlock F H n) (t : ℤ)‖) ≤ Z) :
    ‖logProbExpectation L U (fun n ↦ primeGraphMean (finiteSequenceBlock F H n) h s)‖ ≤
      θ * H + ((H : ℝ) * M / T) * (primeGraphLargeFrequencies T h s θ).card * Z := by
  have hpoint (n : ℕ) : ‖primeGraphMean (finiteSequenceBlock F H n) h s‖ ≤
      θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ primeGraphLargeFrequencies T h s θ,
          ‖blockFourier T (finiteSequenceBlock F H n) (t : ℤ)‖ :=
    norm_primeGraphMean_le_largeFrequencies _ h s hs hHT hT
      (fun j ↦ hF (n + j.1 + 1) (by omega)) hθ hM hmult
  have hweights : ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) = 1 := by
    exact_mod_cast sum_logProbWeightNN hL hLU
  have hexpand : logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
      ∑ t ∈ primeGraphLargeFrequencies T h s θ,
        ‖blockFourier T (finiteSequenceBlock F H n) (t : ℤ)‖) =
      θ * H + ((H : ℝ) * M / T) * ∑ t ∈ primeGraphLargeFrequencies T h s θ,
        logProbExpectation L U (fun n ↦ ‖blockFourier T (finiteSequenceBlock F H n) (t : ℤ)‖) := by
    simp only [logProbExpectation, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hweights, one_mul]
    congr 1
    simp_rw [mul_left_comm (logProbWeightNN L U _ : ℝ) ((H : ℝ) * M / T)]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ ≤ logProbExpectation L U (fun n ↦ ‖primeGraphMean (finiteSequenceBlock F H n) h s‖) :=
      norm_logProbExpectation_le_expectation_norm _ _ _
    _ ≤ logProbExpectation L U (fun n ↦ θ * H + ((H : ℝ) * M / T) *
        ∑ t ∈ primeGraphLargeFrequencies T h s θ,
          ‖blockFourier T (finiteSequenceBlock F H n) (t : ℤ)‖) :=
      logProbExpectation_mono _ _ (fun n _ ↦ hpoint n)
    _ = _ := hexpand
    _ ≤ θ * H + ((H : ℝ) * M / T) * ∑ _t ∈ primeGraphLargeFrequencies T h s θ, Z := by
      gcongr
      exact hfirst _ ‹_›
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end

end Erdos67b

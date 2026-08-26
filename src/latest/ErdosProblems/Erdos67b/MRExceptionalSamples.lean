import ErdosProblems.Erdos67b.MRDiscreteSampling
import ErdosProblems.Erdos67b.MRNarrowPrimePartition

/-!
# Finite sample counts on the actual no-small-block class

Every sample belongs to a large-value set of a narrow prime subblock.
The discrete prime moment bounds those sets, with all integer endpoints
and prime-line coefficient estimates discharged. The finite bound here
still requires its source parameter optimization and the sparse Halász
energy estimates before it yields the exceptional-frequency energy saving.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

theorem mrSum_primeLine_normSq_le_tail
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {L N : ℕ} (hL : 0 < L) (hlo : ∀ p ∈ P, L ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (∑ p ∈ P, ‖mrFinitePrimeLineCoefficient f p‖ ^ 2) ≤ 2 / (L : ℝ) := by
  have hsub : P ⊆ Finset.Ioo (L - 1) (N + 1) := by
    intro p hp
    have hpl := hlo p hp
    have hpn := hhi p hp
    exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := pow_le_pow_left₀ (norm_nonneg (mrFinitePrimeLineCoefficient f p))
        (norm_mrFinitePrimeLineCoefficient_le hbound (hP p hp).pos) 2
      simpa only [inv_pow] using hh
    _ ≤ ∑ p ∈ Finset.Ioo (L - 1) (N + 1), ((p : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ 2 / (((L - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (α := ℝ) (L - 1) (N + 1)
    _ = _ := by
      have hh : ((L - 1 : ℕ) : ℝ) + 1 = L := by exact_mod_cast Nat.sub_add_cancel hL
      rw [hh]

/-- Explicit cardinality budget for prime-line coefficients in `[L,N]`. -/
def mrPrimeLineSampleBudget (L N k : ℕ) (T V : ℝ) : ℝ :=
  ((3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
    ((k.factorial : ℝ) * (2 / (L : ℝ)) ^ k)) / V ^ (2 * k)

theorem mrPrimeLine_sampled_largeValues_card_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {L N k : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hlo : ∀ p ∈ P, L ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hlarge : ∀ t ∈ S, V ≤ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖) :
    (S.card : ℝ) ≤ mrPrimeLineSampleBudget L N k T V := by
  have hlog : 0 ≤ Real.log (N ^ k : ℕ) := Real.log_nonneg (by exact_mod_cast pow_pos hN k)
  have hmass := mrSum_primeLine_normSq_le_tail hP hL hlo hhi hbound
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) hmass k
  apply (mrPrimePolynomial_sampled_largeValues_card_le (k := k) hP hN hhi
    (mrFinitePrimeLineCoefficient f) S hT hV hST hsep hlarge).trans
  unfold mrPrimeLineSampleBudget
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)

/-- A finite cover by large-value sets bounds the cardinality by the sum
of the individual prime-line sample budgets. -/
theorem mrSample_card_le_sum_primeLine_budgets
    (I : Finset ℕ) (P : ℕ → Finset ℕ) (L N k : ℕ → ℕ) (V : ℕ → ℝ)
    (hP : ∀ r ∈ I, ∀ p ∈ P r, p.Prime)
    (hL : ∀ r ∈ I, 0 < L r) (hN : ∀ r ∈ I, 0 < N r)
    (hlo : ∀ r ∈ I, ∀ p ∈ P r, L r ≤ p) (hhi : ∀ r ∈ I, ∀ p ∈ P r, p ≤ N r)
    (hV : ∀ r ∈ I, 0 < V r)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hcover : ∀ t ∈ S, ∃ r ∈ I,
      V r ≤ ‖logarithmicDirichletPolynomial (P r) (mrFinitePrimeLineCoefficient f) t‖) :
    (S.card : ℝ) ≤ ∑ r ∈ I, mrPrimeLineSampleBudget (L r) (N r) (k r) T (V r) := by
  classical
  let E : ℕ → Finset ℝ := fun r ↦ S.filter (fun t ↦
    V r ≤ ‖logarithmicDirichletPolynomial (P r) (mrFinitePrimeLineCoefficient f) t‖)
  have hsub : S ⊆ I.biUnion E := by
    intro t ht
    obtain ⟨r, hr, htlarge⟩ := hcover t ht
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨ht, htlarge⟩⟩
  have hcard : S.card ≤ ∑ r ∈ I, (E r).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ r ∈ I, ((E r).card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      exact mrPrimeLine_sampled_largeValues_card_le (hP r hr) (hL r hr) (hN r hr)
        (hlo r hr) (hhi r hr) hbound (E r) hT (hV r hr)
        (fun t ht ↦ hST t (Finset.mem_filter.mp ht).1)
        (fun s hs t ht hne ↦ hsep s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)
        (fun t ht ↦ (Finset.mem_filter.mp ht).2)

/-- Every actual no-small-block sample is counted using the prime
polynomials of any selected positive level `j ≤ J`. -/
theorem mrArithmetic_noSmall_sample_card_le
    (eta p₁ q₁ : ℝ) {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) (k : ℕ → ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hU : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :
    (S.card : ℝ) ≤ ∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
      mrPrimeLineSampleBudget (mrScheduledNarrowInterval eta p₁ q₁ j r).1
        (mrScheduledNarrowInterval eta p₁ q₁ j r).2 (k r) T
        (Real.exp (-mrThresholdExponent eta (j : ℝ) * mrScheduledParameter eta p₁ q₁ j r)) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hH : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by
    unfold mrLogBlockResolution
    positivity
  apply mrSample_card_le_sum_primeLine_budgets
    (mrScheduledSubblocks eta p₁ q₁ j) (mrScheduledPrimeSubblock eta p₁ q₁ j)
    (fun r ↦ (mrScheduledNarrowInterval eta p₁ q₁ j r).1)
    (fun r ↦ (mrScheduledNarrowInterval eta p₁ q₁ j r).2) k
    (fun r ↦ Real.exp (-mrThresholdExponent eta (j : ℝ) * mrScheduledParameter eta p₁ q₁ j r))
    (fun r _ ↦ mrScheduledPrimeSubblock_prime eta p₁ q₁ j r)
    (fun r _ ↦ mrNarrowPrimeInterval_lower_pos _ r)
    (fun r _ ↦ mrNarrowPrimeInterval_upper_pos hH r)
    (fun r _ p hp ↦ (mrScheduledPrimeSubblock_integer_bounds hH p hp).1)
    (fun r _ p hp ↦ (mrScheduledPrimeSubblock_integer_bounds hH p hp).2)
    (fun _ _ ↦ Real.exp_pos _) hbound S hT hST hsep
  intro t ht
  obtain ⟨r, hr, hlarge⟩ := mrNoSmall_primeBlock_large (mrScheduledSubblocks eta p₁ q₁)
    (fun i r ↦ logarithmicDirichletPolynomial (mrScheduledPrimeSubblock eta p₁ q₁ i r)
      (mrFinitePrimeLineCoefficient f))
    (fun i r ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i r))
    hj hjJ (hU t ht)
  exact ⟨r, hr, hlarge.le⟩

end

end Erdos67b

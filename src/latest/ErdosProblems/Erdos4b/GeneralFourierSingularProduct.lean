/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSingularFactor

/-!
# Convergence and nonvanishing of the rough singular product

Away from the prime divisors of a positive exceptional integer, the
singular-factor deviation is reciprocal-square summable. The remaining
set of primes is finite. No first-order exceptional term is discarded.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def roughDoubledFourierSingularFactor {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) : ℂ :=
  if w < p then doubledFourierSingularFactor edges companion p else 1

theorem summable_primeDivisorIndicator {M : ℕ} (hM : 0 < M) :
    Summable (fun p : Nat.Primes ↦ if p.val ∣ M then (1 : ℝ) else 0) := by
  classical
  have hn : Summable (fun n : ℕ ↦ if n ∈ M.primeFactors then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := M.primeFactors) (fun n hn ↦ if_neg hn)
  have hsub := hn.subtype Nat.Prime
  convert! hsub using 1
  ext p
  simp [Function.comp_def, Nat.mem_primeFactors, p.property, hM.ne']

theorem summable_prime_reciprocalSquare :
    Summable (fun p : Nat.Primes ↦ (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hn : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) := by
    simpa only [one_div] using (Real.summable_nat_pow_inv (p := 2)).mpr (by decide)
  exact hn.subtype Nat.Prime

theorem doubledFourierExceptionalCount_div_le_indicator
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p M : ℕ} (hp : p.Prime) (hedgeCard : (edges p).card ≤ Fintype.card ι)
    (hgeneric : ¬p ∣ M → edges p = ∅ ∧ companion p = true) :
    (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℝ) / p ≤
      (Fintype.card (ι ⊕ ι) : ℝ) * (if p ∣ M then 1 else 0) := by
  have hcount : (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℝ) ≤
      Fintype.card (ι ⊕ ι) := by
    exact_mod_cast (show doubledFourierExceptionalCount Finset.univ (edges p) (companion p) ≤
      Fintype.card (ι ⊕ ι) from by
      simpa only [univ_disjSum_univ_eq, Finset.card_univ] using
        doubledFourierExceptionalCount_le_double_card Finset.univ (edges p) (companion p)
          (by simpa only [Finset.card_univ] using hedgeCard))
  by_cases hpM : p ∣ M
  · rw [if_pos hpM, mul_one]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    apply (div_le_iff₀ hp0).mpr
    exact hcount.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hp1)
  · obtain ⟨he, hc⟩ := hgeneric hpM
    simp [hpM, doubledFourierExceptionalCount, he, hc]

theorem summable_norm_roughDoubledFourierSingularFactor_sub_one
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M w : ℕ} (hM : 0 < M) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) :
    Summable (fun p : Nat.Primes ↦
      ‖roughDoubledFourierSingularFactor w edges companion p - 1‖) := by
  let N := Fintype.card (ι ⊕ ι)
  let C := pairProductErrorConstant N
  have hC : 0 ≤ C := pairProductErrorConstant_nonneg N
  have hsum := ((summable_prime_reciprocalSquare.mul_left C).add
    ((summable_primeDivisorIndicator hM).mul_left (N : ℝ))).mul_left ((2 : ℝ) ^ N)
  apply Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) _ hsum
  intro p
  by_cases hwp : w < p.val
  · simp only [roughDoubledFourierSingularFactor, if_pos hwp]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    have hpCard : 7 * (N : ℝ) ≤ p := hcard.trans (by exact_mod_cast hwp.le)
    apply (norm_doubledFourierSingularFactor_sub_one_le edges companion hp2 hpCard).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (by dsimp [C, N]; rw [mul_one_div])
      (doubledFourierExceptionalCount_div_le_indicator edges companion p.property
        (hedgeCard p hwp) (hgeneric p hwp))
  · simp only [roughDoubledFourierSingularFactor, if_neg hwp, sub_self, norm_zero]
    positivity

theorem multipliable_roughDoubledFourierSingularFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M w : ℕ} (hM : 0 < M) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) :
    Multipliable (fun p : Nat.Primes ↦ roughDoubledFourierSingularFactor w edges companion p) := by
  have hsum := summable_norm_roughDoubledFourierSingularFactor_sub_one
    edges companion hM hcard hedgeCard hgeneric
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

theorem roughDoubledFourierSingularFactor_ne_zero
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {w : ℕ} (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (p : Nat.Primes) : roughDoubledFourierSingularFactor w edges companion p ≠ 0 := by
  by_cases hwp : w < p.val
  · simp only [roughDoubledFourierSingularFactor, if_pos hwp]
    have hpw : (w : ℝ) ≤ p := by exact_mod_cast hwp.le
    have hn : (0 : ℝ) ≤ Fintype.card (ι ⊕ ι) := Nat.cast_nonneg _
    have hhalf := half_le_norm_doubledFourierSingularFactor edges companion
      (by exact_mod_cast p.property.two_le) (by linarith) (hedgeCard p hwp)
    intro hz
    rw [hz, norm_zero] at hhalf
    norm_num at hhalf
  · simp [roughDoubledFourierSingularFactor, hwp]

theorem tprod_roughDoubledFourierSingularFactor_ne_zero
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M w : ℕ} (hM : 0 < M) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) :
    (∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p) ≠ 0 := by
  have hsum := summable_norm_roughDoubledFourierSingularFactor_sub_one
    edges companion hM hcard hedgeCard hgeneric
  have hne : ∀ p : Nat.Primes,
      1 + (roughDoubledFourierSingularFactor w edges companion p - 1) ≠ 0 := by
    intro p
    simpa only [add_sub_cancel] using
      roughDoubledFourierSingularFactor_ne_zero edges companion hcard hedgeCard p
  simpa only [add_sub_cancel] using tprod_one_add_ne_zero_of_summable hne hsum

end

end Erdos4b

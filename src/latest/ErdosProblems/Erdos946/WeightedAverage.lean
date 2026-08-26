/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.MertensRichert
import ErdosProblems.Erdos946.RichertWeights

/-! # Finite averaging of the distinct-prime Richert weight -/

open scoped BigOperators

namespace Erdos946.WeightedAverage

open Erdos851 RichertWeights MertensRichert SieveWindow AffineSieve

noncomputable section

theorem distinctRichertWeight_eq_primeSum {m y Y : ℕ}
    (hm : m ≠ 0)
    (hrough : ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ m) :
    distinctRichertWeight m Y =
      ∑ p ∈ sievePrimes y Y, if p ∣ m then richertTerm Y p else 0 := by
  have htrunc : (∑ p ∈ m.primeFactors, richertTerm Y p) =
      ∑ p ∈ m.primeFactors.filter (fun p ↦ p ≤ Y), richertTerm Y p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hYp : Y ≤ p := by
      have hn : ¬p ≤ Y := fun h ↦ hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
      omega
    exact richertTerm_eq_zero_of_le hYp
  have hsets : m.primeFactors.filter (fun p ↦ p ≤ Y) =
      (sievePrimes y Y).filter (fun p ↦ p ∣ m) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_sievePrimes]
    constructor
    · rintro ⟨⟨hp, hpm, _⟩, hpY⟩
      have hyp : y < p := by
        by_contra h
        exact hrough p hp (Nat.le_of_not_gt h) hpm
      exact ⟨⟨hyp, hpY, hp⟩, hpm⟩
    · rintro ⟨⟨_, hpY, hp⟩, hpm⟩
      exact ⟨⟨hp, hpm, hm⟩, hpY⟩
  unfold distinctRichertWeight
  rw [htrunc, hsets, Finset.sum_filter]

theorem sum_distinctRichertWeight_eq_prime_counts
    (S : Finset ℕ) (F : ℕ → ℕ) {y Y : ℕ}
    (hF : ∀ n ∈ S, F n ≠ 0)
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ F n) :
    (∑ n ∈ S, distinctRichertWeight (F n) Y) =
      ∑ p ∈ sievePrimes y Y,
        richertTerm Y p * ((S.filter fun n ↦ p ∣ F n).card : ℝ) := by
  have hsum : (∑ n ∈ S, distinctRichertWeight (F n) Y) =
      ∑ n ∈ S, ∑ p ∈ sievePrimes y Y,
        if p ∣ F n then richertTerm Y p else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact distinctRichertWeight_eq_primeSum (hF n hn) (hrough n hn)
  rw [hsum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem sum_richertTerm_le_upper {y Y : ℕ} (hY : 1 < Y) :
    (∑ p ∈ sievePrimes y Y, richertTerm Y p) ≤ (Y : ℝ) := by
  calc
    (∑ p ∈ sievePrimes y Y, richertTerm Y p) ≤
        ∑ _p ∈ sievePrimes y Y, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ ↦ richertTerm_le_one hY
    _ = ((sievePrimes y Y).card : ℝ) := by simp
    _ ≤ Y := by
      exact_mod_cast (Finset.card_filter_le (Finset.Ioc y Y) Nat.Prime).trans
        (by simp : (Finset.Ioc y Y).card ≤ Y)

/-- The large-prime count estimate controls the full distinct-prime weight
sum.  The finite endpoint error is at most `16 * Y * E`. -/
theorem sum_distinctRichertWeight_le_of_prime_counts
    (S : Finset ℕ) (F : ℕ → ℕ) {X y Y : ℕ} {U E : ℝ}
    (hY : 1 < Y) (hE : 0 ≤ E)
    (hF : ∀ n ∈ S, F n ≠ 0)
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ F n)
    (hcount : ∀ p ∈ sievePrimes y Y,
      ((S.filter fun n ↦ p ∣ F n).card : ℝ) ≤
        16 * (((X : ℝ) / p) * U + E)) :
    (∑ n ∈ S, distinctRichertWeight (F n) Y) ≤
      16 * (X : ℝ) * U * primeRichertMass y Y + 16 * Y * E := by
  rw [sum_distinctRichertWeight_eq_prime_counts S F hF hrough]
  have hmajor := Finset.sum_le_sum (s := sievePrimes y Y) fun p hp ↦
    mul_le_mul_of_nonneg_left (hcount p hp)
      (richertTerm_nonneg hY (mem_sievePrimes.mp hp).2.2.pos)
  have hexpand :
      (∑ p ∈ sievePrimes y Y, richertTerm Y p *
        (16 * (((X : ℝ) / p) * U + E))) =
      16 * (X : ℝ) * U * primeRichertMass y Y +
        16 * E * ∑ p ∈ sievePrimes y Y, richertTerm Y p := by
    unfold primeRichertMass
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [richertTerm_eq_of_le hY (mem_sievePrimes.mp hp).2.1]
    ring
  rw [hexpand] at hmajor
  have herr := mul_le_mul_of_nonneg_left (sum_richertTerm_le_upper (y := y) hY)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hE)
  nlinarith

theorem affine_weight_sum_bound {a b : Fin 16 → ℕ} {X z y Y : ℕ}
    (hz : 272 ≤ z) (hzy : z ≤ y) (hY : 1 < Y)
    (hlocal : ∀ p : ℕ, p.Prime → z < p → localNu a b p = 16)
    (hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ∀ i, (a i).Coprime p)
    (hF : ∀ n ∈ siftedCandidates a b X z (y + 1), affineProduct a b n ≠ 0)
    (hrough : ∀ n ∈ siftedCandidates a b X z (y + 1),
      ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ affineProduct a b n) :
    (∑ n ∈ siftedCandidates a b X z (y + 1),
      distinctRichertWeight (affineProduct a b n) Y) ≤
      16 * (X : ℝ) * ((1 + sieveError) * sieveV z y) * primeRichertMass y Y +
        16 * Y * ((y ^ 500 : ℕ) : ℝ) ^ 2 := by
  apply sum_distinctRichertWeight_le_of_prime_counts _ _ hY (sq_nonneg _) hF hrough
  intro p hp
  have hp' := mem_sievePrimes.mp hp
  exact affine_conditioned_cardinality_bound hz hzy hp'.2.2 hp'.1
    (hlocal p hp'.2.2 (hzy.trans_lt hp'.1))
    (fun q hq hzq _ ↦ hlocal q hq hzq) hcop

end

end Erdos946.WeightedAverage

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.B1SquarefreeMass
import ErdosProblems.Erdos822.RoughDivisorEuler

/-! # Divisor-weight bounds on the actual iterated-logarithm family -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem gilCofactors_roughDivisor_squarefree {N S m h : ℕ} {C : ℝ}
    (hm : m ∈ gilCofactors N S C) (hh : h ∣ shiftedTotient m) :
    Squarefree (roughPart h (b1Cutoff N)) := by
  apply squarefree_of_dvd_shiftedTotient_of_largeSquarefree
    (N := N) (y := b1Cutoff N) (m := m)
  · exact mem_largeSquarefreeShiftedOddCofactors_iff.mpr
      ⟨gilCofactors_subset_oddRaw N S C hm, gilCofactors_largeSquarefree hm⟩
  · exact (roughPart_dvd h (b1Cutoff N)).trans hh
  · exact fun p hp hpdvd ↦ prime_dvd_roughPart_gt hp hpdvd

theorem sum_inv_roughPart_primeFactors_le_full {n h y : ℕ}
    (hn : n ≠ 0) (hh : h ∣ n) :
    (∑ p ∈ (roughPart h y).primeFactors, (1 : ℝ) / p) ≤ primeDivisorReciprocalMass n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.primeFactors_mono ((roughPart_dvd h y).trans hh) hn) (fun p hp hnot ↦ by positivity)

theorem eventually_gilCofactors_rough_divisor_euler_bound
    {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ gilCofactors N S C, ∀ h : ℕ,
      h ∣ shiftedTotient m →
      (∑ d ∈ (roughPart h (b1Cutoff N)).divisors,
        (4 : ℝ) ^ d.primeFactors.card / d) ≤ Real.exp (4 * (C + 2)) := by
  filter_upwards [eventually_gilCofactors_full_primeMass_le hS C] with N hmass
  intro m hm h hh
  have hmpos := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm)
  have hsne : shiftedTotient m ≠ 0 := by dsimp [shiftedTotient]; omega
  have hprimes := (sum_inv_roughPart_primeFactors_le_full (y := b1Cutoff N) hsne hh).trans (hmass m hm)
  exact (sum_divisors_four_pow_primeFactorsCard_div_le_exp
    (gilCofactors_roughDivisor_squarefree hm hh)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprimes (by norm_num)))

theorem pow_primeFactors_card_le_of_prime_lower_bound
    {R N b : ℕ} (hR : 0 < R) (hN : 2 ≤ N)
    (hRle : R ≤ 2 * N ^ 28)
    (hrough : ∀ p ∈ R.primeFactors, b ^ 30 ≤ p) :
    b ^ R.primeFactors.card ≤ N := by
  have hprod : (b ^ 30) ^ R.primeFactors.card ≤ R :=
    (Finset.pow_card_le_prod R.primeFactors id (b ^ 30) hrough).trans
      (Nat.le_of_dvd hR R.prod_primeFactors_dvd)
  have hN2 : 2 ≤ N ^ 2 := by nlinarith only [hN]
  have hupper : 2 * N ^ 28 ≤ N ^ 30 := by
    calc
      _ ≤ N ^ 2 * N ^ 28 := Nat.mul_le_mul_right _ hN2
      _ = N ^ 30 := by ring
  have hpowers : (b ^ R.primeFactors.card) ^ 30 ≤ N ^ 30 := by
    have h := hprod.trans (hRle.trans hupper)
    simpa only [← pow_mul, Nat.mul_comm] using h
  by_contra hnot
  have hlt : N < b ^ R.primeFactors.card := by omega
  exact (not_lt_of_ge hpowers) (Nat.pow_lt_pow_left hlt (by norm_num))

theorem eventually_five_pow_roughPart_primeFactors_card_le_nat :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, 0 < h → h ≤ 2 * N ^ 28 →
      5 ^ (roughPart h (b1Cutoff N)).primeFactors.card ≤ N := by
  filter_upwards [tendsto_b1Cutoff_atTop.eventually_ge_atTop (5 ^ 30), eventually_ge_atTop 2]
    with N hy hN
  intro h hh hhN
  apply pow_primeFactors_card_le_of_prime_lower_bound
    (Nat.pos_of_ne_zero (roughPart_ne_zero h (b1Cutoff N))) hN
    ((Nat.le_of_dvd hh (roughPart_dvd h (b1Cutoff N))).trans hhN)
  intro p hp
  exact hy.trans (mem_primeFactors_roughPart_iff.mp hp).2.le

#print axioms eventually_gilCofactors_rough_divisor_euler_bound
#print axioms eventually_five_pow_roughPart_primeFactors_card_le_nat

end Erdos822

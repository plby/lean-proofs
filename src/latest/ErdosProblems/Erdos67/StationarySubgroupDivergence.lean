import ErdosProblems.Erdos67.StationarySubgroupCount

/-!
# Divergence of primes outside a proper unit subgroup

This proof uses only prime factorization, finite CRT counting, a finite Euler
product lower bound, and the small-tail property of a convergent series.
-/

open scoped BigOperators Topology
open Finset Filter

namespace Erdos67.StationaryModel

noncomputable def badPrimeReciprocal (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (p : ℕ) : ℝ := by
  classical
  exact if BadResiduePrime q H p then 1 / p else 0

theorem badPrimeReciprocal_nonneg (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (p : ℕ) :
    0 ≤ badPrimeReciprocal q H p := by
  unfold badPrimeReciprocal
  split_ifs <;> positivity

theorem not_summable_badPrimeReciprocal (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ)
    (a : (ZMod q.val)ˣ) (ha : a ∉ H) : ¬ Summable (badPrimeReciprocal q H) := by
  classical
  intro hsum
  let B : ℝ := ∑' n, badPrimeReciprocal q H n
  let c : ℝ := Real.exp (-2 * B) / (2 * (q.val : ℝ))
  have hc : 0 < c := div_pos (Real.exp_pos _) (by positivity)
  obtain ⟨K, hK⟩ := hsum.nat_tsum_vanishing (Iio_mem_nhds hc)
  let S : Finset ℕ := (range K).filter (BadResiduePrime q H)
  have hS (p : ℕ) (hp : p ∈ S) : BadResiduePrime q H p := (mem_filter.mp hp).2
  have hPpos : 0 < ∏ p ∈ S, p := prod_pos fun p hp ↦ (hS p hp).1.pos
  let P : ℕ+ := ⟨∏ p ∈ S, p, hPpos⟩
  have hqP : Nat.Coprime q.val P.val := by
    change Nat.Coprime q.val (∏ p ∈ S, p)
    apply Nat.coprime_prod_right_iff.mpr
    exact fun p hp ↦ (hS p hp).2.1.symm
  have hSP (p : ℕ) (hp : p ∈ S) : p ∣ P.val := dvd_prod_of_mem (fun p ↦ p) hp
  have hPF (p : ℕ) (hp : p ∈ P.val.primeFactors) : BadResiduePrime q H p := by
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    change p ∣ ∏ r ∈ S, r at hpd
    obtain ⟨r, hr, hpr⟩ := (hpp.prime.dvd_finsetProd_iff (fun p : ℕ ↦ p)).mp hpd
    have he : p = r := (Nat.prime_dvd_prime_iff_eq hpp (hS r hr).1).mp hpr
    exact he ▸ hS r hr
  have hbound : (∑ p ∈ P.val.primeFactors, (1 / p : ℝ)) ≤ B := by
    calc
      _ = ∑ p ∈ P.val.primeFactors, badPrimeReciprocal q H p := by
        apply sum_congr rfl
        intro p hp
        simp only [badPrimeReciprocal, if_pos (hPF p hp)]
      _ ≤ B := hsum.sum_le_tsum _ (fun p _ ↦ badPrimeReciprocal_nonneg q H p)
  have hlower : Real.exp (-2 * B) ≤ (P.val.totient : ℝ) / P.val := by
    rw [totient_ratio_eq_euler_product P.val P.pos]
    exact euler_product_lower_of_sum_le P.val.primeFactors
      (fun p hp ↦ (hPF p hp).1) B hbound
  let T : ℕ := 2 * (q.val * P.val)
  let tail := badPrimeTail q H S T
  have htailSubset : (↑tail : Set ℕ) ⊆ {n | K ≤ n} := by
    intro p hp
    obtain ⟨_, hbad, hnot⟩ := (mem_badPrimeTail q H S T p).mp hp
    have hnotlt : ¬ p < K := by
      intro hlt
      exact hnot (mem_filter.mpr ⟨mem_range.mpr hlt, hbad⟩)
    exact Nat.le_of_not_gt hnotlt
  have htail : (∑ p ∈ tail, (1 / p : ℝ)) < c := by
    have ht := hK (↑tail : Set ℕ) htailSubset
    rw [Set.mem_Iio, tsum_fintype] at ht
    have he : (∑ p ∈ tail, (1 / p : ℝ)) = ∑ p : (↑tail : Set ℕ), badPrimeReciprocal q H p.val := by
      calc
        _ = ∑ p ∈ tail, badPrimeReciprocal q H p := by
          apply sum_congr rfl
          intro p hp
          simp only [badPrimeReciprocal, if_pos ((mem_badPrimeTail q H S T p).mp hp).2.1]
        _ = _ := (Finset.sum_coe_sort tail (badPrimeReciprocal q H)).symm
    rw [he]
    exact ht
  have hcount := totient_le_bad_prime_tail q P hqP H a ha S hSP
  change (P.val.totient : ℝ) ≤ (T : ℝ) * ∑ p ∈ tail, (1 / p : ℝ) at hcount
  have hP : (0 : ℝ) < P.val := Nat.cast_pos.mpr P.pos
  have hlow := (le_div_iff₀ hP).mp hlower
  have hsmall := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q.val)).mp htail
  have hsmallP := mul_lt_mul_of_pos_right hsmall hP
  dsimp [T] at hcount
  push_cast at hcount
  nlinarith

end Erdos67.StationaryModel

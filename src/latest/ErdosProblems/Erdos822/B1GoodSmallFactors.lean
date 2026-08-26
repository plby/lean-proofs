/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1GapModulus
import ErdosProblems.Erdos822.PeriodicCoprimeMass
import ErdosProblems.Erdos822.B1Harmonic
import ErdosProblems.Erdos822.OddCofactorLayers

/-! # Positive harmonic mass with B1 and the intermediate-prime exclusion -/

namespace Erdos822

open Filter
open scoped BigOperators Classical

def gapSmallFactors (N : ℕ) : Finset ℕ :=
  (Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N)).biUnion
    (fun j ↦ coprimeInterval (b1GapModulus N) (2 ^ j) (2 ^ (j + 1)))

noncomputable def b1GoodSmallFactors (N : ℕ) : Finset ℕ := by
  classical
  exact (gapSmallFactors N).filter fun k ↦ TotientSquareRich k (b1Cutoff N)

theorem eventually_four_mul_doubleLog_sq_le_log :
    ∀ᶠ N : ℕ in atTop, 4 * b1DoubleLog N ^ 2 ≤ Nat.log 2 N := by
  have hsmall := tendsto_natLog_two_atTop.eventually
    (eventually_const_mul_log_pow_div_natCast_le_one 36 2)
  filter_upwards [hsmall, tendsto_natLog_two_atTop.eventually_ge_atTop 4] with N hN hK4
  let K := Nat.log 2 N
  let Z := b1DoubleLog N
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsmall' : 36 * Real.log (K : ℝ) ^ 2 ≤ K := by
    have hN' : 36 * Real.log (K : ℝ) ^ 2 / (K : ℝ) ≤ 1 := hN
    have hmul := (div_le_iff₀ hKpos).mp hN'
    linarith
  have hscale := Erdos387.binaryLogScale_cast_le_three_mul_log hK4
  have hZ : (Z : ℝ) ≤ 3 * Real.log (K : ℝ) := by
    simp only [Erdos387.binaryLogScale, Nat.cast_add, Nat.cast_one] at hscale
    change (Z : ℝ) + 1 ≤ 3 * Real.log (K : ℝ) at hscale
    linarith
  have hlog : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
  have hsq : (Z : ℝ) ^ 2 ≤ (3 * Real.log (K : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hZ
  have hfinal : 4 * (Z : ℝ) ^ 2 ≤ K := by nlinarith
  exact_mod_cast hfinal

theorem eventually_b1GapModulus_le_quarterPow :
    ∀ᶠ N : ℕ in atTop, b1GapModulus N ≤ 2 ^ (Nat.log 2 N / 4) := by
  filter_upwards [eventually_four_mul_doubleLog_sq_le_log,
      tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2] with N hN hZ
  calc
    b1GapModulus N ≤ 2 ^ (b1DoubleLog N ^ 2) := gapModulus_le_two_pow_sq hZ
    _ ≤ 2 ^ (Nat.log 2 N / 4) := by
      apply Nat.pow_le_pow_right (by norm_num)
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

theorem eventually_b1GapModulus_small_in_blocks {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
      4 * (b1GapModulus N : ℝ) ≤ δ * (2 : ℝ) ^ j := by
  let M := ⌈4 / δ⌉₊
  filter_upwards [eventually_b1GapModulus_le_quarterPow,
      tendsto_natLog_two_atTop.eventually_ge_atTop (4 * M)] with N hQ hK
  intro j hj
  let a := Nat.log 2 N / 4
  have hMa : M ≤ a := by dsimp [a]; omega
  have hMpow : M ≤ 2 ^ a := hMa.trans Nat.lt_two_pow_self.le
  have hreal : 4 / δ ≤ (2 : ℝ) ^ a := by
    exact (Nat.le_ceil (4 / δ)).trans (by exact_mod_cast hMpow)
  have hδA : 4 ≤ δ * (2 : ℝ) ^ a := by
    have h := (div_le_iff₀ hδ).mp hreal
    nlinarith
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ j := by
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have hjlo := (Finset.mem_Ico.mp hj).1
    dsimp [a]
    omega
  have hQR : (b1GapModulus N : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast hQ
  calc
    4 * (b1GapModulus N : ℝ) ≤ 4 * (2 : ℝ) ^ a := by gcongr
    _ ≤ δ * ((2 : ℝ) ^ a * (2 : ℝ) ^ a) := by
      have h := mul_le_mul_of_nonneg_right hδA (show (0 : ℝ) ≤ (2 : ℝ) ^ a by positivity)
      nlinarith
    _ ≤ δ * (2 : ℝ) ^ j := mul_le_mul_of_nonneg_left hpow hδ.le

theorem coprimeInterval_dyadic_disjoint {Q i j : ℕ} (hij : i ≠ j) :
    Disjoint (coprimeInterval Q (2 ^ i) (2 ^ (i + 1)))
      (coprimeInterval Q (2 ^ j) (2 ^ (j + 1))) := by
  have hlt {a b : ℕ} (hab : a < b) :
      Disjoint (coprimeInterval Q (2 ^ a) (2 ^ (a + 1)))
        (coprimeInterval Q (2 ^ b) (2 ^ (b + 1))) := by
    rw [Finset.disjoint_left]
    intro n hna hnb
    have ha := Finset.mem_Ioc.mp (Finset.mem_filter.mp hna).1
    have hb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hnb).1
    have hpow : 2 ^ (a + 1) ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hlt hij
  · exact (hlt hij).symm

theorem sum_inv_gapSmallFactors_eq (N : ℕ) :
    (∑ k ∈ gapSmallFactors N, (1 : ℝ) / k) =
      ∑ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
        ∑ k ∈ coprimeInterval (b1GapModulus N) (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / k := by
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact coprimeInterval_dyadic_disjoint hij

/-- The intermediate-prime exclusion leaves a positive amount of harmonic
small-factor mass, uniformly as the ambient scale grows. -/
theorem exists_eventually_sum_inv_gapSmallFactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ k ∈ gapSmallFactors N, (1 : ℝ) / k := by
  obtain ⟨δ, hδ, hden⟩ := exists_b1GapModulus_totient_ratio_lower
  refine ⟨δ / 16, by positivity, ?_⟩
  filter_upwards [eventually_b1GapModulus_small_in_blocks hδ,
      tendsto_b1Cutoff_atTop.eventually_ge_atTop 2,
      tendsto_natLog_two_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop 1] with N hQ hy hK1 hN1
  let K := Nat.log 2 N
  have hlog : Real.log (N : ℝ) ≤ 2 * (K : ℝ) := by
    have h := Erdos387.real_log_nat_le_log_two_add_one N hN1
    have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    norm_num only [Nat.cast_add, Nat.cast_one] at h
    linarith
  have hhalf : (K : ℝ) / 2 ≤ (Finset.Ico (K / 2) K).card := by
    have hcardNat : K ≤ 2 * (Finset.Ico (K / 2) K).card := by
      simp only [Nat.card_Ico]
      omega
    have hcardR : (K : ℝ) ≤ 2 * ((Finset.Ico (K / 2) K).card : ℝ) := by exact_mod_cast hcardNat
    linarith
  rw [sum_inv_gapSmallFactors_eq]
  calc
    δ / 16 * Real.log (N : ℝ) ≤ δ / 16 * (2 * (K : ℝ)) := by gcongr
    _ = δ / 4 * ((K : ℝ) / 2) := by ring
    _ ≤ δ / 4 * ((Finset.Ico (K / 2) K).card : ℝ) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = ∑ _j ∈ Finset.Ico (K / 2) K, δ / 4 := by simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.Ico (K / 2) K,
        ∑ k ∈ coprimeInterval (b1GapModulus N) (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / k := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_inv_coprimeInterval_dyadic_lower
        (gapModulus_pos _ _) hδ.le (hden N hy) (hQ j hj)

theorem gapSmallFactors_odd_and_no_intermediate_prime
    {N k : ℕ} (hk : k ∈ gapSmallFactors N) :
    Odd k ∧ ∀ p : ℕ, p.Prime → b1Cutoff N < p → p ≤ b1DoubleLog N → ¬ p ∣ k := by
  obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
  have hcop := (Finset.mem_filter.mp hkj).2
  exact (gapModulus_coprime_iff _ _ _).mp hcop

theorem gapSmallFactors_subset_oddSmallFactors (N : ℕ) :
    gapSmallFactors N ⊆ oddSmallFactors N := by
  intro k hk
  have hodd := (gapSmallFactors_odd_and_no_intermediate_prime hk).1
  obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
  have hjhi := (Finset.mem_Ico.mp hj).2
  have hkhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hkj).1).2
  have hKpos : 0 < Nat.log 2 N := by omega
  have hNne : N ≠ 0 := by
    intro hN
    simp [hN] at hKpos
  have hkpow : k ≤ 2 ^ Nat.log 2 N := hkhi.trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hkneq : k ≠ 2 ^ Nat.log 2 N := by
    intro heq
    have hnot := Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hodd)
    apply hnot
    rw [heq]
    exact dvd_pow_self 2 hKpos.ne'
  have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hNne
  have hkN : k + 1 ≤ N := by omega
  obtain ⟨a, ha⟩ := hodd
  apply mem_oddSmallFactors_iff.mpr
  refine ⟨a + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  omega

theorem b1GoodSmallFactors_subset_oddSmallFactors (N : ℕ) :
    b1GoodSmallFactors N ⊆ oddSmallFactors N := by
  classical
  exact (Finset.filter_subset _ _).trans (gapSmallFactors_subset_oddSmallFactors N)

theorem b1GoodSmallFactors_squareRich {N k : ℕ} (hk : k ∈ b1GoodSmallFactors N) :
    TotientSquareRich k (b1Cutoff N) := by
  classical
  exact (Finset.mem_filter.mp hk).2

theorem gapSmallFactors_not_squareRich_subset (N : ℕ) :
    (gapSmallFactors N).filter (fun k ↦ ¬ TotientSquareRich k (b1Cutoff N)) ⊆
      b1UpperHalfFailures N := by
  classical
  intro k hk
  obtain ⟨hkgap, hkfail⟩ := Finset.mem_filter.mp hk
  obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hkgap
  exact Finset.mem_biUnion.mpr
    ⟨j, hj, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hkj).1, hkfail⟩⟩

/-- B1 and avoidance of the intermediate prime interval coexist on a
positive harmonic-mass family of odd small factors. -/
theorem exists_eventually_sum_inv_b1GoodSmallFactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k := by
  classical
  obtain ⟨c, hc, hmass⟩ := exists_eventually_sum_inv_gapSmallFactors_lower
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmass,
      eventually_sum_inv_b1UpperHalfFailures_le_log (ε := c / 2) (by positivity)]
    with N hN hbad
  have hsplit :
      (∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k) +
        (∑ k ∈ (gapSmallFactors N).filter
          (fun k ↦ ¬ TotientSquareRich k (b1Cutoff N)), (1 : ℝ) / k) =
        ∑ k ∈ gapSmallFactors N, (1 : ℝ) / k := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hbadmass :
      (∑ k ∈ (gapSmallFactors N).filter
        (fun k ↦ ¬ TotientSquareRich k (b1Cutoff N)), (1 : ℝ) / k) ≤
        ∑ k ∈ b1UpperHalfFailures N, (1 : ℝ) / k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (gapSmallFactors_not_squareRich_subset N) (fun k hk hnot ↦ by positivity)
  linarith

#print axioms exists_eventually_sum_inv_b1GoodSmallFactors_lower

end Erdos822

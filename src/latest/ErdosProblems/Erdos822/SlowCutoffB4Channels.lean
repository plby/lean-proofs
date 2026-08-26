/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.StructuredTotientCommonPrime
import ErdosProblems.Erdos822.LargeGcdFreeBasic
import ErdosProblems.Erdos822.LargeCutoffB4

/-!
# Four channels for a slow-cutoff B4 failure

Unlike the earlier `N^4` cutoff, a slowly growing cutoff allows the common
prime to divide the small factor `k`.  The exact four-channel representation
below is the starting point for the requisite reciprocal-mass union bound.
-/

namespace Erdos822

/-- Odd structured cofactors having a prime above `y` in common with their
totient. -/
noncomputable def slowCutoffBadOddCofactors (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ m ∧ p ∣ Nat.totient m

@[simp]
theorem mem_slowCutoffBadOddCofactors_iff
    {N y m : ℕ} :
    m ∈ slowCutoffBadOddCofactors N y ↔
      m ∈ oddRawCofactors N ∧
        ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ m ∧ p ∣ Nat.totient m := by
  simp [slowCutoffBadOddCofactors]

theorem mem_largeGcdFreeOddCofactors_iff_not_mem_slowBad
    {N y m : ℕ} (hm : m ∈ oddRawCofactors N) :
    m ∈ largeGcdFreeOddCofactors N y ↔
      m ∉ slowCutoffBadOddCofactors N y := by
  rw [mem_largeGcdFreeOddCofactors_iff,
    mem_slowCutoffBadOddCofactors_iff]
  simp only [hm, true_and, not_exists, not_and]

/-- Every slow-cutoff B4 failure has a unique structured representation
and belongs to one of the four explicit divisibility channels. -/
theorem exists_four_channels_of_mem_slowCutoffBad
    {N y m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ slowCutoffBadOddCofactors N y) :
    ∃ k r q p : ℕ,
      (k, r, q) ∈ oddCofactorTriples N ∧
      m = k * r * q ∧ p.Prime ∧ y < p ∧
      ((p ∣ k ∧ p ∣ Nat.totient k) ∨
       (p ∣ k ∧ p ∣ r - 1) ∨
       (p ∣ k ∧ p ∣ q - 1) ∨
       (p = r ∧ r ∣ q - 1)) := by
  have hmData := mem_slowCutoffBadOddCofactors_iff.mp hm
  obtain ⟨p, hp, hyp, hpm, hpφ⟩ := hmData.2
  rw [oddRawCofactors] at hmData
  simp only [Finset.mem_image] at hmData
  obtain ⟨⟨k, r, q⟩, ht, hprod⟩ := hmData.1
  rw [mem_oddCofactorTriples_iff] at ht
  have hsep := oddCofactorTriples_separated hN (by
    rw [mem_oddCofactorTriples_iff]
    exact ht)
  have hrPrime := (mem_middlePrimes_iff.mp ht.2.1).2.2
  have hqPrime := (mem_largePrimes_iff.mp ht.2.2).2.2
  have hrk : ¬ r ∣ k := by
    intro hdiv
    have hle := Nat.le_of_dvd (oddSmallFactors_pos ht.1) hdiv
    omega
  have hqkr : ¬ q ∣ k * r := by
    intro hdiv
    have hle := Nat.le_of_dvd
      (Nat.mul_pos (oddSmallFactors_pos ht.1) hrPrime.pos) hdiv
    omega
  have hrlekr : r ≤ k * r := by
    have hmul := Nat.mul_le_mul_right r
      (show 1 ≤ k from (oddSmallFactors_pos ht.1))
    simpa using hmul
  have hrq : r < q := hrlekr.trans_lt hsep.2.2
  have hprod' : k * r * q = m := by
    simpa [cofactorProduct] using hprod
  have hpm' : p ∣ k * r * q := by
    rw [hprod']
    exact hpm
  have hpφ' : p ∣ Nat.totient (k * r * q) := by
    rw [hprod']
    exact hpφ
  refine ⟨k, r, q, p, ?_, hprod'.symm, hp, hyp, ?_⟩
  · rw [mem_oddCofactorTriples_iff]
    exact ht
  · exact prime_dvd_structured_product_and_totient_four_cases
      hp hrPrime hqPrime hrk hqkr (oddSmallFactors_pos ht.1)
      hsep.2.1 hrq hpm' hpφ'

/-- Channel 1: a prime above the cutoff divides both `k` and `φ(k)`. -/
noncomputable def slowInternalTotientCofactors (N y : ℕ) : Finset ℕ := by
  classical
  exact ((oddCofactorTriples N).filter fun (t : ℕ × ℕ × ℕ) =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧ p ∣ Nat.totient t.1).image
      cofactorProduct

/-- Channel 2: a prime above the cutoff divides `k` and `r-1`. -/
noncomputable def slowSmallMiddlePredCofactors (N y : ℕ) : Finset ℕ := by
  classical
  exact ((oddCofactorTriples N).filter fun (t : ℕ × ℕ × ℕ) =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧ p ∣ t.2.1 - 1).image
      cofactorProduct

/-- Channel 3: a prime above the cutoff divides `k` and `q-1`. -/
noncomputable def slowSmallLargePredCofactors (N y : ℕ) : Finset ℕ := by
  classical
  exact ((oddCofactorTriples N).filter fun (t : ℕ × ℕ × ℕ) =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧ p ∣ t.2.2 - 1).image
      cofactorProduct

@[simp]
theorem mem_slowInternalTotientCofactors_iff {N y m : ℕ} :
    m ∈ slowInternalTotientCofactors N y ↔
      ∃ k r q p : ℕ, (k, r, q) ∈ oddCofactorTriples N ∧
        p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ Nat.totient k ∧
        m = k * r * q := by
  classical
  constructor
  · intro hm
    rw [slowInternalTotientCofactors, Finset.mem_image] at hm
    obtain ⟨⟨k, r, q⟩, ht, hprod⟩ := hm
    obtain ⟨htriple, p, hp, hyp, hpk, hpφ⟩ := Finset.mem_filter.mp ht
    exact ⟨k, r, q, p, htriple, hp, hyp, hpk, hpφ,
      by simpa [cofactorProduct] using hprod.symm⟩
  · rintro ⟨k, r, q, p, ht, hp, hyp, hpk, hpφ, rfl⟩
    rw [slowInternalTotientCofactors, Finset.mem_image]
    exact ⟨(k, r, q), Finset.mem_filter.mpr
      ⟨ht, ⟨p, hp, hyp, hpk, hpφ⟩⟩, by simp [cofactorProduct]⟩

@[simp]
theorem mem_slowSmallMiddlePredCofactors_iff {N y m : ℕ} :
    m ∈ slowSmallMiddlePredCofactors N y ↔
      ∃ k r q p : ℕ, (k, r, q) ∈ oddCofactorTriples N ∧
        p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ r - 1 ∧
        m = k * r * q := by
  classical
  constructor
  · intro hm
    rw [slowSmallMiddlePredCofactors, Finset.mem_image] at hm
    obtain ⟨⟨k, r, q⟩, ht, hprod⟩ := hm
    obtain ⟨htriple, p, hp, hyp, hpk, hpR⟩ := Finset.mem_filter.mp ht
    exact ⟨k, r, q, p, htriple, hp, hyp, hpk, hpR,
      by simpa [cofactorProduct] using hprod.symm⟩
  · rintro ⟨k, r, q, p, ht, hp, hyp, hpk, hpR, rfl⟩
    rw [slowSmallMiddlePredCofactors, Finset.mem_image]
    exact ⟨(k, r, q), Finset.mem_filter.mpr
      ⟨ht, ⟨p, hp, hyp, hpk, hpR⟩⟩, by simp [cofactorProduct]⟩

@[simp]
theorem mem_slowSmallLargePredCofactors_iff {N y m : ℕ} :
    m ∈ slowSmallLargePredCofactors N y ↔
      ∃ k r q p : ℕ, (k, r, q) ∈ oddCofactorTriples N ∧
        p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1 ∧
        m = k * r * q := by
  classical
  constructor
  · intro hm
    rw [slowSmallLargePredCofactors, Finset.mem_image] at hm
    obtain ⟨⟨k, r, q⟩, ht, hprod⟩ := hm
    obtain ⟨htriple, p, hp, hyp, hpk, hpQ⟩ := Finset.mem_filter.mp ht
    exact ⟨k, r, q, p, htriple, hp, hyp, hpk, hpQ,
      by simpa [cofactorProduct] using hprod.symm⟩
  · rintro ⟨k, r, q, p, ht, hp, hyp, hpk, hpQ, rfl⟩
    rw [slowSmallLargePredCofactors, Finset.mem_image]
    exact ⟨(k, r, q), Finset.mem_filter.mpr
      ⟨ht, ⟨p, hp, hyp, hpk, hpQ⟩⟩, by simp [cofactorProduct]⟩

/-- The bad slow-cutoff family is covered by the four explicit channel
families.  The fourth is the already-developed `r ∣ q-1` family. -/
theorem slowCutoffBadOddCofactors_subset_four_channels
    {N y : ℕ} (hN : 2 ≤ N) :
    slowCutoffBadOddCofactors N y ⊆
      slowInternalTotientCofactors N y ∪
        (slowSmallMiddlePredCofactors N y ∪
          (slowSmallLargePredCofactors N y ∪ middlePredLargeCofactors N)) := by
  intro m hm
  obtain ⟨k, r, q, p, ht, hprod, hp, hyp, hcase⟩ :=
    exists_four_channels_of_mem_slowCutoffBad hN hm
  rcases hcase with h | h | h | h
  · apply Finset.mem_union_left
    rw [mem_slowInternalTotientCofactors_iff]
    exact ⟨k, r, q, p, ht, hp, hyp, h.1, h.2, hprod⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    rw [mem_slowSmallMiddlePredCofactors_iff]
    exact ⟨k, r, q, p, ht, hp, hyp, h.1, h.2, hprod⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    rw [mem_slowSmallLargePredCofactors_iff]
    exact ⟨k, r, q, p, ht, hp, hyp, h.1, h.2, hprod⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    rw [mem_middlePredLargeCofactors_iff]
    exact ⟨k, r, q, ht, by simpa [h.1] using h.2, hprod⟩

end Erdos822

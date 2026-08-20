/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperComplementaryLargestPrime
import ErdosProblems.Erdos446.UpperRoughGlobalInterval
import ErdosProblems.Erdos446.UpperPrimeClusterTargetScale

/-!
# Erdős Problem 446: the endpoint-free complementary rough shell

This is the finite counting core of Ford's Lemma 3.2.  A nontrivial
squarefree divisor event is marked by the factor having smaller largest
prime.  The complementary selection makes the residual factor strictly
larger than the pivot, and hence the uniform rough-interval estimate has no
Brun endpoint term.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- The part of a squarefree divisor shell for which a divisor witness has
a nontrivial complementary factor. -/
def squarefreeNontrivialDivisorShell (X₀ X₁ y z : ℕ) : Finset ℕ := by
  classical
  exact (squarefreeDivisorShell X₀ X₁ y z).filter fun n ↦
    ∃ m ∈ Finset.Ioc y z, m ∣ n ∧ 1 < n / m

theorem mem_squarefreeNontrivialDivisorShell {X₀ X₁ y z n : ℕ} :
    n ∈ squarefreeNontrivialDivisorShell X₀ X₁ y z ↔
      n ∈ squarefreeDivisorShell X₀ X₁ y z ∧
        ∃ m ∈ Finset.Ioc y z, m ∣ n ∧ 1 < n / m := by
  classical
  simp [squarefreeNontrivialDivisorShell]

/-- The full squarefree shell is the union of its nontrivial complementary
part and at most `z+1` small endpoint integers. -/
theorem squarefreeDivisorShell_subset_small_union_nontrivial
    {X₀ X₁ y z : ℕ} :
    squarefreeDivisorShell X₀ X₁ y z ⊆
      Finset.range (z + 1) ∪
        squarefreeNontrivialDivisorShell X₀ X₁ y z := by
  classical
  intro n hn
  have hnData := mem_squarefreeDivisorShell.mp hn
  rw [divisorCountIoc, Finset.card_pos] at hnData
  obtain ⟨m, hm⟩ := hnData.2.2.2
  have hmData := Finset.mem_filter.mp hm
  by_cases he : 1 < n / m
  · exact Finset.mem_union_right _
      (mem_squarefreeNontrivialDivisorShell.mpr
        ⟨hn, m, hmData.1, hmData.2, he⟩)
  · apply Finset.mem_union_left
    rw [Finset.mem_range]
    have hnPos : 0 < n := Nat.zero_lt_of_lt hnData.1
    have hePos := complementaryDivisor_pos hnPos hmData.2
    have heOne : n / m = 1 := by omega
    have hnm : n = m := by
      simpa [heOne] using (Nat.div_mul_cancel hmData.2).symm
    rw [hnm]
    exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp hmData.1).2

/-- Literal source data attached to one complementary `(a,p)` shell. -/
def fordComplementaryShellWitness
    (X₀ X₁ y z a p : ℕ) : Prop :=
  ∃ n m s t b : ℕ,
    X₀ < n ∧ n ≤ X₁ ∧ Squarefree n ∧
    y < m ∧ m ≤ z ∧ m ∣ n ∧ 1 < m ∧ 1 < n / m ∧
    s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
    (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
    Erdos469.largestPrimeFactor s < Erdos469.largestPrimeFactor t ∧
    p = Erdos469.largestPrimeFactor s ∧
    a = fordLowerPrimePart n p ∧ b = fordUpperPrimePart n p ∧
    p.Prime ∧ 0 < a ∧ p < b ∧ n = a * p * b ∧
    Erdos387.IsZRough p b ∧ s / p ∈ a.divisors ∧ s = (s / p) * p

/-- The finite family of actual complementary `(a,p)` pairs in a shell. -/
def fordComplementaryShellPairs (X₀ X₁ y z : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc 1 X₁ ×ˢ Nat.primesLE z).filter fun ap ↦
    fordComplementaryShellWitness X₀ X₁ y z ap.1 ap.2

theorem mem_fordComplementaryShellPairs {X₀ X₁ y z a p : ℕ} :
    (a, p) ∈ fordComplementaryShellPairs X₀ X₁ y z ↔
      1 ≤ a ∧ a ≤ X₁ ∧ p ≤ z ∧ p.Prime ∧
        fordComplementaryShellWitness X₀ X₁ y z a p := by
  classical
  simp [fordComplementaryShellPairs, Nat.mem_primesLE, and_assoc]

theorem complementary_pair_mem
    {X₀ X₁ y z n m : ℕ} (hy : 1 ≤ y)
    (hnX₀ : X₀ < n) (hnX₁ : n ≤ X₁) (hn : Squarefree n)
    (hmI : m ∈ Finset.Ioc y z) (hm : m ∣ n) (heOne : 1 < n / m) :
    ∃ a p b : ℕ,
      (a, p) ∈ fordComplementaryShellPairs X₀ X₁ y z ∧
      p < b ∧ n = a * p * b ∧ Erdos387.IsZRough p b := by
  have hmOne : 1 < m := hy.trans_lt (Finset.mem_Ioc.mp hmI).1
  obtain ⟨s, t, p, a, b, hs, ht, hsOne, htOne, hst, hlt,
      hp, ha, hb, hpPrime, haPos, hpb, hnprod, hrough, hsdiv, hseq⟩ :=
    squarefree_complementary_largestPrime_shell hn hm hmOne heOne
  have hpLeZ : p ≤ z := by
    have hmSpec := Erdos469.largestPrimeFactor_spec hmOne
    rcases hst with hleft | hright
    · rw [hp, hleft.1]
      exact (Nat.le_of_dvd (by omega) hmSpec.dvd).trans
        (Finset.mem_Ioc.mp hmI).2
    · have hpt : p < Erdos469.largestPrimeFactor m := by
        simpa [hright.2, hp] using hlt
      exact hpt.le.trans
        ((Nat.le_of_dvd (by omega) hmSpec.dvd).trans
          (Finset.mem_Ioc.mp hmI).2)
  have haDvd : a ∣ n := by
    use p * b
    simpa [mul_assoc] using hnprod
  have haLe : a ≤ X₁ :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hnX₀) haDvd).trans hnX₁
  refine ⟨a, p, b, ?_, hpb, hnprod, hrough⟩
  rw [mem_fordComplementaryShellPairs]
  refine ⟨haPos, haLe, hpLeZ, hpPrime, ?_⟩
  exact ⟨n, m, s, t, b, hnX₀, hnX₁, hn,
    (Finset.mem_Ioc.mp hmI).1, (Finset.mem_Ioc.mp hmI).2,
    hm, hmOne, heOne, hs, ht, hsOne, htOne, hst, hlt,
    hp, ha, hb, hpPrime, haPos, hpb, hnprod, hrough, hsdiv, hseq⟩

/-- Products generated by the genuinely nontrivial rough residual. -/
def fordComplementaryRoughValues (X a p : ℕ) : Finset ℕ := by
  classical
  exact (Erdos387.RoughHarmonic.roughPositiveIoc p p (X / (a * p))).image
    fun b ↦ a * p * b

def fordComplementaryRoughUnion
    (X₀ X₁ y z : ℕ) : Finset ℕ :=
  (fordComplementaryShellPairs X₀ X₁ y z).biUnion fun ap ↦
    fordComplementaryRoughValues X₁ ap.1 ap.2

theorem squarefreeNontrivialDivisorShell_subset_complementaryRoughUnion
    {X₀ X₁ y z : ℕ} (hy : 1 ≤ y) :
    squarefreeNontrivialDivisorShell X₀ X₁ y z ⊆
      fordComplementaryRoughUnion X₀ X₁ y z := by
  classical
  intro n hn
  rw [mem_squarefreeNontrivialDivisorShell] at hn
  obtain ⟨m, hmI, hm, heOne⟩ := hn.2
  have hnData := mem_squarefreeDivisorShell.mp hn.1
  obtain ⟨a, p, b, hap, hpb, hnprod, hrough⟩ :=
    complementary_pair_mem hy hnData.1 hnData.2.1 hnData.2.2.1
      hmI hm heOne
  rw [fordComplementaryRoughUnion, Finset.mem_biUnion]
  refine ⟨(a, p), hap, ?_⟩
  rw [fordComplementaryRoughValues, Finset.mem_image]
  refine ⟨b, ?_, hnprod.symm⟩
  rw [Erdos387.RoughHarmonic.mem_roughPositiveIoc]
  have hapPos : 0 < a * p := Nat.mul_pos
    (mem_fordComplementaryShellPairs.mp hap).1
    (mem_fordComplementaryShellPairs.mp hap).2.2.2.1.pos
  refine ⟨hpb, ?_, hrough⟩
  apply (Nat.le_div_iff_mul_le hapPos).2
  calc
    b * (a * p) = n := by rw [hnprod]; ac_rfl
    _ ≤ X₁ := hnData.2.1

theorem card_fordComplementaryRoughValues_le
    {B : ℝ} (hB : 0 < B)
    (hrough : ∀ p A U : ℕ, 2 ≤ p → 1 ≤ A →
      ((Erdos387.RoughHarmonic.roughPositiveIoc p A U).card : ℝ) ≤
        B * (U : ℝ) / Real.log p)
    {X a p : ℕ} (ha : 0 < a) (hp : p.Prime) :
    ((fordComplementaryRoughValues X a p).card : ℝ) ≤
      B * (X : ℝ) /
        ((a : ℝ) * (p : ℝ) * Real.log (p : ℝ)) := by
  have hlogp : 0 < Real.log (p : ℝ) := hp.log_pos
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hapR : 0 < (a : ℝ) * (p : ℝ) := mul_pos haR hpR
  have himage : (fordComplementaryRoughValues X a p).card ≤
      (Erdos387.RoughHarmonic.roughPositiveIoc p p
        (X / (a * p))).card := by
    unfold fordComplementaryRoughValues
    exact Finset.card_image_le
  have hbase := hrough p p (X / (a * p)) hp.two_le hp.one_le
  have hdiv : ((X / (a * p) : ℕ) : ℝ) ≤
      (X : ℝ) / ((a : ℝ) * (p : ℝ)) := by
    simpa [Nat.cast_mul] using
      (Nat.cast_div_le : ((X / (a * p) : ℕ) : ℝ) ≤
        (X : ℝ) / ((a * p : ℕ) : ℝ))
  calc
    ((fordComplementaryRoughValues X a p).card : ℝ) ≤
        ((Erdos387.RoughHarmonic.roughPositiveIoc p p
          (X / (a * p))).card : ℝ) := by exact_mod_cast himage
    _ ≤ B * ((X / (a * p) : ℕ) : ℝ) / Real.log p := hbase
    _ ≤ B * ((X : ℝ) / ((a : ℝ) * (p : ℝ))) /
          Real.log p := by gcongr
    _ = B * (X : ℝ) /
        ((a : ℝ) * (p : ℝ) * Real.log (p : ℝ)) := by
      field_simp [hapR.ne', hlogp.ne']
      <;> ring

/-- Endpoint-free largest-prime/rough-sieve shell reduction. -/
theorem exists_pos_squarefreeDivisorShell_le_complementary_weight :
    ∃ B : ℝ, 0 < B ∧ ∀ X₀ X₁ y z : ℕ, 1 ≤ y →
      ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
        (z + 1 : ℕ) +
          B * (X₁ : ℝ) *
            (∑ ap ∈ fordComplementaryShellPairs X₀ X₁ y z,
              1 / ((ap.1 : ℝ) * (ap.2 : ℝ) *
                Real.log (ap.2 : ℝ))) := by
  obtain ⟨B, hB, hrough⟩ :=
    exists_uniform_roughPositiveIoc_card_le_div_log
  refine ⟨B, hB, fun X₀ X₁ y z hy ↦ ?_⟩
  have hcover := squarefreeDivisorShell_subset_small_union_nontrivial
    (X₀ := X₀) (X₁ := X₁) (y := y) (z := z)
  have hnontriv :=
    squarefreeNontrivialDivisorShell_subset_complementaryRoughUnion
      (X₀ := X₀) (X₁ := X₁) (z := z) hy
  calc
    ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
        (((Finset.range (z + 1) ∪
          squarefreeNontrivialDivisorShell X₀ X₁ y z).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ((z + 1) +
          (squarefreeNontrivialDivisorShell X₀ X₁ y z).card : ℕ) := by
      have hu := Finset.card_union_le (Finset.range (z + 1))
        (squarefreeNontrivialDivisorShell X₀ X₁ y z)
      have hu' :
          (Finset.range (z + 1) ∪
            squarefreeNontrivialDivisorShell X₀ X₁ y z).card ≤
            z + 1 +
              (squarefreeNontrivialDivisorShell X₀ X₁ y z).card := by
        simpa using hu
      exact_mod_cast hu'
    _ ≤ (z + 1 : ℕ) +
          ((fordComplementaryRoughUnion X₀ X₁ y z).card : ℝ) := by
      push_cast
      gcongr
    _ ≤ (z + 1 : ℕ) +
          ∑ ap ∈ fordComplementaryShellPairs X₀ X₁ y z,
            (B * (X₁ : ℝ) /
              ((ap.1 : ℝ) * (ap.2 : ℝ) * Real.log (ap.2 : ℝ))) := by
      gcongr
      calc
        ((fordComplementaryRoughUnion X₀ X₁ y z).card : ℝ) ≤
            ∑ ap ∈ fordComplementaryShellPairs X₀ X₁ y z,
              ((fordComplementaryRoughValues X₁ ap.1 ap.2).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ap hap
          exact card_fordComplementaryRoughValues_le hB hrough
            (mem_fordComplementaryShellPairs.mp hap).1
            (mem_fordComplementaryShellPairs.mp hap).2.2.2.1
    _ = (z + 1 : ℕ) + B * (X₁ : ℝ) *
          (∑ ap ∈ fordComplementaryShellPairs X₀ X₁ y z,
            1 / ((ap.1 : ℝ) * (ap.2 : ℝ) *
              Real.log (ap.2 : ℝ))) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ap hap
      ring

end

end Erdos446

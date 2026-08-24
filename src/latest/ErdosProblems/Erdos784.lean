/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 784.
https://www.erdosproblems.com/forum/thread/784

Informal authors:
- Imre Ruzsa
- Andreas Weingartner

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos784.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos784.Erdos784Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 784

This file formalizes the small-sieve question both as literally printed and
with the intended condition that the sifting set not contain `1`.  The
detailed mathematical proof and the correspondence with the declarations
below are in `tex/784.tex`.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos784

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact finite formulations -/

/-- Reciprocal mass of a finite set of positive integers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

/-- Positive integers at most `N` which are divisible by no member of `A`. -/
def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

/-- Integers in the positive prefix removed by at least one modulus. -/
def covered (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => ∃ a ∈ A, a ∣ n

@[simp] lemma mem_unsieved {N n : ℕ} {A : Finset ℕ} :
    n ∈ unsieved N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∀ a ∈ A, ¬a ∣ n := by
  simp only [unsieved, mem_filter, mem_Icc]
  tauto

@[simp] lemma mem_covered {N n : ℕ} {A : Finset ℕ} :
    n ∈ covered N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∃ a ∈ A, a ∣ n := by
  simp only [covered, mem_filter, mem_Icc]
  tauto

/-- The hypotheses in the problem exactly as printed, allowing `1 ∈ A`. -/
def LiteralAdmissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ reciprocalMass A ≤ C

/-- The intended hypotheses, in which the sifting set is contained in
`{2, ..., N}`. -/
def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Icc 2 N ∧ reciprocalMass A ≤ C

/-- The polynomial-logarithmic lower bound asked for in Problem 784, with
all constants and the phrase "sufficiently large" made explicit. -/
def HasPolylogLowerBound
    (admissible : ℝ → ℕ → Finset ℕ → Prop) (C : ℝ) : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, admissible C N A →
      K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c ≤ (unsieved N A).card

/-- The literal assertion from the displayed question. -/
abbrev LiteralAnswer (C : ℝ) : Prop :=
  HasPolylogLowerBound LiteralAdmissible C

/-- The customary corrected assertion with `1 ∉ A`. -/
abbrev CorrectedAnswer (C : ℝ) : Prop :=
  HasPolylogLowerBound Admissible C

/-! ## The elementary union bound -/

lemma cast_card_unsieved_add_cast_card_covered (N : ℕ) (A : Finset ℕ) :
    ((unsieved N A).card : ℝ) + ((covered N A).card : ℝ) = N := by
  have hDisjoint : Disjoint (unsieved N A) (covered N A) := by
    rw [disjoint_left]
    intro n hnU hnC
    obtain ⟨_, _, a, ha, hadvd⟩ := mem_covered.mp hnC
    exact (mem_unsieved.mp hnU).2.2 a ha hadvd
  have hUnion : unsieved N A ∪ covered N A = Icc 1 N := by
    ext n
    simp only [mem_union, mem_unsieved, mem_covered, mem_Icc]
    constructor
    · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩
    · rintro ⟨hn1, hnN⟩
      by_cases h : ∃ a ∈ A, a ∣ n
      · exact Or.inr ⟨hn1, hnN, h⟩
      · exact Or.inl ⟨hn1, hnN, fun a ha hadvd => h ⟨a, ha, hadvd⟩⟩
  rw [← Nat.cast_add, ← card_union_of_disjoint hDisjoint, hUnion]
  simp [Nat.card_Icc]

/-- Multiples of `a` in the positive prefix. -/
def multiplesIn (N a : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => a ∣ n

lemma covered_subset_biUnion_multiples (N : ℕ) (A : Finset ℕ) :
    covered N A ⊆ A.biUnion (multiplesIn N) := by
  intro n hn
  obtain ⟨hn1, hnN, a, ha, hadvd⟩ := mem_covered.mp hn
  simp only [mem_biUnion]
  refine ⟨a, ha, ?_⟩
  rw [multiplesIn, mem_filter]
  exact ⟨mem_Ioc.mpr ⟨by omega, hnN⟩, hadvd⟩

lemma card_covered_cast_le_mass (N : ℕ) (A : Finset ℕ) :
    ((covered N A).card : ℝ) ≤ (N : ℝ) * reciprocalMass A := by
  have hcard : (covered N A).card ≤ ∑ a ∈ A, N / a := by
    calc
      (covered N A).card ≤ (A.biUnion (multiplesIn N)).card :=
        card_le_card (covered_subset_biUnion_multiples N A)
      _ ≤ ∑ a ∈ A, (multiplesIn N a).card := card_biUnion_le
      _ = ∑ a ∈ A, N / a := by
        apply sum_congr rfl
        intro a _
        simpa only [multiplesIn] using Nat.Ioc_filter_dvd_card_eq_div N a
  calc
    ((covered N A).card : ℝ) ≤ (∑ a ∈ A, N / a : ℕ) := by
      exact_mod_cast hcard
    _ ≤ ∑ a ∈ A, (N : ℝ) / (a : ℝ) := by
      rw [Nat.cast_sum]
      apply sum_le_sum
      intro a _
      exact (Nat.cast_div_le : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ))
    _ = (N : ℝ) * reciprocalMass A := by
      simp only [reciprocalMass, mul_sum]
      apply sum_congr rfl
      intro a _
      rw [div_eq_mul_inv]

lemma cast_card_unsieved_lower_bound {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hMass : reciprocalMass A ≤ C) :
    (1 - C) * (N : ℝ) ≤ ((unsieved N A).card : ℝ) := by
  have hCovered : ((covered N A).card : ℝ) ≤ (N : ℝ) * C :=
    (card_covered_cast_le_mass N A).trans
      (mul_le_mul_of_nonneg_left hMass (Nat.cast_nonneg N))
  have hPartition := cast_card_unsieved_add_cast_card_covered N A
  linarith

def logarithmicThreshold : ℕ := ⌈Real.exp 1⌉₊

lemma logarithmicThreshold_pos : 0 < logarithmicThreshold := by
  rw [logarithmicThreshold, Nat.ceil_pos]
  exact Real.exp_pos 1

lemma one_le_log_nat {N : ℕ} (hN : logarithmicThreshold ≤ N) :
    (1 : ℝ) ≤ Real.log (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast logarithmicThreshold_pos.trans_le hN
  rw [Real.le_log_iff_exp_le hNpos]
  exact (Nat.le_ceil (Real.exp 1)).trans (by exact_mod_cast hN)

lemma polylog_one_le_one {N : ℕ} (hN : logarithmicThreshold ≤ N) :
    (N : ℝ) / Real.rpow (Real.log (N : ℝ)) 1 ≤ N := by
  rw [show Real.rpow (Real.log (N : ℝ)) 1 = Real.log (N : ℝ) from
    Real.rpow_one _]
  have hlog := one_le_log_nat hN
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  calc
    (N : ℝ) / Real.log (N : ℝ) ≤ (N : ℝ) / 1 :=
      div_le_div_of_nonneg_left hNnonneg zero_lt_one hlog
    _ = N := by simp

theorem hasPolylogLowerBound_of_lt_one
    (admissible : ℝ → ℕ → Finset ℕ → Prop) {C : ℝ} (hC : C < 1)
    (hMass : ∀ {N : ℕ} {A : Finset ℕ}, admissible C N A →
      reciprocalMass A ≤ C) :
    HasPolylogLowerBound admissible C := by
  refine ⟨1, 1 - C, zero_lt_one, sub_pos.mpr hC, logarithmicThreshold, ?_⟩
  intro N hN A hA
  have hScale := polylog_one_le_one hN
  have hNonneg : 0 ≤ (1 - C) := (sub_pos.mpr hC).le
  calc
    (1 - C) * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) 1 =
        (1 - C) * ((N : ℝ) / Real.rpow (Real.log (N : ℝ)) 1) := by ring
    _ ≤ (1 - C) * (N : ℝ) := mul_le_mul_of_nonneg_left hScale hNonneg
    _ ≤ ((unsieved N A).card : ℝ) :=
      cast_card_unsieved_lower_bound (hMass hA)

theorem literalAnswer_of_lt_one {C : ℝ} (hC : C < 1) :
    LiteralAnswer C :=
  hasPolylogLowerBound_of_lt_one LiteralAdmissible hC fun hA => hA.2

theorem correctedAnswer_of_lt_one {C : ℝ} (hC : C < 1) :
    CorrectedAnswer C :=
  hasPolylogLowerBound_of_lt_one Admissible hC fun hA => hA.2

/-! ## The endpoint combinatorics -/

/-- The part of the sifting set which can remove integers at most `Y`. -/
def smallPart (Y : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (· ≤ Y)

/-- Primes in the interval `(Y, N]`. -/
def largePrimes (Y N : ℕ) : Finset ℕ :=
  N.primesLE \ Y.primesLE

/-- Large primes which actually occur in the sifting set. -/
def selectedLargePrimes (Y N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  largePrimes Y N ∩ A

lemma reciprocalMass_nonneg (A : Finset ℕ) : 0 ≤ reciprocalMass A := by
  exact sum_nonneg fun _ _ => inv_nonneg.mpr (by positivity)

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  rw [reciprocalMass, reciprocalMass]
  exact sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => by positivity

lemma reciprocalMass_largePrimes {Y N : ℕ} (hYN : Y ≤ N) :
    reciprocalMass (largePrimes Y N) =
      Erdos784.Analytic.primeReciprocals N -
        Erdos784.Analytic.primeReciprocals Y := by
  have hsub : Y.primesLE ⊆ N.primesLE := by
    intro p hp
    have hpData := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpData.1.trans hYN, hpData.2⟩
  rw [reciprocalMass, largePrimes,
    Erdos784.Analytic.primeReciprocals,
    Erdos784.Analytic.primeReciprocals]
  exact eq_sub_iff_add_eq.mpr (sum_sdiff hsub)

lemma unsieved_mono_endpoint {Y N : ℕ} (hYN : Y ≤ N) (A : Finset ℕ) :
    unsieved Y A ⊆ unsieved N A := by
  intro n hn
  obtain ⟨hn1, hnY, hnA⟩ := mem_unsieved.mp hn
  exact mem_unsieved.mpr ⟨hn1, hnY.trans hYN, hnA⟩

lemma unsieved_smallPart {C : ℝ} {Y N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) :
    unsieved Y (smallPart Y A) = unsieved Y A := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn1, hnY, hnSmall⟩ := mem_unsieved.mp hn
    refine mem_unsieved.mpr ⟨hn1, hnY, ?_⟩
    intro a haA hadvd
    have ha2 : 2 ≤ a := (mem_Icc.mp (hA.1 haA)).1
    have haY : a ≤ Y := (Nat.le_of_dvd (by omega) hadvd).trans hnY
    exact hnSmall a (by simp [smallPart, haA, haY]) hadvd
  · intro hn
    obtain ⟨hn1, hnY, hnA⟩ := mem_unsieved.mp hn
    refine mem_unsieved.mpr ⟨hn1, hnY, ?_⟩
    intro a haSmall
    exact hnA a (mem_filter.mp haSmall).1

lemma smallPart_mass_lower {Y N : ℕ} {A : Finset ℕ}
    (hA : Admissible 1 N A) (hY : 0 < Y) :
    1 - ((unsieved Y A).card : ℝ) / Y ≤ reciprocalMass (smallPart Y A) := by
  have hPartition := cast_card_unsieved_add_cast_card_covered Y (smallPart Y A)
  rw [unsieved_smallPart hA] at hPartition
  have hCovered := card_covered_cast_le_mass Y (smallPart Y A)
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    1 - ((unsieved Y A).card : ℝ) / Y =
        ((covered Y (smallPart Y A)).card : ℝ) / Y := by
      field_simp
      linarith
    _ ≤ reciprocalMass (smallPart Y A) := by
      apply (div_le_iff₀ hYR).2
      simpa [mul_comm] using hCovered

@[simp] lemma mem_largePrimes {Y N p : ℕ} :
    p ∈ largePrimes Y N ↔ p.Prime ∧ Y < p ∧ p ≤ N := by
  change p ∈ N.primesLE \ Y.primesLE ↔ _
  rw [Finset.mem_sdiff]
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpY⟩
    exact ⟨hp, lt_of_not_ge fun h => hpY ⟨h, hp⟩, hpN⟩
  · rintro ⟨hp, hYp, hpN⟩
    exact ⟨⟨hpN, hp⟩, fun h => (not_le_of_gt hYp) h.1⟩

lemma exceptionalLargePrimes_subset_unsieved {C : ℝ} {Y N : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) :
    largePrimes Y N \ A ⊆ unsieved N A := by
  intro p hp
  have hpLarge := mem_largePrimes.mp (mem_sdiff.mp hp).1
  have hpNotA := (mem_sdiff.mp hp).2
  refine mem_unsieved.mpr ⟨hpLarge.1.pos, hpLarge.2.2, ?_⟩
  intro a haA hadvd
  rcases hpLarge.1.eq_one_or_self_of_dvd a hadvd with ha1 | hap
  · have ha2 : 2 ≤ a := (mem_Icc.mp (hA.1 haA)).1
    omega
  · exact hpNotA (hap ▸ haA)

lemma card_largePrimes_le_selected_add_unsieved {C : ℝ} {Y N : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) :
    (largePrimes Y N).card ≤
      (selectedLargePrimes Y N A).card + (unsieved N A).card := by
  have hExceptional : (largePrimes Y N \ A).card ≤ (unsieved N A).card :=
    card_le_card (exceptionalLargePrimes_subset_unsieved hA)
  have hSplit := card_sdiff_add_card_inter (largePrimes Y N) A
  dsimp [selectedLargePrimes]
  omega

lemma selectedLargePrimes_mass_lower {Y N : ℕ} {A : Finset ℕ} :
    ((selectedLargePrimes Y N A).card : ℝ) / N ≤
      reciprocalMass (selectedLargePrimes Y N A) := by
  rw [reciprocalMass]
  calc
    ((selectedLargePrimes Y N A).card : ℝ) / N =
        ∑ _p ∈ selectedLargePrimes Y N A, (1 : ℝ) / N := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ p ∈ selectedLargePrimes Y N A, (1 : ℝ) / p := by
      apply sum_le_sum
      intro p hp
      have hpLarge : p ∈ largePrimes Y N := (mem_inter.mp hp).1
      have hpData := mem_largePrimes.mp hpLarge
      exact one_div_le_one_div_of_le (by exact_mod_cast hpData.1.pos)
        (by exact_mod_cast hpData.2.2)
    _ = ∑ p ∈ selectedLargePrimes Y N A, (p : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro p _
      rw [one_div]

lemma smallPart_disjoint_selectedLargePrimes (Y N : ℕ) (A : Finset ℕ) :
    Disjoint (smallPart Y A) (selectedLargePrimes Y N A) := by
  rw [disjoint_left]
  intro a haSmall haLarge
  have haY : a ≤ Y := (mem_filter.mp haSmall).2
  have hYa : Y < a := (mem_largePrimes.mp (mem_inter.mp haLarge).1).2.1
  omega

lemma small_add_selected_mass_le {Y N : ℕ} (A : Finset ℕ) :
    reciprocalMass (smallPart Y A) +
        reciprocalMass (selectedLargePrimes Y N A) ≤ reciprocalMass A := by
  have hSubset : smallPart Y A ∪ selectedLargePrimes Y N A ⊆ A := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact (mem_filter.mp ha).1
    · exact (mem_inter.mp ha).2
  calc
    reciprocalMass (smallPart Y A) +
        reciprocalMass (selectedLargePrimes Y N A) =
        reciprocalMass (smallPart Y A ∪ selectedLargePrimes Y N A) := by
      simp only [reciprocalMass]
      exact (sum_union (smallPart_disjoint_selectedLargePrimes Y N A)).symm
    _ ≤ reciprocalMass A := reciprocalMass_mono hSubset

/-- The finite combinatorial heart of Ruzsa's endpoint lower bound.  A set
of reciprocal mass at most one must leave enough survivors to account for
the primes in every terminal interval. -/
theorem largePrimes_card_div_le_survivors {Y N : ℕ} {A : Finset ℕ}
    (hA : Admissible 1 N A) (hY : 0 < Y) (hYN : Y ≤ N) :
    ((largePrimes Y N).card : ℝ) / N ≤
      ((unsieved N A).card : ℝ) * ((1 : ℝ) / Y + 1 / N) := by
  have hN : 0 < N := hY.trans_le hYN
  have hSmall := smallPart_mass_lower hA hY
  have hUnsievedMono : (unsieved Y A).card ≤ (unsieved N A).card :=
    card_le_card (unsieved_mono_endpoint hYN A)
  have hSmall' :
      1 - ((unsieved N A).card : ℝ) / Y ≤ reciprocalMass (smallPart Y A) := by
    have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
    have hCardCast : ((unsieved Y A).card : ℝ) ≤ (unsieved N A).card := by
      exact_mod_cast hUnsievedMono
    exact (sub_le_sub_left (div_le_div_of_nonneg_right hCardCast hYR.le) 1).trans hSmall
  have hSelected := selectedLargePrimes_mass_lower (A := A) (Y := Y) (N := N)
  have hMassPieces := small_add_selected_mass_le (Y := Y) (N := N) A
  have hBudget := hA.2
  have hCard := card_largePrimes_le_selected_add_unsieved (Y := Y) hA
  have hCardCast :
      ((largePrimes Y N).card : ℝ) ≤
        (selectedLargePrimes Y N A).card + (unsieved N A).card := by
    exact_mod_cast hCard
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hSelectedUpper :
      reciprocalMass (selectedLargePrimes Y N A) ≤
        ((unsieved N A).card : ℝ) / Y := by
    linarith
  calc
    ((largePrimes Y N).card : ℝ) / N ≤
        (((selectedLargePrimes Y N A).card : ℝ) +
          (unsieved N A).card) / N := div_le_div_of_nonneg_right hCardCast hNR.le
    _ = ((selectedLargePrimes Y N A).card : ℝ) / N +
        ((unsieved N A).card : ℝ) / N := by rw [add_div]
    _ ≤ reciprocalMass (selectedLargePrimes Y N A) +
        ((unsieved N A).card : ℝ) / N := add_le_add hSelected le_rfl
    _ ≤ ((unsieved N A).card : ℝ) / Y +
        ((unsieved N A).card : ℝ) / N := add_le_add hSelectedUpper le_rfl
    _ = ((unsieved N A).card : ℝ) * ((1 : ℝ) / Y + 1 / N) := by ring

def endpointPrimeConstant : ℝ := Real.log 2 / 2

lemma endpointPrimeConstant_pos : 0 < endpointPrimeConstant := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

def endpointCeilLog (N : ℕ) : ℕ := ⌈Real.log (N : ℝ)⌉₊

def endpointCutoff (N : ℕ) : ℕ := N / (endpointCeilLog N) ^ 2

lemma half_real_div_le_nat_div {n p : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ n) :
    (n : ℝ) / (2 * p) ≤ (n / p : ℕ) := by
  have htwo : 2 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using h2p)
  have hltNat : n < p * (n / p + 1) := by
    calc
      n = n % p + p * (n / p) := (Nat.mod_add_div n p).symm
      _ < p + p * (n / p) := Nat.add_lt_add_right (Nat.mod_lt n hp) _
      _ = p * (n / p + 1) := by ring
  have hlt : (n : ℝ) < (p : ℝ) * ((n / p : ℕ) + 1) := by
    exact_mod_cast hltNat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have htwoR : (2 : ℝ) ≤ (n / p : ℕ) := by exact_mod_cast htwo
  rw [div_le_iff₀ (mul_pos (by norm_num) hpR)]
  nlinarith

lemma endpointCeilLog_pos {N : ℕ} (hlog : 0 < Real.log (N : ℝ)) :
    0 < endpointCeilLog N := by
  rw [endpointCeilLog, Nat.ceil_pos]
  exact hlog

lemma endpointCeilLog_cast_bounds {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ≤ (endpointCeilLog N : ℝ) ∧
      (endpointCeilLog N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  constructor
  · exact Nat.le_ceil _
  · have hceil : (endpointCeilLog N : ℝ) < Real.log (N : ℝ) + 1 := by
      simpa only [endpointCeilLog] using
        Nat.ceil_lt_add_one (show 0 ≤ Real.log (N : ℝ) from hlog.trans' zero_le_one)
    linarith

lemma endpointCutoff_bounds {N : ℕ}
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hsize : 2 * (endpointCeilLog N) ^ 2 ≤ N) :
    0 < endpointCutoff N ∧ endpointCutoff N ≤ N ∧
      (N : ℝ) / (8 * (Real.log (N : ℝ)) ^ 2) ≤ endpointCutoff N ∧
      (endpointCutoff N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  let q := endpointCeilLog N
  have hsizeq : 2 * q ^ 2 ≤ N := by simpa only [q] using hsize
  have hq : 0 < q := endpointCeilLog_pos (zero_lt_one.trans_le hlog)
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have hq2N : q ^ 2 ≤ N := by omega
  have hYpos : 0 < N / q ^ 2 := Nat.div_pos hq2N hq2
  have hYN : N / q ^ 2 ≤ N := Nat.div_le_self _ _
  have hqBounds := endpointCeilLog_cast_bounds hlog
  have hqSqUpper : ((q : ℝ) ^ 2) ≤ 4 * (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - 2 * Real.log (N : ℝ))]
  have hqSqLower : (Real.log (N : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - Real.log (N : ℝ))]
  have hlogPos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hHalf : (N : ℝ) / (2 * (q : ℝ) ^ 2) ≤ (N / q ^ 2 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using
      half_real_div_le_nat_div hq2 hsizeq
  have hLower :
      (N : ℝ) / (8 * (Real.log (N : ℝ)) ^ 2) ≤
        (N : ℝ) / (2 * (q : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left hNnonneg (by positivity)
    nlinarith
  have hCastDiv : ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) ^ 2 := by
    calc
      ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((q ^ 2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      _ = (N : ℝ) / (q : ℝ) ^ 2 := by norm_cast
  have hUpper : (N : ℝ) / (q : ℝ) ^ 2 ≤
      (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    exact div_le_div_of_nonneg_left hNnonneg (sq_pos_of_pos hlogPos) hqSqLower
  change 0 < N / q ^ 2 ∧ N / q ^ 2 ≤ N ∧
    (N : ℝ) / (8 * Real.log (N : ℝ) ^ 2) ≤ (N / q ^ 2 : ℕ) ∧
    ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2
  exact ⟨hYpos, hYN, hLower.trans hHalf, hCastDiv.trans hUpper⟩

lemma card_largePrimes_eq_sub {Y N : ℕ} (hYN : Y ≤ N) :
    (largePrimes Y N).card = Nat.primeCounting N - Nat.primeCounting Y := by
  rw [largePrimes, card_sdiff_of_subset (Nat.primesLE_mono hYN)]
  simp

lemma primeCounting_le_self (N : ℕ) : Nat.primeCounting N ≤ N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    N.primesLE.card ≤ (Icc 1 N).card := by
      apply card_le_card
      intro p hp
      have hpData := Nat.mem_primesLE.mp hp
      exact mem_Icc.mpr ⟨hpData.2.pos, hpData.1⟩
    _ = N := by simp [Nat.card_Icc]

/-- Quantitative endpoint bound after separating the finite combinatorics
from the two eventual analytic inequalities. -/
theorem endpoint_lower_of_conditions {N : ℕ}
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hlogLarge : 2 / endpointPrimeConstant ≤ Real.log (N : ℝ))
    (hsize : 2 * (endpointCeilLog N) ^ 2 ≤ N)
    (hPrime : endpointPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ≤
      (Nat.primeCounting N : ℝ))
    (A : Finset ℕ) (hA : Admissible 1 N A) :
    endpointPrimeConstant / 18 * (N : ℝ) /
        Real.rpow (Real.log (N : ℝ)) 3 ≤ (unsieved N A).card := by
  let Y := endpointCutoff N
  have hBounds := endpointCutoff_bounds hlog hsize
  have hY : 0 < Y := hBounds.1
  have hYN : Y ≤ N := hBounds.2.1
  have hYLower :
      (N : ℝ) / (8 * Real.log (N : ℝ) ^ 2) ≤ (Y : ℝ) := hBounds.2.2.1
  have hYUpper :
      (Y : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := hBounds.2.2.2
  have hd : 0 < endpointPrimeConstant := endpointPrimeConstant_pos
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hN : 0 < N := hY.trans_le hYN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdL : 2 ≤ endpointPrimeConstant * Real.log (N : ℝ) := by
    have := (div_le_iff₀ hd).mp hlogLarge
    nlinarith
  have hYSmall :
      (Y : ℝ) ≤ endpointPrimeConstant / 2 * (N : ℝ) / Real.log (N : ℝ) := by
    calc
      (Y : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := hYUpper
      _ ≤ endpointPrimeConstant / 2 * (N : ℝ) / Real.log (N : ℝ) := by
        field_simp
        nlinarith
  have hPiMono : Nat.primeCounting Y ≤ Nat.primeCounting N :=
    Nat.monotone_primeCounting hYN
  have hCardEq :
      ((largePrimes Y N).card : ℝ) =
        (Nat.primeCounting N : ℝ) - Nat.primeCounting Y := by
    rw [card_largePrimes_eq_sub hYN, Nat.cast_sub hPiMono]
  have hPiY : ((Nat.primeCounting Y : ℕ) : ℝ) ≤ Y := by
    exact_mod_cast primeCounting_le_self Y
  have hCardLower :
      endpointPrimeConstant / 2 * (N : ℝ) / Real.log (N : ℝ) ≤
        ((largePrimes Y N).card : ℝ) := by
    calc
      endpointPrimeConstant / 2 * (N : ℝ) / Real.log (N : ℝ) =
          endpointPrimeConstant * (N : ℝ) / Real.log (N : ℝ) -
            endpointPrimeConstant / 2 * (N : ℝ) / Real.log (N : ℝ) := by ring
      _ ≤ (Nat.primeCounting N : ℝ) - (Y : ℝ) := sub_le_sub hPrime hYSmall
      _ ≤ (Nat.primeCounting N : ℝ) - Nat.primeCounting Y :=
        sub_le_sub_left hPiY _
      _ = ((largePrimes Y N).card : ℝ) := hCardEq.symm
  have hInvY :
      (1 : ℝ) / Y ≤ 8 * Real.log (N : ℝ) ^ 2 / N := by
    have hbase : 0 < (N : ℝ) / (8 * Real.log (N : ℝ) ^ 2) := by positivity
    calc
      (1 : ℝ) / Y ≤ 1 / ((N : ℝ) / (8 * Real.log (N : ℝ) ^ 2)) :=
        one_div_le_one_div_of_le hbase hYLower
      _ = 8 * Real.log (N : ℝ) ^ 2 / N := by field_simp
  have hInvN : (1 : ℝ) / N ≤ Real.log (N : ℝ) ^ 2 / N := by
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)])
      hNR.le
  have hDenom :
      (1 : ℝ) / Y + 1 / N ≤ 9 * Real.log (N : ℝ) ^ 2 / N := by
    calc
      (1 : ℝ) / Y + 1 / N ≤
          8 * Real.log (N : ℝ) ^ 2 / N +
            Real.log (N : ℝ) ^ 2 / N := add_le_add hInvY hInvN
      _ = 9 * Real.log (N : ℝ) ^ 2 / N := by ring
  have hFinite := largePrimes_card_div_le_survivors hA hY hYN
  have hCardDivLower :
      endpointPrimeConstant / (2 * Real.log (N : ℝ)) ≤
        ((largePrimes Y N).card : ℝ) / N := by
    calc
      endpointPrimeConstant / (2 * Real.log (N : ℝ)) =
          (endpointPrimeConstant / 2 * (N : ℝ) /
            Real.log (N : ℝ)) / N := by field_simp
      _ ≤ ((largePrimes Y N).card : ℝ) / N :=
        div_le_div_of_nonneg_right hCardLower hNR.le
  have hSurvivorsNonneg : (0 : ℝ) ≤ (unsieved N A).card := by positivity
  have hCombined :
      endpointPrimeConstant / (2 * Real.log (N : ℝ)) ≤
        ((unsieved N A).card : ℝ) *
          (9 * Real.log (N : ℝ) ^ 2 / N) :=
    hCardDivLower.trans (hFinite.trans
      (mul_le_mul_of_nonneg_left hDenom hSurvivorsNonneg))
  have hFactor : 0 < 9 * Real.log (N : ℝ) ^ 2 / (N : ℝ) := by positivity
  have hSolved :
      (endpointPrimeConstant / (2 * Real.log (N : ℝ))) /
          (9 * Real.log (N : ℝ) ^ 2 / (N : ℝ)) ≤ (unsieved N A).card := by
    apply (div_le_iff₀ hFactor).2
    simpa [mul_comm] using hCombined
  calc
    endpointPrimeConstant / 18 * (N : ℝ) /
        Real.rpow (Real.log (N : ℝ)) 3 =
        (endpointPrimeConstant / (2 * Real.log (N : ℝ))) /
          (9 * Real.log (N : ℝ) ^ 2 / (N : ℝ)) := by
      rw [show Real.rpow (Real.log (N : ℝ)) 3 =
        Real.log (N : ℝ) ^ (3 : ℕ) from Real.rpow_natCast _ 3]
      field_simp
      ring
    _ ≤ (unsieved N A).card := hSolved

lemma eventually_endpoint_log_conditions :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
        2 / endpointPrimeConstant ≤ Real.log (N : ℝ) := by
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually
    (eventually_ge_atTop (max 1 (2 / endpointPrimeConstant)))] with N hN
  exact ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩

lemma eventually_endpoint_cutoff_size :
    ∀ᶠ N : ℕ in atTop, 2 * (endpointCeilLog N) ^ 2 ≤ N := by
  have hsmallReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (by norm_num : (0 : ℝ) < 1 / 8)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_endpoint_log_conditions] with N hsmall hlog
  have hlogSqSmall : Real.log (N : ℝ) ^ 2 ≤ (1 / 8 : ℝ) * N := by
    simpa only [Real.norm_eq_abs, id_eq,
      abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),
      abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) by positivity)] using hsmall
  have hqBounds := endpointCeilLog_cast_bounds hlog.1
  have hqSq : ((endpointCeilLog N : ℝ) ^ 2) ≤
      4 * Real.log (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((endpointCeilLog N : ℝ) - 2 * Real.log (N : ℝ))]
  have hreal : (2 * (endpointCeilLog N) ^ 2 : ℕ) ≤ (N : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

lemma eventually_endpoint_prime_lower :
    ∀ᶠ N : ℕ in atTop,
      endpointPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ≤
        (Nat.primeCounting N : ℝ) := by
  have hd : 0 < endpointPrimeConstant := endpointPrimeConstant_pos
  have hsmallReal := Real.isLittleO_log_id_atTop.bound (half_pos hd)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_endpoint_log_conditions,
    eventually_ge_atTop 4] with N hsmall hlog hN4
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLogSmall :
      Real.log (N : ℝ) ≤ endpointPrimeConstant / 2 * (N : ℝ) := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_nonneg hL.le,
      abs_of_nonneg hNpos.le] using hsmall
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hSuccLog :
      Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log (N : ℝ) := by
    calc
      Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show N + 1 ≤ 2 * N by omega)
      _ = Real.log 2 + Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num) hNne]
  have hLogTwo :
      Real.log 2 ≤ endpointPrimeConstant / 2 * (N : ℝ) := by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hN4R : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    calc
      Real.log 2 = (Real.log 2 / 4) * 4 := by ring
      _ ≤ (Real.log 2 / 4) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN4R (by positivity)
      _ = endpointPrimeConstant / 2 * (N : ℝ) := by
        rw [endpointPrimeConstant]
        ring
  have hSuccSmall :
      Real.log ((N + 1 : ℕ) : ℝ) ≤ endpointPrimeConstant * (N : ℝ) := by
    linarith
  have hNumerator :
      endpointPrimeConstant * (N : ℝ) ≤
        (N : ℝ) * Real.log 2 - Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [endpointPrimeConstant] at hSuccSmall ⊢
    linarith
  calc
    endpointPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ≤
        ((N : ℝ) * Real.log 2 - Real.log ((N + 1 : ℕ) : ℝ)) /
          Real.log (N : ℝ) := div_le_div_of_nonneg_right hNumerator hL.le
    _ ≤ (Nat.primeCounting N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Chebyshev.pi_ge N

lemma eventually_endpoint_conditions :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
      2 / endpointPrimeConstant ≤ Real.log (N : ℝ) ∧
      2 * (endpointCeilLog N) ^ 2 ≤ N ∧
      endpointPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ≤
        (Nat.primeCounting N : ℝ) := by
  filter_upwards [eventually_endpoint_log_conditions,
    eventually_endpoint_cutoff_size, eventually_endpoint_prime_lower] with N hlog hsize hprime
  exact ⟨hlog.1, hlog.2, hsize, hprime⟩

/-- Ruzsa's positive endpoint, in the exact strength needed by Problem 784.
The proof above gives an explicit exponent `3`; the sharp order is
`N / log N`. -/
theorem correctedAnswer_one : CorrectedAnswer 1 := by
  refine ⟨3, endpointPrimeConstant / 18, by norm_num,
    div_pos endpointPrimeConstant_pos (by norm_num), ?_⟩
  have hConditions := eventually_endpoint_conditions
  rw [eventually_atTop] at hConditions
  obtain ⟨N₀, hN₀⟩ := hConditions
  refine ⟨N₀, ?_⟩
  intro N hN A hA
  exact endpoint_lower_of_conditions (hN₀ N hN).1 (hN₀ N hN).2.1
    (hN₀ N hN).2.2.1 (hN₀ N hN).2.2.2 A hA

theorem correctedAnswer_of_pos_of_le_one {C : ℝ} (hC : 0 < C) (hC1 : C ≤ 1) :
    CorrectedAnswer C := by
  rcases hC1.lt_or_eq with hlt | rfl
  · exact correctedAnswer_of_lt_one hlt
  · exact correctedAnswer_one

/-! ## The Schinzel--Szekeres boundary construction -/

/-- `ssGood Y n` means that every nontrivial divisor `d` of `n` satisfies
`d * P⁻(d) ≤ Y`.  This is the predicate `F(n) ≤ Y`, written without taking
a finite maximum. -/
def ssGood (Y n : ℕ) : Prop :=
  ∀ d : ℕ, d ∣ n → 1 < d → d * d.minFac ≤ Y

/-- The minimal elements, for divisibility, outside `ssGood Y`. -/
def ssBoundary (Y : ℕ) : Finset ℕ :=
  (Icc 2 Y).filter fun b =>
    ¬ssGood Y b ∧ ∀ d : ℕ, d ∣ b → d < b → ssGood Y d

@[simp] lemma ssGood_one (Y : ℕ) : ssGood Y 1 := by
  intro d hd hd1
  have : d ≤ 1 := Nat.le_of_dvd (by omega) hd
  omega

lemma ssGood_of_dvd {Y m n : ℕ} (hn : ssGood Y n) (hmn : m ∣ n) : ssGood Y m := by
  intro d hdm hd1
  exact hn d (hdm.trans hmn) hd1

@[simp] lemma mem_ssBoundary {Y b : ℕ} :
    b ∈ ssBoundary Y ↔
      2 ≤ b ∧ b ≤ Y ∧ ¬ssGood Y b ∧
        ∀ d : ℕ, d ∣ b → d < b → ssGood Y d := by
  simp only [ssBoundary, mem_filter, mem_Icc]
  tauto

lemma ssBoundary_not_good {Y b : ℕ} (hb : b ∈ ssBoundary Y) : ¬ssGood Y b :=
  (mem_ssBoundary.mp hb).2.2.1

lemma ssBoundary_self_bad {Y b : ℕ} (hb : b ∈ ssBoundary Y) :
    Y < b * b.minFac := by
  have hnot := ssBoundary_not_good hb
  simp only [ssGood] at hnot
  push Not at hnot
  obtain ⟨d, hdb, hd1, hbad⟩ := hnot
  have hdb_le : d ≤ b := Nat.le_of_dvd (by
    have := (mem_ssBoundary.mp hb).1
    omega) hdb
  have hdb_eq : d = b := by
    by_contra hne
    have hlt : d < b := lt_of_le_of_ne hdb_le hne
    have hgood := (mem_ssBoundary.mp hb).2.2.2 d hdb hlt
    exact (not_le_of_gt hbad) (hgood d dvd_rfl hd1)
  simpa [hdb_eq] using hbad

lemma ssBoundary_antichain {Y a b : ℕ}
    (ha : a ∈ ssBoundary Y) (hb : b ∈ ssBoundary Y) (hab : a ∣ b) : a = b := by
  have hale : a ≤ b := Nat.le_of_dvd (by
    have := (mem_ssBoundary.mp hb).1
    omega) hab
  rcases hale.eq_or_lt with h | h
  · exact h
  · exact False.elim <| ssBoundary_not_good ha
      ((mem_ssBoundary.mp hb).2.2.2 a hab h)

lemma ssBoundary_lcm_gt {Y a b : ℕ}
    (ha : a ∈ ssBoundary Y) (hb : b ∈ ssBoundary Y) (hne : a ≠ b) :
    Y < a.lcm b := by
  by_contra hnot
  have hlY : a.lcm b ≤ Y := le_of_not_gt hnot
  let g := a.gcd b
  let qa := a / g
  let qb := b / g
  have haPos : 0 < a := by have := (mem_ssBoundary.mp ha).1; omega
  have hbPos : 0 < b := by have := (mem_ssBoundary.mp hb).1; omega
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_left b haPos
  have hga : g * qa = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * qb = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hla : a.lcm b = a * qb := by
    apply Nat.eq_of_mul_eq_mul_left hgPos
    calc
      g * a.lcm b = a * b := Nat.gcd_mul_lcm a b
      _ = a * (g * qb) := by rw [hgb]
      _ = g * (a * qb) := by ac_rfl
  have hlb : a.lcm b = b * qa := by
    apply Nat.eq_of_mul_eq_mul_left hgPos
    calc
      g * a.lcm b = a * b := Nat.gcd_mul_lcm a b
      _ = (g * qa) * b := by rw [hga]
      _ = g * (b * qa) := by ac_rfl
  have hna : ¬a ∣ b := fun hab => hne (ssBoundary_antichain ha hb hab)
  have hnb : ¬b ∣ a := fun hba => hne (ssBoundary_antichain hb ha hba).symm
  have hqa2 : 2 ≤ qa := by
    have hqa0 : 0 < qa := Nat.div_pos (Nat.gcd_le_left b haPos) hgPos
    by_contra h
    have hqa1 : qa = 1 := by omega
    apply hna
    refine ⟨qb, ?_⟩
    calc
      b = g * qb := hgb.symm
      _ = a * qb := by rw [← hga, hqa1]; simp
  have hqb2 : 2 ≤ qb := by
    have hqb0 : 0 < qb := Nat.div_pos (Nat.gcd_le_right a hbPos) hgPos
    by_contra h
    have hqb1 : qb = 1 := by omega
    apply hnb
    refine ⟨qa, ?_⟩
    calc
      a = g * qa := hga.symm
      _ = b * qa := by rw [← hgb, hqb1]; simp
  have hmina : a.minFac ≤ qa :=
    Nat.minFac_le_of_dvd hqa2 ⟨g, by simpa [mul_comm] using hga.symm⟩
  have hminb : b.minFac ≤ qb :=
    Nat.minFac_le_of_dvd hqb2 ⟨g, by simpa [mul_comm] using hgb.symm⟩
  have hqb_lt : qb < a.minFac := by
    apply (Nat.mul_lt_mul_left haPos).mp
    rw [← hla]
    exact hlY.trans_lt (ssBoundary_self_bad ha)
  have hqa_lt : qa < b.minFac := by
    apply (Nat.mul_lt_mul_left hbPos).mp
    rw [← hlb]
    exact hlY.trans_lt (ssBoundary_self_bad hb)
  have hqbqa : qb < qa := hqb_lt.trans_le hmina
  have hqaqb : qa < qb := hqa_lt.trans_le hminb
  exact (not_lt_of_ge hqbqa.le) hqaqb

lemma ssBoundary_multiples_pairwise (Y : ℕ) :
    ((ssBoundary Y : Set ℕ).PairwiseDisjoint (multiplesIn Y)) := by
  intro a ha b hb hab
  change Disjoint (multiplesIn Y a) (multiplesIn Y b)
  rw [Finset.disjoint_left]
  intro n hna hnb
  have hna' := mem_filter.mp hna
  have hnb' := mem_filter.mp hnb
  have hlcm : a.lcm b ∣ n := Nat.lcm_dvd hna'.2 hnb'.2
  have hnPos : 0 < n := (mem_Ioc.mp hna'.1).1
  have hlcm_le_n := Nat.le_of_dvd hnPos hlcm
  have hnY := (mem_Ioc.mp hna'.1).2
  exact (not_le_of_gt (ssBoundary_lcm_gt ha hb hab)) (hlcm_le_n.trans hnY)

lemma sum_boundary_div_le (Y : ℕ) :
    ∑ b ∈ ssBoundary Y, Y / b ≤ Y := by
  have hcard := card_biUnion (ssBoundary_multiples_pairwise Y)
  have hsub : (ssBoundary Y).biUnion (multiplesIn Y) ⊆ Ioc 0 Y := by
    intro n hn
    simp only [mem_biUnion] at hn
    obtain ⟨b, _hb, hnb⟩ := hn
    exact (mem_filter.mp hnb).1
  calc
    ∑ b ∈ ssBoundary Y, Y / b = ((ssBoundary Y).biUnion (multiplesIn Y)).card := by
      rw [hcard]
      apply sum_congr rfl
      intro b _
      exact (Nat.Ioc_filter_dvd_card_eq_div Y b).symm
    _ ≤ (Ioc 0 Y).card := card_le_card hsub
    _ = Y := by simp

lemma one_div_le_div_add_one_div {Y b : ℕ} (hY : 0 < Y) (hb : 0 < b) :
    (1 : ℝ) / b ≤ ((Y / b : ℕ) : ℝ) / Y + 1 / Y := by
  have hNat : Y ≤ b * (Y / b + 1) := (Nat.lt_mul_div_succ Y hb).le
  have hCast : (Y : ℝ) ≤ (b : ℝ) * ((Y / b : ℕ) + 1) := by exact_mod_cast hNat
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (div_le_iff₀ hbR).2
  rw [← add_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hYR).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hCast

lemma ssBoundary_mass_le {Y : ℕ} (hY : 0 < Y) :
    reciprocalMass (ssBoundary Y) ≤ 1 + ((ssBoundary Y).card : ℝ) / Y := by
  have hPoint (b : ℕ) (hb : b ∈ ssBoundary Y) :
      (b : ℝ)⁻¹ ≤ ((Y / b : ℕ) : ℝ) / Y + 1 / Y := by
    rw [← one_div]
    exact one_div_le_div_add_one_div hY (by
      have := (mem_ssBoundary.mp hb).1
      omega)
  rw [reciprocalMass]
  calc
    ∑ b ∈ ssBoundary Y, (b : ℝ)⁻¹ ≤
        ∑ b ∈ ssBoundary Y, (((Y / b : ℕ) : ℝ) / Y + 1 / Y) := by
      exact sum_le_sum fun b hb => hPoint b hb
    _ = (∑ b ∈ ssBoundary Y, (Y / b : ℕ) : ℝ) / Y +
        ((ssBoundary Y).card : ℝ) / Y := by
      simp only [sum_add_distrib, sum_div, sum_const, nsmul_eq_mul]
      ring
    _ ≤ 1 + ((ssBoundary Y).card : ℝ) / Y := by
      gcongr
      have hsum : (∑ b ∈ ssBoundary Y, Y / b : ℕ) ≤ Y := sum_boundary_div_le Y
      have hcast : ((∑ b ∈ ssBoundary Y, Y / b : ℕ) : ℝ) ≤ Y := by exact_mod_cast hsum
      exact (div_le_iff₀ (by exact_mod_cast hY : (0 : ℝ) < Y)).2 (by simpa using hcast)

lemma exists_ssBoundary_or_largePrime {Y N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hnBad : ¬ssGood Y n) :
    ∃ b : ℕ, b ∣ n ∧ (b ∈ ssBoundary Y ∨ b ∈ largePrimes Y N) := by
  let P : ℕ → Prop := fun d => d ∣ n ∧ ¬ssGood Y d
  have hP : ∃ d, P d := ⟨n, dvd_rfl, hnBad⟩
  let b := Nat.find hP
  have hbP : P b := Nat.find_spec hP
  have hbPos : 0 < b := Nat.pos_of_dvd_of_pos hbP.1 (by omega)
  have hb1 : 1 < b := by
    by_contra h
    have hbEq : b = 1 := by omega
    exact hbP.2 (hbEq ▸ ssGood_one Y)
  have hbMin : ∀ d : ℕ, d ∣ b → d < b → ssGood Y d := by
    intro d hdb hdb_lt
    by_contra hdBad
    exact (Nat.find_min hP hdb_lt) ⟨hdb.trans hbP.1, hdBad⟩
  refine ⟨b, hbP.1, ?_⟩
  by_cases hbY : b ≤ Y
  · left
    exact mem_ssBoundary.mpr ⟨hb1, hbY, hbP.2, hbMin⟩
  · right
    have hYb : Y < b := lt_of_not_ge hbY
    have hbPrime : b.Prime := by
      by_contra hbNotPrime
      let p := b.minFac
      let m := b / p
      have hpPrime : p.Prime := Nat.minFac_prime (by omega)
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hpm : p ≤ m := Nat.minFac_le_div hbPos hbNotPrime
      have hm2 : 2 ≤ m := hp2.trans hpm
      have hmDvdB : m ∣ b := Nat.div_dvd_of_dvd (Nat.minFac_dvd b)
      have hmDvdN : m ∣ n := hmDvdB.trans hbP.1
      have hmLt : m < b := Nat.div_lt_self hbPos hpPrime.one_lt
      have hpMinM : p ≤ m.minFac := by
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : m ≠ 1)).two_le
          ((Nat.minFac_dvd m).trans hmDvdB)
      have hpmul : p * m = b := Nat.mul_div_cancel' (Nat.minFac_dvd b)
      have hmBadSelf : Y < m * m.minFac := by
        calc
          Y < b := hYb
          _ = p * m := hpmul.symm
          _ = m * p := by ac_rfl
          _ ≤ m * m.minFac := Nat.mul_le_mul_left m hpMinM
      have hmBad : ¬ssGood Y m := by
        intro hmGood
        exact (not_le_of_gt hmBadSelf) (hmGood m dvd_rfl hm2)
      exact (Nat.find_min hP hmLt) ⟨hmDvdN, hmBad⟩
    exact mem_largePrimes.mpr ⟨hbPrime, hYb, (Nat.le_of_dvd (by omega) hbP.1).trans hnN⟩

/-- The actual Ruzsa sifting set: the Schinzel--Szekeres boundary at `Y`,
together with the primes in `(Y,N]`. -/
def ruzsaSet (Y N : ℕ) : Finset ℕ := ssBoundary Y ∪ largePrimes Y N

lemma unsieved_ruzsaSet_subset_good {Y N : ℕ} :
    unsieved N (ruzsaSet Y N) ⊆ (Icc 1 N).filter (ssGood Y) := by
  intro n hn
  have hnData := mem_unsieved.mp hn
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hnData.1, hnData.2.1⟩, ?_⟩
  by_contra hnBad
  obtain ⟨b, hbn, hb⟩ := exists_ssBoundary_or_largePrime
    hnData.1 hnData.2.1 hnBad
  exact hnData.2.2 b (by simpa [ruzsaSet] using hb) hbn

lemma ssGood_le_half {Y n : ℕ} (hn1 : 1 < n) (hn : ssGood Y n) : 2 * n ≤ Y := by
  have hmin2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  simpa [mul_comm] using (Nat.mul_le_mul_left n hmin2).trans (hn n dvd_rfl hn1)

lemma ruzsaSet_survivors_le {Y N : ℕ} (hY : 0 < Y) :
    (unsieved N (ruzsaSet Y N)).card ≤ Y := by
  have hsub : unsieved N (ruzsaSet Y N) ⊆ Icc 1 Y := by
    intro n hn
    have hgood := mem_filter.mp (unsieved_ruzsaSet_subset_good hn)
    have hnRange := mem_Icc.mp hgood.1
    refine mem_Icc.mpr ⟨hnRange.1, ?_⟩
    by_cases hnEq : n = 1
    · omega
    · have hhalf := ssGood_le_half (by omega) hgood.2
      omega
  calc
    (unsieved N (ruzsaSet Y N)).card ≤ (Icc 1 Y).card := card_le_card hsub
    _ ≤ Y := by simp [Nat.card_Icc]

lemma ssBoundary_disjoint_largePrimes (Y N : ℕ) :
    Disjoint (ssBoundary Y) (largePrimes Y N) := by
  rw [Finset.disjoint_left]
  intro b hbBoundary hbPrime
  have hbY := (mem_ssBoundary.mp hbBoundary).2.1
  have hYb := (mem_largePrimes.mp hbPrime).2.1
  omega

lemma reciprocalMass_ruzsaSet {Y N : ℕ} (hYN : Y ≤ N) :
    reciprocalMass (ruzsaSet Y N) =
      reciprocalMass (ssBoundary Y) +
        (Erdos784.Analytic.primeReciprocals N -
          Erdos784.Analytic.primeReciprocals Y) := by
  rw [ruzsaSet, reciprocalMass, sum_union (ssBoundary_disjoint_largePrimes Y N)]
  change reciprocalMass (ssBoundary Y) + reciprocalMass (largePrimes Y N) = _
  rw [reciprocalMass_largePrimes hYN]

lemma ruzsaSet_subset_Icc {Y N : ℕ} (hYN : Y ≤ N) :
    ruzsaSet Y N ⊆ Icc 2 N := by
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · have h := mem_ssBoundary.mp ha
    exact mem_Icc.mpr ⟨h.1, h.2.1.trans hYN⟩
  · have h := mem_largePrimes.mp ha
    exact mem_Icc.mpr ⟨h.1.two_le, h.2.2⟩

open scoped ArithmeticFunction.Omega

lemma ssGood_pow_bound {Y n r : ℕ} (hY : 0 < Y) (hnPos : 0 < n)
    (hnGood : ssGood Y n) (hOmega : Ω n ≤ r) :
    n ^ (2 ^ r) ≤ Y ^ (2 ^ r - 1) := by
  induction r generalizing n with
  | zero =>
      have hOm : Ω n = 0 := by omega
      have hn1 : n = 1 := by
        rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hOm with h | h
        · omega
        · exact h
      simp [hn1]
  | succ r ih =>
      by_cases hn1 : n = 1
      · subst n
        simpa using Nat.one_le_pow (2 ^ (r + 1) - 1) Y hY
      let p := n.minFac
      let m := n / p
      have hpPrime : p.Prime := Nat.minFac_prime hn1
      have hpPos : 0 < p := hpPrime.pos
      have hmPos : 0 < m := Nat.div_pos (Nat.minFac_le hnPos) hpPos
      have hpm : p * m = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have hmDvd : m ∣ n := Nat.div_dvd_of_dvd (Nat.minFac_dvd n)
      have hmGood : ssGood Y m := ssGood_of_dvd hnGood hmDvd
      have hOmegaEq : Ω n = 1 + Ω m := by
        calc
          Ω n = Ω (p * m) := by rw [hpm]
          _ = Ω p + Ω m := ArithmeticFunction.cardFactors_mul hpPrime.ne_zero hmPos.ne'
          _ = 1 + Ω m := by rw [ArithmeticFunction.cardFactors_apply_prime hpPrime]
      have hmOmega : Ω m ≤ r := by omega
      have hmPow := ih hmPos hmGood hmOmega
      have hn1lt : 1 < n := by omega
      have hnp : n * p ≤ Y := hnGood n dvd_rfl hn1lt
      have hnSq : n ^ 2 ≤ Y * m := by
        calc
          n ^ 2 = (n * p) * m := by rw [pow_two, ← hpm]; ac_rfl
          _ ≤ Y * m := Nat.mul_le_mul_right m hnp
      have hPow : (n ^ 2) ^ (2 ^ r) ≤ (Y * m) ^ (2 ^ r) :=
        Nat.pow_le_pow_left hnSq _
      calc
        n ^ (2 ^ (r + 1)) = (n ^ 2) ^ (2 ^ r) := by
          have he : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; omega
          rw [he, pow_mul]
        _ ≤ (Y * m) ^ (2 ^ r) := hPow
        _ = Y ^ (2 ^ r) * m ^ (2 ^ r) := by rw [mul_pow]
        _ ≤ Y ^ (2 ^ r) * Y ^ (2 ^ r - 1) := Nat.mul_le_mul_left _ hmPow
        _ = Y ^ (2 ^ (r + 1) - 1) := by
          rw [← pow_add, pow_succ]
          have : 0 < 2 ^ r := pow_pos (by omega) _
          congr 1
          omega

def omegaCutoff (Y : ℕ) : ℕ :=
  ⌊(7 / 5 : ℝ) * Erdos784.Analytic.logLogNat Y⌋₊

lemma cutoff_pow_two_le {Y : ℕ} (hlog : 1 ≤ Real.log (Y : ℝ)) :
    ((2 ^ omegaCutoff Y : ℕ) : ℝ) ≤
      Real.rpow (Real.log (Y : ℝ)) (99 / 100 : ℝ) := by
  let L := Erdos784.Analytic.logLogNat Y
  have hL : 0 ≤ L := by
    exact Real.log_nonneg hlog
  have hfloor : ((omegaCutoff Y : ℕ) : ℝ) ≤ (7 / 5 : ℝ) * L := by
    exact Nat.floor_le (mul_nonneg (by norm_num) hL)
  have hcoef : (7 / 5 : ℝ) * Real.log 2 < 99 / 100 := by
    have hlog2 := Real.log_two_lt_d9
    norm_num at hlog2 ⊢
    nlinarith
  have hexp : Real.log 2 * (omegaCutoff Y : ℝ) ≤ (99 / 100 : ℝ) * L := by
    calc
      Real.log 2 * (omegaCutoff Y : ℝ) ≤
          Real.log 2 * ((7 / 5 : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hfloor (Real.log_pos (by norm_num)).le
      _ = ((7 / 5 : ℝ) * Real.log 2) * L := by ring
      _ ≤ (99 / 100 : ℝ) * L :=
        mul_le_mul_of_nonneg_right hcoef.le hL
  calc
    ((2 ^ omegaCutoff Y : ℕ) : ℝ) = (2 : ℝ) ^ omegaCutoff Y := by norm_cast
    _ = Real.rpow 2 (omegaCutoff Y : ℝ) :=
      (Real.rpow_natCast 2 (omegaCutoff Y)).symm
    _ = Real.exp (Real.log 2 * (omegaCutoff Y : ℝ)) :=
      Real.rpow_def_of_pos (by norm_num) _
    _ ≤ Real.exp ((99 / 100 : ℝ) * L) := Real.exp_le_exp.mpr hexp
    _ = Real.rpow (Real.log (Y : ℝ)) (99 / 100 : ℝ) := by
      symm
      calc
        Real.rpow (Real.log (Y : ℝ)) (99 / 100 : ℝ) =
            Real.exp (Real.log (Real.log (Y : ℝ)) * (99 / 100 : ℝ)) :=
          Real.rpow_def_of_pos (zero_lt_one.trans_le hlog) _
        _ = Real.exp ((99 / 100 : ℝ) * L) := by
          congr 1
          simp only [L, Erdos784.Analytic.logLogNat]
          ring

lemma eventually_const_mul_cutoff_lt_log {M : ℝ} (hM : 0 < M) :
    ∀ᶠ Y : ℕ in atTop,
      M * ((2 ^ omegaCutoff Y : ℕ) : ℝ) < Real.log (Y : ℝ) := by
  have htlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto
      (fun Y : ℕ => Real.rpow (Real.log (Y : ℝ)) (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp htlog
  filter_upwards [htlog.eventually (eventually_ge_atTop 1),
      hpow.eventually (eventually_gt_atTop M)] with Y hlog hMpow
  have hxpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlog
  have hcut := cutoff_pow_two_le hlog
  calc
    M * ((2 ^ omegaCutoff Y : ℕ) : ℝ) ≤
        M * Real.rpow (Real.log (Y : ℝ)) (99 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hcut hM.le
    _ < Real.rpow (Real.log (Y : ℝ)) (1 / 100 : ℝ) *
        Real.rpow (Real.log (Y : ℝ)) (99 / 100 : ℝ) :=
      mul_lt_mul_of_pos_right hMpow (Real.rpow_pos_of_pos hxpos _)
    _ = Real.rpow (Real.log (Y : ℝ)) ((1 / 100 : ℝ) + 99 / 100) :=
      (Real.rpow_add hxpos _ _).symm
    _ = Real.log (Y : ℝ) := by norm_num

lemma eventually_lowOmega_good_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ Y : ℕ in atTop, ∀ n : ℕ, n ∈ Icc 1 Y → ssGood Y n →
      n ∉ Erdos784.Analytic.highOmega Y → (n : ℝ) ≤ ε * (Y : ℝ) := by
  have hM : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε hε1)
  have hexp := eventually_const_mul_cutoff_lt_log hM
  have htlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hexp, Erdos784.Analytic.eventually_logLogNat_pos,
      htlog.eventually (eventually_ge_atTop 1)] with Y hExp hL hlog
  intro n hnRange hnGood hnHigh
  have hnData := Finset.mem_Icc.mp hnRange
  have hYpos : 0 < Y := by
    by_contra hY
    have : Y = 0 := Nat.eq_zero_of_not_pos hY
    subst Y
    norm_num at hlog
  have hnPos : 0 < n := hnData.1
  have hNotLarge : ¬(7 / 5 : ℝ) * Erdos784.Analytic.logLogNat Y < (Ω n : ℝ) := by
    intro hlarge
    apply hnHigh
    exact mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hnPos, hnData.2⟩, hlarge⟩
  have hOmegaReal : (Ω n : ℝ) ≤
      (7 / 5 : ℝ) * Erdos784.Analytic.logLogNat Y := le_of_not_gt hNotLarge
  have hOmega : Ω n ≤ omegaCutoff Y := by
    exact Nat.le_floor hOmegaReal
  let E : ℕ := 2 ^ omegaCutoff Y
  have hEpos : 0 < E := pow_pos (by omega) _
  have hYreal : 0 < (Y : ℝ) := by exact_mod_cast hYpos
  have hlogprod : 0 < Real.log ((ε : ℝ) ^ E * (Y : ℝ)) := by
    rw [Real.log_mul (pow_ne_zero E hε.ne') hYreal.ne', Real.log_pow]
    dsimp only [E] at hExp ⊢
    nlinarith
  have hprod : 1 < (ε : ℝ) ^ E * (Y : ℝ) := by
    apply (Real.log_pos_iff (mul_nonneg (by positivity) hYreal.le)).mp
    exact hlogprod
  have hnPow := ssGood_pow_bound hYpos hnPos hnGood hOmega
  have hnPowR : (n : ℝ) ^ E ≤ (Y : ℝ) ^ (E - 1) := by
    exact_mod_cast hnPow
  by_contra hnle
  have hnlt : ε * (Y : ℝ) < (n : ℝ) := lt_of_not_ge hnle
  have hpowlt : (ε * (Y : ℝ)) ^ E < (n : ℝ) ^ E :=
    pow_lt_pow_left₀ hnlt (mul_nonneg hε.le hYreal.le) hEpos.ne'
  have hbasePos : 0 < (Y : ℝ) ^ (E - 1) := pow_pos hYreal _
  have hupper : (Y : ℝ) ^ (E - 1) < (ε * (Y : ℝ)) ^ E := by
    calc
      (Y : ℝ) ^ (E - 1) <
          (Y : ℝ) ^ (E - 1) * ((ε : ℝ) ^ E * (Y : ℝ)) := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hprod hbasePos
      _ = (ε : ℝ) ^ E * ((Y : ℝ) ^ (E - 1) * (Y : ℝ)) := by ring
      _ = (ε : ℝ) ^ E * (Y : ℝ) ^ E := by
        rw [← pow_succ]
        congr 2
        omega
      _ = (ε * (Y : ℝ)) ^ E := (mul_pow ε (Y : ℝ) E).symm
  exact (not_lt_of_ge hnPowR) (hupper.trans hpowlt)

def ssGoodUpTo (Y : ℕ) : Finset ℕ := (Icc 1 Y).filter (ssGood Y)

lemma eventually_ssGoodUpTo_card_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ((ssGoodUpTo Y).card : ℝ) ≤ ε * (Y : ℝ) := by
  let η : ℝ := min (ε / 4) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηε : 2 * η ≤ ε := by
    have := min_le_left (ε / 4) (1 / 2)
    dsimp [η]
    linarith
  filter_upwards [Erdos784.Analytic.eventually_highOmega_card_le hη,
      eventually_lowOmega_good_le hη hη1] with Y hHigh hLow
  let lowGood := ssGoodUpTo Y \ Erdos784.Analytic.highOmega Y
  have hLowPoint : ∀ n ∈ lowGood, n ∈ Icc 1 ⌊η * (Y : ℝ)⌋₊ := by
    intro n hn
    have hn' := mem_sdiff.mp hn
    have hnGood := mem_filter.mp hn'.1
    have hnle := hLow n hnGood.1 hnGood.2 hn'.2
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnGood.1).1,
      Nat.le_floor hnle⟩
  have hLowCardNat : lowGood.card ≤ (Icc 1 ⌊η * (Y : ℝ)⌋₊).card :=
    card_le_card fun n hn => hLowPoint n hn
  have hLowCard : (lowGood.card : ℝ) ≤ η * (Y : ℝ) := by
    calc
      (lowGood.card : ℝ) ≤ ((Icc 1 ⌊η * (Y : ℝ)⌋₊).card : ℕ) := by
        exact_mod_cast hLowCardNat
      _ ≤ (⌊η * (Y : ℝ)⌋₊ : ℕ) := by
        exact_mod_cast (by simp : (Icc 1 ⌊η * (Y : ℝ)⌋₊).card ≤ ⌊η * (Y : ℝ)⌋₊)
      _ ≤ η * (Y : ℝ) := Nat.floor_le (mul_nonneg hη.le (by positivity))
  have hsub : ssGoodUpTo Y ⊆ Erdos784.Analytic.highOmega Y ∪ lowGood := by
    intro n hn
    by_cases hnh : n ∈ Erdos784.Analytic.highOmega Y
    · exact mem_union_left _ hnh
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hn, hnh⟩)
  have hcardNat : (ssGoodUpTo Y).card ≤
      (Erdos784.Analytic.highOmega Y).card + lowGood.card := by
    exact (card_le_card hsub).trans (card_union_le _ _)
  have hcard : ((ssGoodUpTo Y).card : ℝ) ≤
      (Erdos784.Analytic.highOmega Y).card + lowGood.card := by
    exact_mod_cast hcardNat
  calc
    ((ssGoodUpTo Y).card : ℝ) ≤
        (Erdos784.Analytic.highOmega Y).card + lowGood.card := hcard
    _ ≤ η * (Y : ℝ) + η * (Y : ℝ) := add_le_add hHigh hLowCard
    _ = 2 * η * (Y : ℝ) := by ring
    _ ≤ ε * (Y : ℝ) :=
      mul_le_mul_of_nonneg_right hηε (by positivity)

def ssBoundarySmallMinFac (Y K : ℕ) : Finset ℕ :=
  (ssBoundary Y).filter fun b => b.minFac ≤ K

def ssBoundaryLargeMinFac (Y K : ℕ) : Finset ℕ :=
  (ssBoundary Y).filter fun b => K < b.minFac

lemma ssBoundarySmallMinFac_card_le (Y K : ℕ) :
    (ssBoundarySmallMinFac Y K).card ≤ (Icc 2 K).card * (ssGoodUpTo Y).card := by
  let f : ℕ → ℕ × ℕ := fun b => (b.minFac, b / b.minFac)
  rw [← card_product]
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    have hb' := mem_filter.mp hb
    have hbData := mem_ssBoundary.mp hb'.1
    have hbNe : b ≠ 1 := by omega
    have hpPrime := Nat.minFac_prime hbNe
    have hpPos := hpPrime.pos
    have hmPos : 0 < b / b.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hpPos
    have hmDvd : b / b.minFac ∣ b := Nat.div_dvd_of_dvd (Nat.minFac_dvd b)
    have hmLt : b / b.minFac < b := Nat.div_lt_self (by omega) hpPrime.one_lt
    have hmGood := hbData.2.2.2 (b / b.minFac) hmDvd hmLt
    exact mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hb'.2⟩,
      mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmPos, (Nat.le_of_dvd (by omega) hmDvd).trans hbData.2.1⟩,
        hmGood⟩⟩
  · intro a ha b hb hab
    have haNe : a ≠ 1 := by
      have := (mem_ssBoundary.mp (mem_filter.mp ha).1).1
      omega
    have hbNe : b ≠ 1 := by
      have := (mem_ssBoundary.mp (mem_filter.mp hb).1).1
      omega
    have haRec : a.minFac * (a / a.minFac) = a :=
      Nat.mul_div_cancel' (Nat.minFac_dvd a)
    have hbRec : b.minFac * (b / b.minFac) = b :=
      Nat.mul_div_cancel' (Nat.minFac_dvd b)
    exact haRec ▸ hbRec ▸ congrArg (fun z : ℕ × ℕ => z.1 * z.2) hab

lemma eventually_ssBoundarySmallMinFac_card_le (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop,
      ((ssBoundarySmallMinFac Y K).card : ℝ) ≤ ε * (Y : ℝ) := by
  let d : ℝ := ((Icc 2 K).card : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hgood := eventually_ssGoodUpTo_card_le (show 0 < ε / d by positivity)
  filter_upwards [hgood] with Y hY
  have hcard := ssBoundarySmallMinFac_card_le Y K
  have hcardR : ((ssBoundarySmallMinFac Y K).card : ℝ) ≤
      ((Icc 2 K).card : ℝ) * (ssGoodUpTo Y).card := by exact_mod_cast hcard
  calc
    ((ssBoundarySmallMinFac Y K).card : ℝ) ≤
        ((Icc 2 K).card : ℝ) * (ssGoodUpTo Y).card := hcardR
    _ ≤ ((Icc 2 K).card : ℝ) * ((ε / d) * (Y : ℝ)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    _ ≤ ε * (Y : ℝ) := by
      dsimp [d]
      have hden : 0 < ((Icc 2 K).card : ℝ) + 1 := by positivity
      have hfrac : ((Icc 2 K).card : ℝ) /
          (((Icc 2 K).card : ℝ) + 1) ≤ 1 := by
        exact (div_le_one hden).2 (by linarith)
      calc
        ((Icc 2 K).card : ℝ) * ((ε / (((Icc 2 K).card : ℝ) + 1)) * (Y : ℝ)) =
            (((Icc 2 K).card : ℝ) / (((Icc 2 K).card : ℝ) + 1)) *
              (ε * (Y : ℝ)) := by ring
        _ ≤ 1 * (ε * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right hfrac (mul_nonneg hε.le (by positivity))
        _ = ε * (Y : ℝ) := one_mul _

lemma ssBoundaryLargeMinFac_coprime {Y K b : ℕ}
    (hb : b ∈ ssBoundaryLargeMinFac Y K) : (primorial K).Coprime b := by
  by_contra hcop
  obtain ⟨p, hp, hpQ, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpK : p ≤ K := hp.dvd_primorial_iff.mp hpQ
  have hminp : b.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpb
  have hKmin := (mem_filter.mp hb).2
  omega

lemma ssBoundaryLargeMinFac_card_le (Y K : ℕ) :
    (ssBoundaryLargeMinFac Y K).card ≤
      (primorial K).totient * ((Y + 1) / primorial K + 1) := by
  have hsub : ssBoundaryLargeMinFac Y K ⊆
      (Ico 0 (Y + 1)).filter fun b => (primorial K).Coprime b := by
    intro b hb
    have hbData := mem_ssBoundary.mp (mem_filter.mp hb).1
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.zero_le _, Nat.lt_succ_of_le hbData.2.1⟩,
      ssBoundaryLargeMinFac_coprime hb⟩
  calc
    (ssBoundaryLargeMinFac Y K).card ≤
        ((Ico 0 (Y + 1)).filter fun b => (primorial K).Coprime b).card :=
      card_le_card hsub
    _ ≤ (primorial K).totient * ((Y + 1) / primorial K + 1) := by
      simpa using Nat.Ico_filter_coprime_le (a := primorial K) 0 (Y + 1)
        (primorial_ne_zero K)

lemma eventually_ssBoundaryLargeMinFac_card_le (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ Y : ℕ in atTop,
      ((ssBoundaryLargeMinFac Y K).card : ℝ) ≤
        (((primorial K).totient : ℝ) / primorial K + δ) * (Y : ℝ) := by
  let Q : ℕ := primorial K
  let D : ℝ := ((Q.totient : ℝ) / Q) + Q.totient
  have hQ : 0 < Q := primorial_pos K
  obtain ⟨N : ℕ, hN⟩ := Archimedean.arch D hδ
  filter_upwards [eventually_ge_atTop N] with Y hNY
  have hD : D ≤ δ * (Y : ℝ) := by
    have hcast : (N : ℝ) ≤ Y := by exact_mod_cast hNY
    have hmul := mul_le_mul_of_nonneg_right hcast hδ.le
    have hN' : D ≤ (N : ℝ) * δ := by simpa [nsmul_eq_mul] using hN
    exact hN'.trans (by simpa [mul_comm] using hmul)
  have hcard := ssBoundaryLargeMinFac_card_le Y K
  have hcardR : ((ssBoundaryLargeMinFac Y K).card : ℝ) ≤
      (Q.totient : ℝ) * (((Y + 1) / Q : ℕ) + 1) := by
    dsimp [Q]
    exact_mod_cast hcard
  have hdiv : (((Y + 1) / Q : ℕ) : ℝ) ≤ ((Y : ℝ) + 1) / Q := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_div_le (α := ℝ) (m := Y + 1) (n := Q))
  calc
    ((ssBoundaryLargeMinFac Y K).card : ℝ) ≤
        (Q.totient : ℝ) * (((Y + 1) / Q : ℕ) + 1) := hcardR
    _ ≤ (Q.totient : ℝ) * (((Y : ℝ) + 1) / Q + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiv le_rfl) (by positivity)
    _ = ((Q.totient : ℝ) / Q) * (Y : ℝ) + D := by
      dsimp [D]
      field_simp
      ring
    _ ≤ ((Q.totient : ℝ) / Q) * (Y : ℝ) + δ * (Y : ℝ) :=
      add_le_add le_rfl hD
    _ = (((primorial K).totient : ℝ) / primorial K + δ) * (Y : ℝ) := by
      dsimp [Q]
      ring

lemma primeReciprocals_unbounded (B : ℝ) :
    ∃ K : ℕ, B < Erdos784.Analytic.primeReciprocals K := by
  by_contra hnot
  push Not at hnot
  apply not_summable_one_div_on_primes
  let f : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime} (fun n => (1 : ℝ) / n)
  apply summable_of_sum_range_le (f := f) (c := B)
  · intro n
    by_cases hn : n.Prime <;> simp [f, hn, one_div]
  · intro N
    calc
      ∑ n ∈ range N, f n ≤ ∑ n ∈ Icc 0 N, f n := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_range.mp hn).le⟩
        · intro n _hn _hnot
          by_cases hn : n.Prime <;> simp [f, hn, one_div]
      _ = Erdos784.Analytic.primeReciprocals N := by
        rw [Erdos784.Analytic.primeReciprocals_eq_sum_Icc]
        apply sum_congr rfl
        intro n _hn
        simp [f, Set.indicator, one_div]
      _ ≤ B := hnot N

lemma totient_primorial_ratio_le_exp_neg (K : ℕ) :
    ((primorial K).totient : ℝ) / primorial K ≤
      Real.exp (-Erdos784.Analytic.primeReciprocals K) := by
  let Q := primorial K
  have hQ : 0 < Q := primorial_pos K
  have hreal : (Q.totient : ℝ) = (Q : ℝ) *
      ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors Q)
  have hratio : (Q.totient : ℝ) / Q =
      ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    rw [hreal]
    field_simp
  rw [hratio, primeFactors_primorial]
  calc
    ∏ p ∈ K.primesLE, (1 - (p : ℝ)⁻¹) ≤
        ∏ p ∈ K.primesLE, Real.exp (-(p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        have hinv : (p : ℝ)⁻¹ ≤ 1 := by
          exact (inv_le_one₀ (by positivity)).2 (by linarith)
        linarith
      · intro p _hp
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (∑ p ∈ K.primesLE, -(p : ℝ)⁻¹) := by
      rw [Real.exp_sum]
    _ = Real.exp (-Erdos784.Analytic.primeReciprocals K) := by
      congr 1
      rw [Erdos784.Analytic.primeReciprocals, ← sum_neg_distrib]

lemma exists_totient_primorial_ratio_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ((primorial K).totient : ℝ) / primorial K < ε := by
  obtain ⟨K, hK⟩ := primeReciprocals_unbounded (-Real.log ε)
  refine ⟨K, (totient_primorial_ratio_le_exp_neg K).trans_lt ?_⟩
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith)

lemma eventually_ssBoundary_card_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ((ssBoundary Y).card : ℝ) ≤ ε * (Y : ℝ) := by
  obtain ⟨K, hK⟩ := exists_totient_primorial_ratio_lt
    (show 0 < ε / 4 by positivity)
  filter_upwards [eventually_ssBoundarySmallMinFac_card_le K
      (show 0 < ε / 4 by positivity),
    eventually_ssBoundaryLargeMinFac_card_le K
      (show 0 < ε / 4 by positivity)] with Y hSmall hLarge
  have hsub : ssBoundary Y ⊆
      ssBoundarySmallMinFac Y K ∪ ssBoundaryLargeMinFac Y K := by
    intro b hb
    by_cases hmin : b.minFac ≤ K
    · exact mem_union_left _ (mem_filter.mpr ⟨hb, hmin⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hb, lt_of_not_ge hmin⟩)
  have hcardNat : (ssBoundary Y).card ≤
      (ssBoundarySmallMinFac Y K).card + (ssBoundaryLargeMinFac Y K).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hcard : ((ssBoundary Y).card : ℝ) ≤
      (ssBoundarySmallMinFac Y K).card + (ssBoundaryLargeMinFac Y K).card := by
    exact_mod_cast hcardNat
  calc
    ((ssBoundary Y).card : ℝ) ≤
        (ssBoundarySmallMinFac Y K).card +
          (ssBoundaryLargeMinFac Y K).card := hcard
    _ ≤ (ε / 4) * (Y : ℝ) +
        ((((primorial K).totient : ℝ) / primorial K + ε / 4) * (Y : ℝ)) :=
      add_le_add hSmall hLarge
    _ ≤ (ε / 4) * (Y : ℝ) + ((ε / 4 + ε / 4) * (Y : ℝ)) := by
      gcongr
    _ ≤ ε * (Y : ℝ) := by
      have hY0 : 0 ≤ (Y : ℝ) := by positivity
      nlinarith

def powerScale (α : ℝ) (N : ℕ) : ℕ := ⌊Real.rpow (N : ℝ) α⌋₊

lemma eventually_powerScale_between {β α : ℝ}
    (hβ : 0 < β) (hβα : β < α) (hα1 : α < 1) :
    ∀ᶠ N : ℕ in atTop,
      Real.rpow (N : ℝ) β ≤ (powerScale α N : ℝ) ∧ powerScale α N ≤ N := by
  have hdiff : 0 < α - β := sub_pos.mpr hβα
  have hpow : Tendsto (fun N : ℕ => Real.rpow (N : ℝ) (α - β)) atTop atTop :=
    (tendsto_rpow_atTop hdiff).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpow.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with N hfactor hN1
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hxpos : 0 < (N : ℝ) := zero_lt_one.trans_le hx1
  have hxbeta : 1 ≤ Real.rpow (N : ℝ) β := by
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (N : ℝ) * β) :=
        Real.exp_le_exp.mpr (mul_nonneg (Real.log_nonneg hx1) hβ.le)
      _ = Real.rpow (N : ℝ) β := (Real.rpow_def_of_pos hxpos _).symm
  have hsplit : Real.rpow (N : ℝ) α =
      Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) (α - β) := by
    calc
      Real.rpow (N : ℝ) α = Real.rpow (N : ℝ) (β + (α - β)) := by
        congr 1
        ring
      _ = Real.rpow (N : ℝ) β * Real.rpow (N : ℝ) (α - β) :=
        Real.rpow_add hxpos _ _
  have hlower : Real.rpow (N : ℝ) β ≤ (powerScale α N : ℝ) := by
    have hgap : Real.rpow (N : ℝ) β + 1 ≤ Real.rpow (N : ℝ) α := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_left hfactor
        (Real.rpow_nonneg (zero_le_one.trans hx1) β)]
    have hfloor := Nat.sub_one_lt_floor (Real.rpow (N : ℝ) α)
    dsimp [powerScale]
    calc
      Real.rpow (N : ℝ) β ≤ Real.rpow (N : ℝ) α - 1 := by linarith
      _ ≤ (⌊Real.rpow (N : ℝ) α⌋₊ : ℕ) := hfloor.le
  have hupperR : (powerScale α N : ℝ) ≤ (N : ℝ) := by
    calc
      (powerScale α N : ℝ) ≤ Real.rpow (N : ℝ) α :=
        Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hx1) α)
      _ ≤ Real.rpow (N : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
      _ = (N : ℝ) := by norm_num
  exact ⟨hlower, by exact_mod_cast hupperR⟩

lemma eventually_primeReciprocals_powerScale_sub_le {β α η : ℝ}
    (hβ : 0 < β) (hβα : β < α) (hα1 : α < 1) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      Erdos784.Analytic.primeReciprocals N -
          Erdos784.Analytic.primeReciprocals (powerScale α N) ≤
        (Real.log 4 + 1) * (-Real.log β) + η := by
  obtain ⟨T, hT3, htail⟩ :=
    Erdos784.Analytic.primeReciprocals_sub_le_loglog (δ := (1 : ℝ)) one_pos
  have hscale := eventually_powerScale_between hβ hβα hα1
  have htlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowβ : Tendsto (fun N : ℕ => Real.rpow (N : ℝ) β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let K : ℝ := Real.log 4 + 1
  filter_upwards [hscale, hpowβ.eventually (eventually_ge_atTop T),
      htlog.eventually (eventually_ge_atTop (max 1 (K / η)))]
    with N hscaleN hpowT hlogLarge
  let Y := powerScale α N
  have hTY : T ≤ (Y : ℝ) := hpowT.trans hscaleN.1
  have hYN : Y ≤ N := hscaleN.2
  have hlogN : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans_le (le_max_left _ _ |>.trans hlogLarge)
  have hterm : K / Real.log (N : ℝ) ≤ η := by
    apply (div_le_iff₀ hlogN).2
    have hKη : K / η ≤ Real.log (N : ℝ) :=
      (le_max_right _ _).trans hlogLarge
    have := mul_le_mul_of_nonneg_right hKη hη.le
    field_simp at this ⊢
    linarith
  have hNone : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp hlogN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hNone
  have hpowPos : 0 < Real.rpow (N : ℝ) β := Real.rpow_pos_of_pos hNpos _
  have hYpos : 0 < (Y : ℝ) := hpowPos.trans_le hscaleN.1
  have hlogYlower : β * Real.log (N : ℝ) ≤ Real.log (Y : ℝ) := by
    calc
      β * Real.log (N : ℝ) = Real.log (Real.rpow (N : ℝ) β) :=
        (Real.log_rpow hNpos β).symm
      _ ≤ Real.log (Y : ℝ) := Real.log_le_log hpowPos hscaleN.1
  have hβlogPos : 0 < β * Real.log (N : ℝ) := mul_pos hβ hlogN
  have hloglogLower : Real.log β + Real.log (Real.log (N : ℝ)) ≤
      Real.log (Real.log (Y : ℝ)) := by
    calc
      Real.log β + Real.log (Real.log (N : ℝ)) =
          Real.log (β * Real.log (N : ℝ)) := by
        rw [Real.log_mul hβ.ne' hlogN.ne']
      _ ≤ Real.log (Real.log (Y : ℝ)) :=
        Real.log_le_log hβlogPos hlogYlower
  have hdiff : Real.log (Real.log (N : ℝ)) - Real.log (Real.log (Y : ℝ)) ≤
      -Real.log β := by linarith
  have hbase := htail Y N hTY hYN
  dsimp [Y, K] at hterm hbase ⊢
  calc
    Erdos784.Analytic.primeReciprocals N -
        Erdos784.Analytic.primeReciprocals (powerScale α N) ≤
      (Real.log 4 + 1) / Real.log (N : ℝ) +
        (Real.log 4 + 1) *
          (Real.log (Real.log (N : ℝ)) -
            Real.log (Real.log (powerScale α N : ℝ))) := hbase
    _ ≤ η + (Real.log 4 + 1) * (-Real.log β) := by
      exact add_le_add hterm (mul_le_mul_of_nonneg_left hdiff
        (add_nonneg (Real.log_pos (by norm_num)).le zero_le_one))
    _ = (Real.log 4 + 1) * (-Real.log β) + η := by ring

lemma exists_powerScale_ruzsaSet_eventually_admissible {C : ℝ} (hC : 1 < C) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ᶠ N : ℕ in atTop,
        Admissible C N (ruzsaSet (powerScale α N) N) := by
  let Δ : ℝ := C - 1
  let R : ℝ := Real.log 4 + 1
  let β : ℝ := Real.exp (-Δ / (8 * R))
  let α : ℝ := (1 + β) / 2
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  have hR : 0 < R := by
    dsimp [R]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hexponent : -Δ / (8 * R) < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr hΔ) (mul_pos (by norm_num) hR)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by
    dsimp [β]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hexponent
  have hα : 0 < α := by dsimp [α]; linarith
  have hβα : β < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hlogβ : Real.log β = -Δ / (8 * R) := by
    dsimp [β]
    rw [Real.log_exp]
  have htail := eventually_primeReciprocals_powerScale_sub_le
    hβ hβα hα1 (show 0 < Δ / 8 by positivity)
  have hboundary := eventually_ssBoundary_card_le
    (show 0 < Δ / 4 by positivity)
  rw [eventually_atTop] at hboundary
  obtain ⟨Y₀, hboundary⟩ := hboundary
  have hscale := eventually_powerScale_between hβ hβα hα1
  have hpowY₀ : ∀ᶠ N : ℕ in atTop, (Y₀ : ℝ) ≤ Real.rpow (N : ℝ) β :=
    ((tendsto_rpow_atTop hβ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop (Y₀ : ℝ))
  refine ⟨α, hα, hα1, ?_⟩
  filter_upwards [htail, hpowY₀, hscale, eventually_ge_atTop 1]
    with N htailN hpowY₀N hscaleN hN1
  let Y := powerScale α N
  have hYN : Y ≤ N := hscaleN.2
  have hY₀Y : Y₀ ≤ Y := by
    exact_mod_cast hpowY₀N.trans hscaleN.1
  have hboundaryN := hboundary Y hY₀Y
  have hYreal : 0 < (Y : ℝ) :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hN1) β).trans_le hscaleN.1
  have hY : 0 < Y := by exact_mod_cast hYreal
  have hcardDiv : ((ssBoundary Y).card : ℝ) / Y ≤ Δ / 4 := by
    apply (div_le_iff₀ hYreal).2
    simpa [mul_comm] using hboundaryN
  have htail' :
      Erdos784.Analytic.primeReciprocals N -
          Erdos784.Analytic.primeReciprocals Y ≤ Δ / 4 := by
    calc
      Erdos784.Analytic.primeReciprocals N -
          Erdos784.Analytic.primeReciprocals Y ≤
        R * (-Real.log β) + Δ / 8 := by
          simpa [Y, R] using htailN
      _ = Δ / 4 := by
        rw [hlogβ]
        field_simp [hR.ne']
        ring
  refine ⟨ruzsaSet_subset_Icc hYN, ?_⟩
  rw [reciprocalMass_ruzsaSet hYN]
  calc
    reciprocalMass (ssBoundary Y) +
        (Erdos784.Analytic.primeReciprocals N -
          Erdos784.Analytic.primeReciprocals Y) ≤
      (1 + ((ssBoundary Y).card : ℝ) / Y) + Δ / 4 :=
        add_le_add (ssBoundary_mass_le hY) htail'
    _ ≤ (1 + Δ / 4) + Δ / 4 := by gcongr
    _ ≤ C := by dsimp [Δ]; linarith

lemma eventually_powerScale_lt_polylog {α c K : ℝ}
    (hα1 : α < 1) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      (powerScale α N : ℝ) <
        K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c := by
  have hs : 0 < 1 - α := sub_pos.mpr hα1
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop c hs).bound (show 0 < K / 2 by positivity)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖Real.rpow (Real.log (N : ℝ)) c‖ ≤
        (K / 2) * ‖Real.rpow (N : ℝ) (1 - α)‖ :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hbound hN2
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogpow : 0 < Real.rpow (Real.log (N : ℝ)) c :=
    Real.rpow_pos_of_pos hlog _
  have hpowNonneg : 0 ≤ Real.rpow (N : ℝ) (1 - α) :=
    Real.rpow_nonneg hNpos.le _
  have hbound' : Real.rpow (Real.log (N : ℝ)) c ≤
      (K / 2) * Real.rpow (N : ℝ) (1 - α) := by
    rw [Real.norm_eq_abs, abs_of_pos hlogpow, Real.norm_eq_abs,
      abs_of_nonneg hpowNonneg] at hbound
    exact hbound
  have hfloor : (powerScale α N : ℝ) ≤ Real.rpow (N : ℝ) α :=
    Nat.floor_le (Real.rpow_nonneg hNpos.le _)
  apply (lt_div_iff₀ hlogpow).2
  calc
    (powerScale α N : ℝ) * Real.rpow (Real.log (N : ℝ)) c ≤
        Real.rpow (N : ℝ) α * Real.rpow (Real.log (N : ℝ)) c :=
      mul_le_mul_of_nonneg_right hfloor hlogpow.le
    _ ≤ Real.rpow (N : ℝ) α *
        ((K / 2) * Real.rpow (N : ℝ) (1 - α)) :=
      mul_le_mul_of_nonneg_left hbound' (Real.rpow_nonneg hNpos.le _)
    _ = (K / 2) * (N : ℝ) := by
      calc
        Real.rpow (N : ℝ) α *
            ((K / 2) * Real.rpow (N : ℝ) (1 - α)) =
          (K / 2) * (Real.rpow (N : ℝ) α *
            Real.rpow (N : ℝ) (1 - α)) := by ring
        _ = (K / 2) * Real.rpow (N : ℝ) (α + (1 - α)) := by
          exact congrArg (fun z : ℝ => (K / 2) * z)
            (Real.rpow_add hNpos α (1 - α)).symm
        _ = (K / 2) * (N : ℝ) := by norm_num
    _ < K * (N : ℝ) := by nlinarith

theorem not_correctedAnswer_of_one_lt {C : ℝ} (hC : 1 < C) :
    ¬CorrectedAnswer C := by
  rintro ⟨c, K, hc, hK, N₀, hBound⟩
  obtain ⟨α, hα, hα1, hAdmissible⟩ :=
    exists_powerScale_ruzsaSet_eventually_admissible hC
  have hSmall := eventually_powerScale_lt_polylog (c := c) (K := K) hα1 hK
  have hScale := eventually_powerScale_between
    (show 0 < α / 2 by positivity) (show α / 2 < α by linarith) hα1
  have hFalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hAdmissible, hSmall, hScale, eventually_ge_atTop N₀,
        eventually_ge_atTop 1]
      with N hAdm hSmallN hScaleN hN₀ hN1
    let Y := powerScale α N
    let A := ruzsaSet Y N
    have hYreal : 0 < (Y : ℝ) :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hN1) (α / 2)).trans_le hScaleN.1
    have hY : 0 < Y := by exact_mod_cast hYreal
    have hLower := hBound N hN₀ A (by simpa [A, Y] using hAdm)
    have hUpperNat : (unsieved N A).card ≤ Y := by
      simpa [A] using ruzsaSet_survivors_le (N := N) hY
    have hUpper : ((unsieved N A).card : ℝ) ≤ Y := by exact_mod_cast hUpperNat
    have hScaleLess : (Y : ℝ) <
        K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c := by
      simpa [Y] using hSmallN
    exact (not_lt_of_ge (hLower.trans hUpper)) hScaleLess
  rw [eventually_atTop] at hFalse
  obtain ⟨M, hM⟩ := hFalse
  exact hM M le_rfl

/-- Complete resolution of the customary corrected problem: the requested
polylogarithmic lower bound holds exactly for `0 < C ≤ 1`. -/
theorem erdos_784_corrected {C : ℝ} (hC : 0 < C) :
    CorrectedAnswer C ↔ C ≤ 1 := by
  constructor
  · intro hAnswer
    by_contra hNot
    exact not_correctedAnswer_of_one_lt (lt_of_not_ge hNot) hAnswer
  · exact correctedAnswer_of_pos_of_le_one hC


/-! ## The literal obstruction at reciprocal mass one -/

lemma singleton_one_literalAdmissible {C : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hN : 1 ≤ N) : LiteralAdmissible C N {1} := by
  constructor
  · simpa using hN
  · simpa [reciprocalMass] using hC

@[simp] lemma unsieved_singleton_one (N : ℕ) : unsieved N {1} = ∅ := by
  ext n
  simp [unsieved]

theorem not_literalAnswer_of_one_le {C : ℝ} (hC : 1 ≤ C) :
    ¬LiteralAnswer C := by
  rintro ⟨c, K, hc, hK, N₀, hBound⟩
  let N := max N₀ logarithmicThreshold
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hN3 : logarithmicThreshold ≤ N := le_max_right _ _
  have hN1 : 1 ≤ N := logarithmicThreshold_pos.trans_le hN3
  have hApply := hBound N hN₀ {1} (singleton_one_literalAdmissible hC hN1)
  rw [unsieved_singleton_one] at hApply
  have hlog : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans_le (one_le_log_nat hN3)
  have hRight :
      0 < K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c := by
    exact div_pos (mul_pos hK (by positivity)) (Real.rpow_pos_of_pos hlog c)
  norm_num at hApply
  exact (not_lt_of_ge hApply) hRight

/-- Complete resolution of Problem 784 exactly as printed: for a positive
budget the proposed lower bound holds precisely below reciprocal mass one. -/
theorem erdos_784 {C : ℝ} (_hC : 0 < C) :
    LiteralAnswer C ↔ C < 1 := by
  constructor
  · intro h
    by_contra hNot
    exact not_literalAnswer_of_one_le (le_of_not_gt hNot) h
  · exact literalAnswer_of_lt_one

end

end Erdos784

#print axioms Erdos784.erdos_784
#print axioms Erdos784.erdos_784_corrected
#print axioms Erdos784.correctedAnswer_one

alias _root_.Erdos784.erdos_784_literal := _root_.Erdos784.erdos_784

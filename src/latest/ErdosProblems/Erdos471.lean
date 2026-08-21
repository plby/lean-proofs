/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib
import ErdosProblems.Erdos471.AnalyticConclusion

/-!
# Erdős Problem 471

Starting from a finite set of primes, repeatedly adjoin every prime that is
the sum of three distinct elements already present.  This file formalizes the
exact closure operation and the reduction of the affirmative answer to the
distinct-summand form of Vinogradov's three-primes theorem.
-/

namespace Erdos471

/-- Three natural numbers are pairwise distinct. -/
def PairwiseDistinct3 (a b c : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c

instance (a b c : ℕ) : Decidable (PairwiseDistinct3 a b c) := by
  unfold PairwiseDistinct3
  infer_instance

/-- The sums of ordered triples of distinct elements of `Q`.  Taking an image
removes the irrelevant ordering and any duplicate sums. -/
def tripleSums (Q : Finset ℕ) : Finset ℕ :=
  ((((Q ×ˢ Q) ×ˢ Q).filter fun t : (ℕ × ℕ) × ℕ ↦
      PairwiseDistinct3 t.1.1 t.1.2 t.2).image fun t ↦
        t.1.1 + t.1.2 + t.2)

/-- The prime-valued sums of three distinct elements of `Q`. -/
def newPrimes (Q : Finset ℕ) : Finset ℕ :=
  (tripleSums Q).filter Nat.Prime

/-- One exact step of the process in Erdős Problem 471. -/
def step (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ newPrimes Q

/-- The generations of the closure process, starting at generation zero. -/
def generation (Q : Finset ℕ) : ℕ → Finset ℕ
  | 0 => Q
  | i + 1 => step (generation Q i)

/-- Every member of a finset is prime. -/
def IsPrimeFinset (Q : Finset ℕ) : Prop :=
  ∀ p ∈ Q, Nat.Prime p

/-- The cardinalities of the generations are unbounded. -/
def HasUnboundedGenerations (Q : Finset ℕ) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ, k ≤ (generation Q i).card

/-- The exact distinct-summand consequence of Vinogradov's three-primes
theorem needed for Erdős Problem 471. -/
def DistinctTernaryGoldbachEventually : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
    ∃ a b c : ℕ,
      Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧
        PairwiseDistinct3 a b c ∧ n = a + b + c

/-- Ordered triples of primes whose sum is `n`.  The range bounds make this a
finite object while imposing no mathematical restriction on a representation. -/
def primeTripleRepresentations (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) ×ˢ
      (Finset.range (n + 1))).filter fun t : (ℕ × ℕ) × ℕ ↦
        Nat.Prime t.1.1 ∧ Nat.Prime t.1.2 ∧ Nat.Prime t.2 ∧
          t.1.1 + t.1.2 + t.2 = n)

/-- Representations with a repeated coordinate. -/
def repeatedPrimeTripleRepresentations (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (primeTripleRepresentations n).filter fun t ↦
    ¬ PairwiseDistinct3 t.1.1 t.1.2 t.2

/-- The quantitative form of ternary Vinogradov needed to force distinct
summands: eventually there are more representations than all possible
coordinate diagonals combined. -/
def TernaryPrimeCountEventuallyLarge : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
    3 * (n + 1) < (primeTripleRepresentations n).card

/-- The logarithmically weighted count of ordered prime triples summing to
`n`.  This is the prime-only quantity naturally produced by the circle
method after prime-power terms have been removed. -/
noncomputable def primeTripleLogWeight (n : ℕ) : ℝ :=
  ∑ t ∈ primeTripleRepresentations n,
    Real.log (t.1.1 : ℝ) * Real.log (t.1.2 : ℝ) * Real.log (t.2 : ℝ)

/-- A qualitative Hardy--Littlewood lower bound, with an unspecified positive
constant, is enough for Problem 471. -/
def WeightedTernaryPrimeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
    c * (n : ℝ) ^ 2 ≤ primeTripleLogWeight n

/-- The circle-method form of the large-odd estimate, before removing proper
prime powers from the von Mangoldt weight. -/
def VonMangoldtTernaryLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
    c * (n : ℝ) ^ 2 ≤ PrimePowerTail.vonMangoldtTripleWeight n

/-- The major/minor-arc argument supplies the von Mangoldt lower bound
without any remaining hypothesis. -/
theorem vonMangoldtTernaryLowerBound : VonMangoldtTernaryLowerBound := by
  obtain ⟨c, hc, hlarge⟩ := Analytic.eventually_vonMangoldtTripleWeight_lower
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨c, hc, N, ?_⟩
  intro n hn hodd
  exact hN n (Nat.le_of_lt hn) hodd

private theorem vonMangoldt_eq_primeLog_of_not_properPrimePower
    (m : ℕ) (hnot : ¬ PrimePowerTail.ProperPrimePower m) :
    ArithmeticFunction.vonMangoldt m =
      if m.Prime then Real.log (m : ℝ) else 0 := by
  by_cases hp : m.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rw [if_neg hp]
    apply not_ne_iff.mp
    intro hne
    exact hnot ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne, hp⟩

/-- Removing every proper-prime-power coordinate leaves exactly the prime-log
weighted triple count (up to the harmless reassociation of products). -/
theorem primeOnlyWeightedContribution_eq_primeTripleLogWeight (n : ℕ) :
    PrimePowerTail.primeOnlyWeightedContribution n = primeTripleLogWeight n := by
  classical
  unfold PrimePowerTail.primeOnlyWeightedContribution
    PrimePowerTail.primeOnlyWeightedTriples PrimePowerTail.weightedTriples
    primeTripleLogWeight primeTripleRepresentations
  simp_rw [Finset.sum_filter]
  simp_rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ha ↦ ?_
  refine Finset.sum_congr rfl fun b _hb ↦ ?_
  refine Finset.sum_congr rfl fun c _hc ↦ ?_
  by_cases hsum : a + b + c = n
  · simp only [hsum, if_true]
    by_cases hnot : ¬ PrimePowerTail.HasProperPrimePowerComponent (a, b, c)
    · have hparts := PrimePowerTail.not_hasProperPrimePowerComponent_iff.mp hnot
      rw [if_pos hnot,
        vonMangoldt_eq_primeLog_of_not_properPrimePower a hparts.1,
        vonMangoldt_eq_primeLog_of_not_properPrimePower b hparts.2.1,
        vonMangoldt_eq_primeLog_of_not_properPrimePower c hparts.2.2]
      by_cases ha : a.Prime <;> by_cases hb : b.Prime <;> by_cases hc : c.Prime <;>
        simp [ha, hb, hc]
    · rw [if_neg hnot]
      push_neg at hnot
      rcases hnot with h | h | h
      · have ha : ¬a.Prime := h.2
        simp [ha]
      · have hb : ¬b.Prime := h.2
        simp [hb]
      · have hc : ¬c.Prime := h.2
        simp [hc]
  · simp [hsum]

/-- The elementary prime-power tail is negligible compared with a positive
quadratic von Mangoldt lower bound. -/
theorem weightedTernaryPrimeLowerBound_of_vonMangoldt
    (hvm : VonMangoldtTernaryLowerBound) :
    WeightedTernaryPrimeLowerBound := by
  rcases hvm with ⟨c, hc, Nv, hNv⟩
  obtain ⟨Nt, hNt⟩ := Filter.eventually_atTop.mp
    (PrimePowerTail.eventually_tail_le_eps_sq (show 0 < c / 2 by positivity))
  refine ⟨c / 2, by positivity, max Nv Nt, ?_⟩
  intro n hn hodd
  have hNv' : Nv < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hNt' : Nt ≤ n := le_trans (le_max_right _ _) (Nat.le_of_lt hn)
  have hlower := hNv n hNv' hodd
  have htail := hNt n hNt'
  have hsplit := PrimePowerTail.vonMangoldtTripleWeight_split n
  rw [primeOnlyWeightedContribution_eq_primeTripleLogWeight] at hsplit
  nlinarith [sq_nonneg (n : ℝ)]

theorem rawPrimeTripleLogWeight_self (n : ℕ) :
    CircleMethod.rawPrimeTripleLogWeight n n = primeTripleLogWeight n := by
  classical
  unfold CircleMethod.rawPrimeTripleLogWeight primeTripleLogWeight
    primeTripleRepresentations
  simp_rw [Finset.sum_filter]
  simp_rw [Finset.sum_product]
  simp_rw [Finset.sum_filter]
  simp [ite_and]

/-- The weighted prime-triple count is exactly the `n`th Fourier coefficient
of the cube of the weighted prime exponential sum. -/
theorem primeTripleLogWeight_eq_circleIntegral (n : ℕ) :
    (primeTripleLogWeight n : ℂ) =
      ∫ α in Set.Icc (0 : ℝ) 1,
        (CircleMethod.primeLogExpSum α n) ^ 3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
  rw [CircleMethod.integral_primeLogExpSum_cube_kernel,
    rawPrimeTripleLogWeight_self]

theorem mem_primeTripleRepresentations {n a b c : ℕ} :
    ((a, b), c) ∈ primeTripleRepresentations n ↔
      Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧ a + b + c = n := by
  rw [primeTripleRepresentations, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Finset.mem_product]
    have ha : a ≤ n := by
      have := h.1.pos
      omega
    have hb : b ≤ n := by
      have := h.2.1.pos
      omega
    have hc : c ≤ n := by
      have := h.2.2.1.pos
      omega
    simp only [Finset.mem_range]
    omega

/-- Every summand in the prime-only weighted count is at most `log(n)^3`. -/
theorem primeTripleLogWeight_le (n : ℕ) :
    primeTripleLogWeight n ≤
      (primeTripleRepresentations n).card * Real.log (n : ℝ) ^ 3 := by
  classical
  unfold primeTripleLogWeight
  calc
    (∑ t ∈ primeTripleRepresentations n,
        Real.log (t.1.1 : ℝ) * Real.log (t.1.2 : ℝ) * Real.log (t.2 : ℝ)) ≤
        ∑ _t ∈ primeTripleRepresentations n, Real.log (n : ℝ) ^ 3 := by
      refine Finset.sum_le_sum fun t ht ↦ ?_
      rcases t with ⟨⟨a, b⟩, c⟩
      have hrep := mem_primeTripleRepresentations.mp ht
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      have ha_le : a ≤ n := by omega
      have hb_le : b ≤ n := by omega
      have hc_le : c ≤ n := by omega
      have hla0 : 0 ≤ Real.log (a : ℝ) :=
        Real.log_nonneg (by exact_mod_cast ha.one_le)
      have hlb0 : 0 ≤ Real.log (b : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hb.one_le)
      have hlc0 : 0 ≤ Real.log (c : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hc.one_le)
      have hla : Real.log (a : ℝ) ≤ Real.log (n : ℝ) := by
        exact Real.log_le_log (by exact_mod_cast ha.pos) (by exact_mod_cast ha_le)
      have hlb : Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
        exact Real.log_le_log (by exact_mod_cast hb.pos) (by exact_mod_cast hb_le)
      have hlc : Real.log (c : ℝ) ≤ Real.log (n : ℝ) := by
        exact Real.log_le_log (by exact_mod_cast hc.pos) (by exact_mod_cast hc_le)
      calc
        Real.log (a : ℝ) * Real.log (b : ℝ) * Real.log (c : ℝ) ≤
            Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
          gcongr
        _ = Real.log (n : ℝ) ^ 3 := by ring
    _ = (primeTripleRepresentations n).card * Real.log (n : ℝ) ^ 3 := by
      simp [nsmul_eq_mul]

/-- A fixed positive multiple of `n^2` eventually dominates the diagonal
scale `3(n+1) log(n)^3`. -/
theorem eventually_diagonal_log_weight_lt_square {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      3 * ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3 < c * (n : ℝ) ^ 2 := by
  have hsmall :=
    ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).natCast_atTop).bound
      (by positivity : (0 : ℝ) < c / 7)
  filter_upwards [hsmall, Filter.eventually_ge_atTop 2] with n hnsmall hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hs : Real.log (n : ℝ) ^ 3 ≤ (c / 7) * (n : ℝ) := by
    simpa [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg hlog0, abs_of_pos hnpos] using hnsmall
  have hmul : (n : ℝ) * Real.log (n : ℝ) ^ 3 ≤
      (n : ℝ) * ((c / 7) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hs hnpos.le
  have hnadd : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    norm_num
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hlog3 : 0 ≤ Real.log (n : ℝ) ^ 3 := by positivity
  calc
    3 * ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3 ≤
        6 * (n : ℝ) * Real.log (n : ℝ) ^ 3 := by
      nlinarith
    _ ≤ 6 * ((n : ℝ) * ((c / 7) * (n : ℝ))) := by
      nlinarith
    _ < c * (n : ℝ) ^ 2 := by
      nlinarith [sq_pos_of_pos hnpos]

/-- The Hardy--Littlewood weighted lower bound implies the representation
count needed to eliminate all three coordinate diagonals. -/
theorem ternaryPrimeCountEventuallyLarge_of_weightedLowerBound
    (hweighted : WeightedTernaryPrimeLowerBound) :
    TernaryPrimeCountEventuallyLarge := by
  rcases hweighted with ⟨c, hc, Nw, hNw⟩
  obtain ⟨Ng, hNg⟩ := Filter.eventually_atTop.mp
    (eventually_diagonal_log_weight_lt_square hc)
  refine ⟨max Nw (max Ng 1), ?_⟩
  intro n hn hodd
  have hnNw : Nw < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnNg : Ng ≤ n := le_trans
    ((le_max_left Ng 1).trans (le_max_right Nw (max Ng 1))) (Nat.le_of_lt hn)
  have hn2 : 2 ≤ n := by
    have : 1 < n := lt_of_le_of_lt
      ((le_max_right Ng 1).trans (le_max_right Nw (max Ng 1))) hn
    omega
  have hlower := hNw n hnNw hodd
  have hdiag := hNg n hnNg
  have hupper := primeTripleLogWeight_le n
  by_contra hcard
  have hcard' : (primeTripleRepresentations n).card ≤ 3 * (n + 1) := by omega
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hcardReal : ((primeTripleRepresentations n).card : ℝ) ≤
      3 * ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard'
  have hcountWeight :
      (primeTripleRepresentations n).card * Real.log (n : ℝ) ^ 3 ≤
        3 * ((n + 1 : ℕ) : ℝ) * Real.log (n : ℝ) ^ 3 := by
    exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
  linarith

private def repeatedAB (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (primeTripleRepresentations n).filter fun t ↦ t.1.1 = t.1.2

private def repeatedAC (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (primeTripleRepresentations n).filter fun t ↦ t.1.1 = t.2

private def repeatedBC (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (primeTripleRepresentations n).filter fun t ↦ t.1.2 = t.2

private theorem repeatedAB_card_le (n : ℕ) :
    (repeatedAB n).card ≤ n + 1 := by
  have hcard : (repeatedAB n).card ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t : (ℕ × ℕ) × ℕ ↦ t.1.1) ?_ ?_
    · intro t ht
      rcases t with ⟨⟨a, b⟩, c⟩
      have htF : ((a, b), c) ∈ repeatedAB n := ht
      have ht' := Finset.mem_filter.mp htF
      have hrep := (mem_primeTripleRepresentations.mp ht'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      simpa using (show a < n + 1 by omega)
    · rintro ⟨⟨a, b⟩, c⟩ ht ⟨⟨a', b'⟩, c'⟩ ht' haa'
      have htF : ((a, b), c) ∈ repeatedAB n := ht
      have htF' : ((a', b'), c') ∈ repeatedAB n := ht'
      have htParts := Finset.mem_filter.mp htF
      have htParts' := Finset.mem_filter.mp htF'
      have hrep := (mem_primeTripleRepresentations.mp htParts.1)
      have hrep' := (mem_primeTripleRepresentations.mp htParts'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      rcases hrep' with ⟨ha', hb', hc', hsum'⟩
      have hab : a = b := by simpa using htParts.2
      have hab' : a' = b' := by simpa using htParts'.2
      have haa : a = a' := by simpa using haa'
      have hcc : c = c' := by omega
      subst b
      subst b'
      subst a'
      subst c'
      rfl
  simpa using hcard

private theorem repeatedAC_card_le (n : ℕ) :
    (repeatedAC n).card ≤ n + 1 := by
  have hcard : (repeatedAC n).card ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t : (ℕ × ℕ) × ℕ ↦ t.1.1) ?_ ?_
    · intro t ht
      rcases t with ⟨⟨a, b⟩, c⟩
      have htF : ((a, b), c) ∈ repeatedAC n := ht
      have ht' := Finset.mem_filter.mp htF
      have hrep := (mem_primeTripleRepresentations.mp ht'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      simpa using (show a < n + 1 by omega)
    · rintro ⟨⟨a, b⟩, c⟩ ht ⟨⟨a', b'⟩, c'⟩ ht' haa'
      have htF : ((a, b), c) ∈ repeatedAC n := ht
      have htF' : ((a', b'), c') ∈ repeatedAC n := ht'
      have htParts := Finset.mem_filter.mp htF
      have htParts' := Finset.mem_filter.mp htF'
      have hrep := (mem_primeTripleRepresentations.mp htParts.1)
      have hrep' := (mem_primeTripleRepresentations.mp htParts'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      rcases hrep' with ⟨ha', hb', hc', hsum'⟩
      have hac : a = c := by simpa using htParts.2
      have hac' : a' = c' := by simpa using htParts'.2
      have haa : a = a' := by simpa using haa'
      have hbb : b = b' := by omega
      subst c
      subst c'
      subst a'
      subst b'
      rfl
  simpa using hcard

private theorem repeatedBC_card_le (n : ℕ) :
    (repeatedBC n).card ≤ n + 1 := by
  have hcard : (repeatedBC n).card ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t : (ℕ × ℕ) × ℕ ↦ t.1.2) ?_ ?_
    · intro t ht
      rcases t with ⟨⟨a, b⟩, c⟩
      have htF : ((a, b), c) ∈ repeatedBC n := ht
      have ht' := Finset.mem_filter.mp htF
      have hrep := (mem_primeTripleRepresentations.mp ht'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      simpa using (show b < n + 1 by omega)
    · rintro ⟨⟨a, b⟩, c⟩ ht ⟨⟨a', b'⟩, c'⟩ ht' hbb'
      have htF : ((a, b), c) ∈ repeatedBC n := ht
      have htF' : ((a', b'), c') ∈ repeatedBC n := ht'
      have htParts := Finset.mem_filter.mp htF
      have htParts' := Finset.mem_filter.mp htF'
      have hrep := (mem_primeTripleRepresentations.mp htParts.1)
      have hrep' := (mem_primeTripleRepresentations.mp htParts'.1)
      rcases hrep with ⟨ha, hb, hc, hsum⟩
      rcases hrep' with ⟨ha', hb', hc', hsum'⟩
      have hbc : b = c := by simpa using htParts.2
      have hbc' : b' = c' := by simpa using htParts'.2
      have hbb : b = b' := by simpa using hbb'
      have haa : a = a' := by omega
      subst c
      subst c'
      subst b'
      subst a'
      rfl
  simpa using hcard

/-- At most `3(n+1)` ordered prime representations of `n` have a repeated
coordinate.  Each of the three diagonals injects into one coordinate. -/
theorem repeatedPrimeTripleRepresentations_card_le (n : ℕ) :
    (repeatedPrimeTripleRepresentations n).card ≤ 3 * (n + 1) := by
  have hsub : repeatedPrimeTripleRepresentations n ⊆
      repeatedAB n ∪ repeatedAC n ∪ repeatedBC n := by
    intro t ht
    rcases t with ⟨⟨a, b⟩, c⟩
    simp only [repeatedPrimeTripleRepresentations, Finset.mem_filter] at ht
    simp only [Finset.mem_union, repeatedAB, repeatedAC, repeatedBC,
      Finset.mem_filter, ht.1, true_and]
    simp only [PairwiseDistinct3] at ht
    tauto
  have hunion : (repeatedAB n ∪ repeatedAC n ∪ repeatedBC n).card ≤
      (repeatedAB n).card + (repeatedAC n).card + (repeatedBC n).card := by
    calc
      ((repeatedAB n ∪ repeatedAC n) ∪ repeatedBC n).card ≤
          (repeatedAB n ∪ repeatedAC n).card + (repeatedBC n).card :=
        Finset.card_union_le _ _
      _ ≤ ((repeatedAB n).card + (repeatedAC n).card) +
          (repeatedBC n).card :=
        Nat.add_le_add_right
          (Finset.card_union_le (repeatedAB n) (repeatedAC n)) _
  exact (Finset.card_le_card hsub).trans <| hunion.trans <| by
    have hab := repeatedAB_card_le n
    have hac := repeatedAC_card_le n
    have hbc := repeatedBC_card_le n
    omega

/-- More than the diagonal bound forces a pairwise-distinct prime triple. -/
theorem exists_distinct_prime_triple_of_count_large {n : ℕ}
    (hcount : 3 * (n + 1) < (primeTripleRepresentations n).card) :
    ∃ a b c : ℕ,
      Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧
        PairwiseDistinct3 a b c ∧ n = a + b + c := by
  classical
  by_contra hnone
  have hsub : primeTripleRepresentations n ⊆
      repeatedPrimeTripleRepresentations n := by
    intro t ht
    rcases t with ⟨⟨a, b⟩, c⟩
    rw [repeatedPrimeTripleRepresentations, Finset.mem_filter]
    refine ⟨ht, ?_⟩
    have hrep := mem_primeTripleRepresentations.mp ht
    intro hdistinct
    apply hnone
    exact ⟨a, b, c, hrep.1, hrep.2.1, hrep.2.2.1, hdistinct, by omega⟩
  have := (Finset.card_le_card hsub).trans
    (repeatedPrimeTripleRepresentations_card_le n)
  omega

theorem distinctTernaryGoldbachEventually_of_count_large
    (hcount : TernaryPrimeCountEventuallyLarge) :
    DistinctTernaryGoldbachEventually := by
  rcases hcount with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact exists_distinct_prime_triple_of_count_large (hN n hn hodd)

theorem mem_tripleSums {Q : Finset ℕ} {p : ℕ} :
    p ∈ tripleSums Q ↔
      ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
        PairwiseDistinct3 a b c ∧ p = a + b + c := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩
    rcases Finset.mem_filter.mp habc with ⟨habcQ, hdistinct⟩
    rcases Finset.mem_product.mp habcQ with ⟨habQ, hcQ⟩
    rcases Finset.mem_product.mp habQ with ⟨haQ, hbQ⟩
    exact ⟨a, haQ, b, hbQ, c, hcQ, hdistinct, rfl⟩
  · rintro ⟨a, haQ, b, hbQ, c, hcQ, hdistinct, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨⟨a, b⟩, c⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨haQ, hbQ⟩, hcQ⟩, hdistinct⟩

theorem mem_newPrimes {Q : Finset ℕ} {p : ℕ} :
    p ∈ newPrimes Q ↔
      Nat.Prime p ∧
        ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
          PairwiseDistinct3 a b c ∧ p = a + b + c := by
  rw [newPrimes, Finset.mem_filter, mem_tripleSums]
  constructor
  · rintro ⟨hsum, hp⟩
    exact ⟨hp, hsum⟩
  · rintro ⟨hp, hsum⟩
    exact ⟨hsum, hp⟩

/-- Membership in a successor generation is exactly membership in the old
generation or being a prime sum of three distinct old elements. -/
theorem mem_step {Q : Finset ℕ} {p : ℕ} :
    p ∈ step Q ↔
      p ∈ Q ∨
        Nat.Prime p ∧
          ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
            PairwiseDistinct3 a b c ∧ p = a + b + c := by
  rw [step, Finset.mem_union, mem_newPrimes]

theorem subset_step (Q : Finset ℕ) : Q ⊆ step Q := by
  exact Finset.subset_union_left

theorem generation_subset_succ (Q : Finset ℕ) (i : ℕ) :
    generation Q i ⊆ generation Q (i + 1) := by
  simpa only [generation] using subset_step (generation Q i)

/-- Once an element occurs, it persists at every later generation. -/
theorem generation_mono (Q : Finset ℕ) {i j : ℕ} (hij : i ≤ j) :
    generation Q i ⊆ generation Q j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j _ ih => exact ih.trans (generation_subset_succ Q j)

theorem isPrimeFinset_step {Q : Finset ℕ} (hQ : IsPrimeFinset Q) :
    IsPrimeFinset (step Q) := by
  intro p hp
  rcases (mem_step.mp hp) with hpQ | hpnew
  · exact hQ p hpQ
  · exact hpnew.1

theorem isPrimeFinset_generation {Q : Finset ℕ} (hQ : IsPrimeFinset Q) :
    ∀ i : ℕ, IsPrimeFinset (generation Q i)
  | 0 => hQ
  | i + 1 => isPrimeFinset_step (isPrimeFinset_generation hQ i)

theorem isPrimeFinset_primesLE (N : ℕ) :
    IsPrimeFinset (Nat.primesLE N) := by
  intro p hp
  exact (Nat.mem_primesLE.mp hp).2

/-- Assuming the precise distinct Vinogradov input, a finite initial segment
of the primes eventually generates every prime. -/
theorem exists_primeFinset_all_primes_reachable
    (hV : DistinctTernaryGoldbachEventually) :
    ∃ Q : Finset ℕ,
      IsPrimeFinset Q ∧
        ∀ p : ℕ, Nat.Prime p → ∃ i : ℕ, p ∈ generation Q i := by
  rcases hV with ⟨NV, hV⟩
  let N := max NV 2
  let Q := Nat.primesLE N
  refine ⟨Q, isPrimeFinset_primesLE N, ?_⟩
  intro p hp
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases hpN : p ≤ N
      · refine ⟨0, ?_⟩
        exact Nat.mem_primesLE.mpr ⟨hpN, hp⟩
      · have hNp : N < p := Nat.lt_of_not_ge hpN
        have hNVp : NV < p := lt_of_le_of_lt (le_max_left NV 2) hNp
        have hp_ne_two : p ≠ 2 := by omega
        have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
        rcases hV p hNVp hp_odd with
          ⟨a, b, c, ha, hb, hc, hdistinct, hp_sum⟩
        have ha_lt : a < p := by
          have hbpos := hb.pos
          have hcpos := hc.pos
          omega
        have hb_lt : b < p := by
          have hapos := ha.pos
          have hcpos := hc.pos
          omega
        have hc_lt : c < p := by
          have hapos := ha.pos
          have hbpos := hb.pos
          omega
        obtain ⟨ia, hia⟩ := ih a ha_lt ha
        obtain ⟨ib, hib⟩ := ih b hb_lt hb
        obtain ⟨ic, hic⟩ := ih c hc_lt hc
        let j := max ia (max ib ic)
        have hia' : a ∈ generation Q j :=
          generation_mono Q (le_max_left ia (max ib ic)) hia
        have hib' : b ∈ generation Q j :=
          generation_mono Q ((le_max_left ib ic).trans (le_max_right ia (max ib ic))) hib
        have hic' : c ∈ generation Q j :=
          generation_mono Q ((le_max_right ib ic).trans (le_max_right ia (max ib ic))) hic
        refine ⟨j + 1, ?_⟩
        rw [generation]
        apply mem_step.mpr
        exact Or.inr ⟨hp, a, hia', b, hib', c, hic', hdistinct, hp_sum⟩

/-- A finite collection of individually reachable numbers can be synchronized
at one generation. -/
theorem finite_subset_eventually_mem {Q F : Finset ℕ}
    (hreach : ∀ p ∈ F, ∃ i : ℕ, p ∈ generation Q i) :
    ∃ j : ℕ, F ⊆ generation Q j := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p F hp ih =>
      obtain ⟨i, hi⟩ := hreach p (by simp)
      obtain ⟨j, hj⟩ := ih (fun q hq ↦ hreach q (Finset.mem_insert_of_mem hq))
      refine ⟨max i j, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact generation_mono Q (le_max_left i j) hi
      · exact generation_mono Q (le_max_right i j) (hj hq)

/-- The complete elementary reduction from distinct ternary Vinogradov to
the affirmative answer to Erdős Problem 471. -/
theorem erdos471_of_distinctTernaryGoldbachEventually
    (hV : DistinctTernaryGoldbachEventually) :
    ∃ Q : Finset ℕ, IsPrimeFinset Q ∧ HasUnboundedGenerations Q := by
  classical
  obtain ⟨Q, hQprime, hreach⟩ :=
    exists_primeFinset_all_primes_reachable hV
  refine ⟨Q, hQprime, ?_⟩
  intro k
  obtain ⟨F, hFprime, hFcard⟩ :=
    Nat.infinite_setOfPred_prime.exists_subset_card_eq k
  obtain ⟨j, hFj⟩ := finite_subset_eventually_mem (Q := Q) (F := F) (by
    intro p hp
    exact hreach p (hFprime hp))
  refine ⟨j, ?_⟩
  simpa [hFcard] using Finset.card_le_card hFj

/-- Erdős Problem 471 has an affirmative answer: a finite set of primes can
be chosen whose generations have arbitrarily large cardinality. -/
theorem erdos471 :
    ∃ Q : Finset ℕ, IsPrimeFinset Q ∧ HasUnboundedGenerations Q := by
  apply erdos471_of_distinctTernaryGoldbachEventually
  apply distinctTernaryGoldbachEventually_of_count_large
  apply ternaryPrimeCountEventuallyLarge_of_weightedLowerBound
  exact weightedTernaryPrimeLowerBound_of_vonMangoldt
    vonMangoldtTernaryLowerBound

#print axioms erdos471

end Erdos471

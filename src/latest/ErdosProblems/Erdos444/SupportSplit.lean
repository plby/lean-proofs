/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos444.ManyPrimes
import ErdosProblems.Erdos444.Moment
import ErdosProblems.Erdos444.RepeatedPrimes
import ErdosProblems.Erdos697.Erdos697PrimeWindow

/-!
# Splitting a product-representation support

Every represented integer is divisible by the product of one tuple from the
chosen finite set.  If every tuple entry has at least `t` distinct prime
factors above `y`, the represented integer therefore has at least `r * t`
such factors counted with multiplicity.  When the entries are at most `X`,
all of these factors lie in the prime window `(y, X]`.

The main theorem splits the representation support into the repeated-prime
exceptional set and the set of integers divisible by many distinct primes
from that window.  It is an exact finite statement; the later analytic
estimates only have to bound the cardinalities of those two sets.
-/

open scoped BigOperators

namespace Erdos444

noncomputable section

/-- Multiplicity, in `n`, of primes in the finite window `(y, X]`. -/
def largePrimeWindowMultiplicity (n y X : ℕ) : ℕ :=
  ∑ p ∈ Erdos697.PrimeWindow.primes y X, n.factorization p

private theorem largePrimeSupport_subset_window
    {a y X : ℕ} (ha : a ≠ 0) (haX : a ≤ X) :
    largePrimeSupport a y ⊆ Erdos697.PrimeWindow.primes y X := by
  intro p hp
  have hpData := mem_largePrimeSupport ha |>.mp hp
  have hpX : p ≤ X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hpData.2.2).trans haX
  exact Erdos697.PrimeWindow.mem_primes.mpr
    ⟨hpData.1, hpX, hpData.2.1⟩

private theorem distinctCount_le_windowMultiplicity
    {a y X : ℕ} (ha : a ≠ 0) (haX : a ≤ X) :
    largePrimeDistinctCount a y ≤
      ∑ p ∈ Erdos697.PrimeWindow.primes y X, a.factorization p := by
  have hsubset := largePrimeSupport_subset_window (y := y) ha haX
  unfold largePrimeDistinctCount
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ _p ∈ largePrimeSupport a y, 1) ≤
        ∑ p ∈ largePrimeSupport a y, a.factorization p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_largePrimeSupport ha |>.mp hp
      exact hpData.2.1.factorization_pos_of_dvd ha hpData.2.2
    _ ≤ ∑ p ∈ Erdos697.PrimeWindow.primes y X,
        a.factorization p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpWindow hpNot
      exact Nat.zero_le _

private theorem largePrimeSupport_mono_dvd
    {a n y : ℕ} (ha : a ≠ 0) (hn : n ≠ 0) (han : a ∣ n) :
    largePrimeSupport a y ⊆ largePrimeSupport n y := by
  intro p hp
  have hpData := mem_largePrimeSupport ha |>.mp hp
  exact mem_largePrimeSupport hn |>.mpr
    ⟨hpData.1, hpData.2.1, hpData.2.2.trans han⟩

private theorem distinctCount_le_largeSupportMultiplicity
    {a n y : ℕ} (ha : a ≠ 0) (hn : n ≠ 0) (han : a ∣ n) :
    largePrimeDistinctCount a y ≤
      ∑ p ∈ largePrimeSupport n y, a.factorization p := by
  have hsubset := largePrimeSupport_mono_dvd (y := y) ha hn han
  unfold largePrimeDistinctCount
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ _p ∈ largePrimeSupport a y, 1) ≤
        ∑ p ∈ largePrimeSupport a y, a.factorization p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_largePrimeSupport ha |>.mp hp
      exact hpData.2.1.factorization_pos_of_dvd ha hpData.2.2
    _ ≤ ∑ p ∈ largePrimeSupport n y, a.factorization p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpSupport hpNot
      exact Nat.zero_le _

private theorem exists_representingTuple
    {Astar : Finset ℕ} {r N n : ℕ}
    (hn : n ∈ representationSupport Astar r N) :
    ∃ a ∈ orderedTuples Astar r, tupleProduct a ∣ n := by
  have hrep := (mem_representationSupport_iff.mp hn).2.2
  unfold representationCount at hrep
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hrep
  exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩

/-- A represented integer has at least `r * t` prime factors above `y`,
counted with multiplicity, provided every tuple entry has at least `t`
distinct such factors. -/
theorem mul_le_largePrimeMultiplicity_of_mem_representationSupport
    {Astar : Finset ℕ} {r N n y t : ℕ}
    (hpos : ∀ a ∈ Astar, 0 < a)
    (hrich : ∀ a ∈ Astar, t ≤ largePrimeDistinctCount a y)
    (hn : n ∈ representationSupport Astar r N) :
    r * t ≤ largePrimeMultiplicity n y := by
  obtain ⟨a, haTuple, haDvd⟩ := exists_representingTuple hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_representationSupport_iff.mp hn).1
  have hprod0 : tupleProduct a ≠ 0 :=
    (tupleProduct_pos haTuple hpos).ne'
  have hfactLe : (tupleProduct a).factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hprod0 hn0).mpr haDvd
  have hentryDvd (i : Fin r) : a i ∣ tupleProduct a := by
    unfold tupleProduct
    exact Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  calc
    r * t = ∑ _i : Fin r, t := by simp
    _ ≤ ∑ i : Fin r, largePrimeDistinctCount (a i) y := by
      apply Finset.sum_le_sum
      intro i hi
      exact hrich (a i) (mem_orderedTuples_iff.mp haTuple i)
    _ ≤ ∑ i : Fin r,
        ∑ p ∈ largePrimeSupport n y, (a i).factorization p := by
      apply Finset.sum_le_sum
      intro i hi
      have hai : a i ∈ Astar := mem_orderedTuples_iff.mp haTuple i
      exact distinctCount_le_largeSupportMultiplicity
        (hpos (a i) hai).ne'
        hn0 ((hentryDvd i).trans haDvd)
    _ = ∑ p ∈ largePrimeSupport n y,
        ∑ i : Fin r, (a i).factorization p := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ largePrimeSupport n y,
        (tupleProduct a).factorization p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Nat.factorization_prod_apply
        (fun i hi ↦ (hpos (a i)
          (mem_orderedTuples_iff.mp haTuple i)).ne')).symm
    _ ≤ ∑ p ∈ largePrimeSupport n y, n.factorization p := by
      apply Finset.sum_le_sum
      intro p hp
      exact hfactLe p
    _ = largePrimeMultiplicity n y := by
      rfl

/-- Stronger window form of the preceding lemma.  The bound on tuple
entries ensures that every large prime contributed by a tuple lies in
`(y, X]`. -/
theorem mul_le_largePrimeWindowMultiplicity_of_mem_representationSupport
    {Astar : Finset ℕ} {r N n y t X : ℕ}
    (hpos : ∀ a ∈ Astar, 0 < a)
    (hle : ∀ a ∈ Astar, a ≤ X)
    (hrich : ∀ a ∈ Astar, t ≤ largePrimeDistinctCount a y)
    (hn : n ∈ representationSupport Astar r N) :
    r * t ≤ largePrimeWindowMultiplicity n y X := by
  obtain ⟨a, haTuple, haDvd⟩ := exists_representingTuple hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_representationSupport_iff.mp hn).1
  have hprod0 : tupleProduct a ≠ 0 :=
    (tupleProduct_pos haTuple hpos).ne'
  have hfactLe : (tupleProduct a).factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hprod0 hn0).mpr haDvd
  calc
    r * t = ∑ _i : Fin r, t := by simp
    _ ≤ ∑ i : Fin r, largePrimeDistinctCount (a i) y := by
      apply Finset.sum_le_sum
      intro i hi
      exact hrich (a i) (mem_orderedTuples_iff.mp haTuple i)
    _ ≤ ∑ i : Fin r,
        ∑ p ∈ Erdos697.PrimeWindow.primes y X,
          (a i).factorization p := by
      apply Finset.sum_le_sum
      intro i hi
      have hai : a i ∈ Astar := mem_orderedTuples_iff.mp haTuple i
      exact distinctCount_le_windowMultiplicity
        (hpos (a i) hai).ne'
        (hle (a i) hai)
    _ = ∑ p ∈ Erdos697.PrimeWindow.primes y X,
        ∑ i : Fin r, (a i).factorization p := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Erdos697.PrimeWindow.primes y X,
        (tupleProduct a).factorization p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Nat.factorization_prod_apply
        (fun i hi ↦ (hpos (a i)
          (mem_orderedTuples_iff.mp haTuple i)).ne')).symm
    _ ≤ ∑ p ∈ Erdos697.PrimeWindow.primes y X,
        n.factorization p := by
      apply Finset.sum_le_sum
      intro p hp
      exact hfactLe p
    _ = largePrimeWindowMultiplicity n y X := by
      rfl

private theorem subset_factorization_sum_le_card_add_excess
    {n y : ℕ} (hn : n ≠ 0) (W : Finset ℕ)
    (hW : W ⊆ largePrimeSupport n y) :
    (∑ p ∈ W, n.factorization p) ≤
      W.card + repeatedPrimeExcess n y := by
  let S := largePrimeSupport n y
  let O := S \ W
  have hdisj : Disjoint W O := Finset.disjoint_sdiff
  have hunion : W ∪ O = S := Finset.union_sdiff_of_subset hW
  have hcardO : O.card ≤ ∑ p ∈ O, n.factorization p := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro p hp
    have hpS : p ∈ largePrimeSupport n y := by
      exact (Finset.mem_sdiff.mp hp).1
    have hpData := mem_largePrimeSupport hn |>.mp hpS
    exact hpData.2.1.factorization_pos_of_dvd hn hpData.2.2
  have hsumSplit : largePrimeMultiplicity n y =
      (∑ p ∈ W, n.factorization p) +
        ∑ p ∈ O, n.factorization p := by
    unfold largePrimeMultiplicity
    change (∑ p ∈ S, n.factorization p) = _
    rw [← hunion, Finset.sum_union hdisj]
  have hcardSplit : largePrimeDistinctCount n y = W.card + O.card := by
    unfold largePrimeDistinctCount
    change S.card = _
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  unfold repeatedPrimeExcess
  rw [hsumSplit, hcardSplit]
  omega

/-- Prime-window multiplicity is bounded by the number of distinct window
prime divisors plus the total repeated-prime excess above `y`. -/
theorem largePrimeWindowMultiplicity_le_count_add_excess
    {n y X : ℕ} (hn : n ≠ 0) :
    largePrimeWindowMultiplicity n y X ≤
      primeDivisorCount (Erdos697.PrimeWindow.primes y X) n +
        repeatedPrimeExcess n y := by
  let P := Erdos697.PrimeWindow.primes y X
  let W := P.filter fun p ↦ p ∣ n
  have hWsub : W ⊆ largePrimeSupport n y := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpWindow := Erdos697.PrimeWindow.mem_primes.mp hpData.1
    exact mem_largePrimeSupport hn |>.mpr
      ⟨hpWindow.1, hpWindow.2.2, hpData.2⟩
  have hsum : largePrimeWindowMultiplicity n y X =
      ∑ p ∈ W, n.factorization p := by
    unfold largePrimeWindowMultiplicity
    change (∑ p ∈ P, n.factorization p) = _
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpP hpNot
    have hpNotDvd : ¬ p ∣ n := by
      intro hpDvd
      exact hpNot (Finset.mem_filter.mpr ⟨hpP, hpDvd⟩)
    exact Nat.factorization_eq_zero_of_not_dvd hpNotDvd
  have hmain := subset_factorization_sum_le_card_add_excess hn W hWsub
  rw [hsum]
  simpa [primeDivisorCount, P, W, Nat.add_comm] using hmain

/-- Exact structural split of the product-representation support.

If `2 * B + K ≤ r * t`, a represented integer is either exceptional
because its repeated-prime excess is greater than `2 * B`, or it has at
least `K` distinct prime divisors in `(y, X]`. -/
theorem representationSupport_subset_repeatedPrime_union_manyPrime
    {Astar : Finset ℕ} {r X y t B K : ℕ}
    (hpos : ∀ a ∈ Astar, 0 < a)
    (hle : ∀ a ∈ Astar, a ≤ X)
    (hrich : ∀ a ∈ Astar, t ≤ largePrimeDistinctCount a y)
    (hBK : 2 * B + K ≤ r * t) :
    representationSupport Astar r (X ^ r) ⊆
      repeatedPrimeExceptionalUpTo y B (X ^ r) ∪
        manyPrimeDivisorsUpTo
          (Erdos697.PrimeWindow.primes y X) K (X ^ r) := by
  intro n hn
  have hnData := mem_representationSupport_iff.mp hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnData.1
  have hmult :=
    mul_le_largePrimeWindowMultiplicity_of_mem_representationSupport
      hpos hle hrich hn
  by_cases hexcess : 2 * B < repeatedPrimeExcess n y
  · exact Finset.mem_union_left _ <|
      mem_repeatedPrimeExceptionalUpTo.mpr
        ⟨hnData.1, hnData.2.1, hexcess⟩
  · apply Finset.mem_union_right
    apply mem_manyPrimeDivisorsUpTo.mpr
    refine ⟨hnData.1, hnData.2.1, ?_⟩
    have hwindow := largePrimeWindowMultiplicity_le_count_add_excess
      (y := y) (X := X) hn0
    omega

end

end Erdos444

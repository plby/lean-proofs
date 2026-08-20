/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperLargestPrimeShell
import ErdosProblems.Erdos446.FordVariableDenominator
import ErdosProblems.Erdos446.PrimeWindows
import Mathlib.MeasureTheory.Measure.Real

/-!
# Erdős Problem 446: the short-prime cluster window

This file proves the reciprocal-prime estimate in Ford's Lemma 3.2.  An
admissible prime is assigned one divisor witnessing `y < d*p ≤ 2*y`, and
the witnesses are grouped by `Nat.log 2 d`.  Primes in one group are within
a factor four.  The number of nonempty groups is controlled sharply by
`clusterLength`: after splitting the dyadic indices into the two parities,
the corresponding divisor intervals are pairwise disjoint subsets of the
divisor cluster.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- The admissible primes above a fixed smooth factor. -/
def fordAdmissiblePrimeFiber (X y z a : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter fun p ↦
    (a, p) ∈ fordAdmissibleLargestPrimePairs X y z

theorem mem_fordAdmissiblePrimeFiber {X y z a p : ℕ} :
    p ∈ fordAdmissiblePrimeFiber X y z a ↔
      p.Prime ∧ p ≤ z ∧
        (a, p) ∈ fordAdmissibleLargestPrimePairs X y z := by
  simp only [fordAdmissiblePrimeFiber, Finset.mem_filter,
    Nat.mem_primesLE]
  aesop

/-- The finite set of divisor witnesses for an admissible prime. -/
def fordPrimeWitnesses (y a p : ℕ) : Finset ℕ :=
  a.divisors.filter fun d ↦ y < d * p ∧ d * p ≤ 2 * y

theorem fordPrimeWitnesses_nonempty_of_admissible
    {X y a p : ℕ}
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    (fordPrimeWitnesses y a p).Nonempty := by
  obtain ⟨d, hd, hlow, hupp⟩ :=
    (mem_fordAdmissibleLargestPrimePairs.mp hap).2.2.2.2.2.2.2
  exact ⟨d, Finset.mem_filter.mpr ⟨hd, hlow, hupp⟩⟩

/-- A canonical witness divisor, with the harmless fallback `1` away from
the admissible family. -/
def fordPrimeWitness (y a p : ℕ) : ℕ :=
  if h : (fordPrimeWitnesses y a p).Nonempty then
    (fordPrimeWitnesses y a p).min' h
  else 1

theorem fordPrimeWitness_mem_of_admissible
    {X y a p : ℕ}
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    fordPrimeWitness y a p ∈ fordPrimeWitnesses y a p := by
  rw [fordPrimeWitness]
  split_ifs with h
  · exact Finset.min'_mem _ h
  · exact (h (fordPrimeWitnesses_nonempty_of_admissible hap)).elim

theorem fordPrimeWitness_spec_of_admissible
    {X y a p : ℕ}
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    fordPrimeWitness y a p ∈ a.divisors ∧
      y < fordPrimeWitness y a p * p ∧
      fordPrimeWitness y a p * p ≤ 2 * y := by
  exact Finset.mem_filter.mp (fordPrimeWitness_mem_of_admissible hap)

/-- Dyadic logarithmic bins actually occupied by divisor witnesses. -/
def fordWitnessBins (X y a : ℕ) : Finset ℕ :=
  (fordAdmissiblePrimeFiber X y (2 * y) a).image fun p ↦
    Nat.log 2 (fordPrimeWitness y a p)

/-- The primes assigned to one witness bin. -/
def fordAdmissiblePrimeFiberBin (X y a j : ℕ) : Finset ℕ :=
  (fordAdmissiblePrimeFiber X y (2 * y) a).filter fun p ↦
    Nat.log 2 (fordPrimeWitness y a p) = j

theorem mem_fordWitnessBins {X y a j : ℕ} :
    j ∈ fordWitnessBins X y a ↔
      ∃ p ∈ fordAdmissiblePrimeFiber X y (2 * y) a,
        Nat.log 2 (fordPrimeWitness y a p) = j := by
  simp [fordWitnessBins]

theorem mem_fordAdmissiblePrimeFiberBin {X y a j p : ℕ} :
    p ∈ fordAdmissiblePrimeFiberBin X y a j ↔
      p ∈ fordAdmissiblePrimeFiber X y (2 * y) a ∧
        Nat.log 2 (fordPrimeWitness y a p) = j := by
  simp [fordAdmissiblePrimeFiberBin]

/-- A representative divisor from an occupied witness bin. -/
def fordWitnessBinDivisor (X y a j : ℕ) : ℕ := by
  classical
  exact if h : ∃ p ∈ fordAdmissiblePrimeFiber X y (2 * y) a,
        Nat.log 2 (fordPrimeWitness y a p) = j then
      fordPrimeWitness y a (Classical.choose h)
    else 1

theorem fordWitnessBinDivisor_spec {X y a j : ℕ}
    (hj : j ∈ fordWitnessBins X y a) :
    fordWitnessBinDivisor X y a j ∈ a.divisors ∧
      Nat.log 2 (fordWitnessBinDivisor X y a j) = j := by
  rw [mem_fordWitnessBins] at hj
  rw [fordWitnessBinDivisor]
  rw [dif_pos hj]
  have hpMem := (Classical.choose_spec hj).1
  have hpPair := (mem_fordAdmissiblePrimeFiber.mp hpMem).2.2
  exact ⟨(fordPrimeWitness_spec_of_admissible hpPair).1,
    (Classical.choose_spec hj).2⟩

theorem fordWitnessBinDivisor_pos {X y a j : ℕ}
    (hj : j ∈ fordWitnessBins X y a) :
    0 < fordWitnessBinDivisor X y a j :=
  Nat.pos_of_mem_divisors (fordWitnessBinDivisor_spec hj).1

/-- Integers in one binary-log bin differ by less than a factor two. -/
theorem lt_two_mul_of_log_two_eq {d e j : ℕ} (hd : 0 < d) (he : 0 < e)
    (hdj : Nat.log 2 d = j) (hej : Nat.log 2 e = j) :
    d < 2 * e := by
  have hdUpper : d < 2 ^ (j + 1) := by
    simpa [hdj] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) d
  have heLower : 2 ^ j ≤ e := by
    simpa [hej] using Nat.pow_log_le_self 2 he.ne'
  calc
    d < 2 ^ (j + 1) := hdUpper
    _ = 2 * 2 ^ j := by rw [pow_succ']
    _ ≤ 2 * e := Nat.mul_le_mul_left 2 heLower

/-- Primes assigned to one witness bin are mutually within a factor four. -/
theorem fordAdmissiblePrimeFiberBin_comparable
    {X y a j p q : ℕ}
    (hp : p ∈ fordAdmissiblePrimeFiberBin X y a j)
    (hq : q ∈ fordAdmissiblePrimeFiberBin X y a j) :
    p ≤ 4 * q := by
  have hpData := mem_fordAdmissiblePrimeFiberBin.mp hp
  have hqData := mem_fordAdmissiblePrimeFiberBin.mp hq
  have hpPair := (mem_fordAdmissiblePrimeFiber.mp hpData.1).2.2
  have hqPair := (mem_fordAdmissiblePrimeFiber.mp hqData.1).2.2
  have hdp := fordPrimeWitness_spec_of_admissible hpPair
  have heq := fordPrimeWitness_spec_of_admissible hqPair
  have hdpos := Nat.pos_of_mem_divisors hdp.1
  have hepos := Nat.pos_of_mem_divisors heq.1
  have hed : fordPrimeWitness y a q < 2 * fordPrimeWitness y a p :=
    lt_two_mul_of_log_two_eq hepos hdpos hqData.2 hpData.2
  have htwoe : 2 * fordPrimeWitness y a q ≤
      4 * fordPrimeWitness y a p := by omega
  have hmul : fordPrimeWitness y a p * p <
      fordPrimeWitness y a p * (4 * q) := by
    calc
      fordPrimeWitness y a p * p ≤ 2 * y := hdp.2.2
      _ < 2 * (fordPrimeWitness y a q * q) := by omega
      _ ≤ (4 * fordPrimeWitness y a p) * q := by
        simpa [mul_assoc] using Nat.mul_le_mul_right q htwoe
      _ = fordPrimeWitness y a p * (4 * q) := by ring
  exact (Nat.mul_lt_mul_left hdpos).mp hmul |>.le

/-! ## Packing the occupied dyadic witness bins -/

/-- One parity class of the occupied witness bins. -/
def fordWitnessBinsParity (X y a r : ℕ) : Finset ℕ :=
  (fordWitnessBins X y a).filter fun j ↦ j % 2 = r

theorem mem_fordWitnessBinsParity {X y a r j : ℕ} :
    j ∈ fordWitnessBinsParity X y a r ↔
      j ∈ fordWitnessBins X y a ∧ j % 2 = r := by
  simp [fordWitnessBinsParity]

theorem two_mul_binDivisor_le_of_add_two_le
    {X y a j k : ℕ} (hj : j ∈ fordWitnessBins X y a)
    (hk : k ∈ fordWitnessBins X y a) (hjk : j + 2 ≤ k) :
    2 * fordWitnessBinDivisor X y a j ≤
      fordWitnessBinDivisor X y a k := by
  have hdpos := fordWitnessBinDivisor_pos hj
  have hepos := fordWitnessBinDivisor_pos hk
  have hjlog := (fordWitnessBinDivisor_spec hj).2
  have hklog := (fordWitnessBinDivisor_spec hk).2
  have hdUpper : fordWitnessBinDivisor X y a j < 2 ^ (j + 1) := by
    simpa [hjlog] using Nat.lt_pow_succ_log_self (by omega : 1 < 2)
      (fordWitnessBinDivisor X y a j)
  have heLower : 2 ^ k ≤ fordWitnessBinDivisor X y a k := by
    simpa [hklog] using Nat.pow_log_le_self 2 hepos.ne'
  have hpow : 2 ^ (j + 2) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) hjk
  exact (calc
    2 * fordWitnessBinDivisor X y a j <
        2 * 2 ^ (j + 1) := (Nat.mul_lt_mul_left (by omega)).mpr hdUpper
    _ = 2 ^ (j + 2) := by ring
    _ ≤ 2 ^ k := hpow
    _ ≤ fordWitnessBinDivisor X y a k := heLower).le

theorem divisorLogInterval_disjoint_of_two_mul_le
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : 2 * d ≤ e) :
    Disjoint (divisorLogInterval d) (divisorLogInterval e) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hdeR : (2 : ℝ) * d ≤ e := by exact_mod_cast hde
  have hlog : Real.log (d : ℝ) ≤
      Real.log (e : ℝ) - Real.log 2 := by
    have hmono : Real.log ((2 : ℝ) * d) ≤ Real.log (e : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simpa only [Set.mem_Ioi] using mul_pos (by norm_num : (0 : ℝ) < 2) hdR)
        (by simpa only [Set.mem_Ioi] using heR) hdeR
    rw [Real.log_mul (by norm_num) hdR.ne'] at hmono
    linarith
  rw [Set.disjoint_left]
  intro u hud hue
  have hud' := hud
  have hue' := hue
  rw [divisorLogInterval, Set.mem_Ico] at hud' hue'
  linarith

theorem fordWitnessBinIntervals_pairwiseDisjoint
    {X y a r : ℕ} :
    (fordWitnessBinsParity X y a r : Set ℕ).PairwiseDisjoint
      (fun j ↦ divisorLogInterval (fordWitnessBinDivisor X y a j)) := by
  intro j hj k hk hjk
  have hjData := mem_fordWitnessBinsParity.mp hj
  have hkData := mem_fordWitnessBinsParity.mp hk
  have hgap : j + 2 ≤ k ∨ k + 2 ≤ j := by
    rcases lt_or_gt_of_ne hjk with hjlt | hklt
    · left
      have hneSucc : j + 1 ≠ k := by
        intro heq
        have := congrArg (fun n : ℕ ↦ n % 2) heq
        omega
      omega
    · right
      have hneSucc : k + 1 ≠ j := by
        intro heq
        have := congrArg (fun n : ℕ ↦ n % 2) heq
        omega
      omega
  rcases hgap with hgap | hgap
  · exact divisorLogInterval_disjoint_of_two_mul_le
      (fordWitnessBinDivisor_pos hjData.1)
      (fordWitnessBinDivisor_pos hkData.1)
      (two_mul_binDivisor_le_of_add_two_le hjData.1 hkData.1 hgap)
  · exact (divisorLogInterval_disjoint_of_two_mul_le
      (fordWitnessBinDivisor_pos hkData.1)
      (fordWitnessBinDivisor_pos hjData.1)
      (two_mul_binDivisor_le_of_add_two_le hkData.1 hjData.1 hgap)).symm

theorem fordWitnessBinsParity_card_mul_log_two_le_clusterLength
    {X y a r : ℕ} :
    ((fordWitnessBinsParity X y a r).card : ℝ) * Real.log 2 ≤
      clusterLength a := by
  let B := fordWitnessBinsParity X y a r
  let D : ℕ → Set ℝ := fun j ↦
    divisorLogInterval (fordWitnessBinDivisor X y a j)
  have hdisj : (B : Set ℕ).PairwiseDisjoint D := by
    simpa only [B, D] using
      (fordWitnessBinIntervals_pairwiseDisjoint (X := X) (y := y)
        (a := a) (r := r))
  have hmeas : ∀ j ∈ B, MeasurableSet (D j) := by
    intro j hj
    exact measurableSet_divisorLogInterval _
  have hsub : (⋃ j ∈ B, D j) ⊆ divisorCluster a := by
    intro u hu
    rw [Set.mem_iUnion] at hu
    obtain ⟨j, hu⟩ := hu
    rw [Set.mem_iUnion] at hu
    obtain ⟨hj, hu⟩ := hu
    exact divisorLogInterval_subset_cluster
      (fordWitnessBinDivisor_spec
        (mem_fordWitnessBinsParity.mp hj).1).1 hu
  have hfinite : ∀ j ∈ B, volume (D j) ≠ ∞ := by
    intro j hj
    simp only [D, volume_divisorLogInterval]
    exact ne_of_lt ENNReal.ofReal_lt_top
  have hunion := MeasureTheory.measureReal_biUnion_finset
    (μ := volume) hdisj hmeas hfinite
  have hmono : volume.real (⋃ j ∈ B, D j) ≤
      volume.real (divisorCluster a) :=
    MeasureTheory.measureReal_mono hsub
      (volume_divisorCluster_lt_top a).ne
  rw [hunion] at hmono
  simpa only [D, Measure.real, volume_divisorLogInterval,
    ENNReal.toReal_ofReal (Real.log_nonneg one_le_two),
    Finset.sum_const, nsmul_eq_mul, clusterLength] using hmono

theorem fordWitnessBins_eq_parity_union (X y a : ℕ) :
    fordWitnessBins X y a =
      fordWitnessBinsParity X y a 0 ∪
        fordWitnessBinsParity X y a 1 := by
  ext j
  simp only [mem_fordWitnessBinsParity, Finset.mem_union]
  constructor
  · intro hj
    have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hmod with hmod | hmod
    · exact Or.inl ⟨hj, hmod⟩
    · exact Or.inr ⟨hj, hmod⟩
  · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj

theorem fordWitnessBinsParity_disjoint (X y a : ℕ) :
    Disjoint (fordWitnessBinsParity X y a 0)
      (fordWitnessBinsParity X y a 1) := by
  rw [Finset.disjoint_left]
  intro j hj0 hj1
  have h0 := (mem_fordWitnessBinsParity.mp hj0).2
  have h1 := (mem_fordWitnessBinsParity.mp hj1).2
  omega

/-- The occupied binary-log bins cost at most two copies of the divisor
cluster: one for each parity. -/
theorem fordWitnessBins_card_mul_log_two_le_two_clusterLength
    (X y a : ℕ) :
    ((fordWitnessBins X y a).card : ℝ) * Real.log 2 ≤
      2 * clusterLength a := by
  have h0 := fordWitnessBinsParity_card_mul_log_two_le_clusterLength
    (X := X) (y := y) (a := a) (r := 0)
  have h1 := fordWitnessBinsParity_card_mul_log_two_le_clusterLength
    (X := X) (y := y) (a := a) (r := 1)
  rw [fordWitnessBins_eq_parity_union,
    Finset.card_union_of_disjoint (fordWitnessBinsParity_disjoint X y a)]
  push_cast
  linarith

/-! ## A uniform factor-four reciprocal-prime estimate -/

theorem exists_pos_uniform_quadruplePrimeMass_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, q.Prime →
      quadruplePrimeMass q ≤ K / Real.log (q : ℝ) := by
  have hevent := eventually_dyadicPrimeMass_bounds
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  let N := max 3 N₀
  let M := primeSetMass (Nat.primesLE (4 * N))
  let K : ℝ := 6 + M * Real.log (N : ℝ)
  have hN3 : 3 ≤ N := by simp [N]
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hM : 0 ≤ M := by
    dsimp [M, primeSetMass]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, fun q hq ↦ ?_⟩
  have hlogq : 0 < Real.log (q : ℝ) := hq.log_pos
  by_cases hqN : N ≤ q
  · have hprime : ∀ t : ℕ, N ≤ t →
        dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ) := by
      intro t ht
      exact (hN₀ t ((le_max_right 3 N₀).trans ht)).2
    have hbase := quadruplePrimeMass_upper hN3 hqN hprime
    exact hbase.trans (div_le_div_of_nonneg_right
      (by
        dsimp [K]
        exact le_add_of_nonneg_right (mul_nonneg hM hlogN.le))
      hlogq.le)
  · have hqLt : q < N := lt_of_not_ge hqN
    have hsub : quadruplePrimes q ⊆ Nat.primesLE (4 * N) := by
      intro p hp
      have hpData := mem_quadruplePrimes.mp hp
      rw [Nat.mem_primesLE]
      exact ⟨hpData.2.1.trans (by omega), hpData.2.2⟩
    have hmass : quadruplePrimeMass q ≤ M := by
      rw [quadruplePrimeMass]
      dsimp [M, primeSetMass]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp hnot ↦ by positivity)
    have hlogLe : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast hqLt.le)
    apply hmass.trans
    rw [le_div_iff₀ hlogq]
    calc
      M * Real.log (q : ℝ) ≤ M * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLe hM
      _ ≤ K := by dsimp [K]; linarith

/-- Any finite prime set whose elements are mutually within a factor four
has reciprocal mass bounded by the logarithm of each of its elements. -/
theorem exists_pos_comparable_primeSetMass_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q) →
      ∀ q ∈ Q, primeSetMass Q ≤ K / Real.log (q : ℝ) := by
  obtain ⟨K₀, hK₀, hquad⟩ :=
    exists_pos_uniform_quadruplePrimeMass_upper
  let Kb : ℝ := K₀ + 1
  let K : ℝ := 3 * Kb
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun Q hprime hcomp q hq ↦ ?_⟩
  have hqPrime := hprime q hq
  have hqlog : 0 < Real.log (q : ℝ) := hqPrime.log_pos
  -- Replace the arbitrary distinguished element by the minimum of `Q`.
  have hQ : Q.Nonempty := ⟨q, hq⟩
  let m := Q.min' hQ
  have hmQ : m ∈ Q := Finset.min'_mem Q hQ
  have hmPrime := hprime m hmQ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmPrime.pos
  have heraseMin : Q.erase m ⊆ quadruplePrimes m := by
    intro p hp
    have hpQ := Finset.mem_of_mem_erase hp
    have hpne : p ≠ m := Finset.ne_of_mem_erase hp
    have hmp : m < p := lt_of_le_of_ne (Finset.min'_le Q p hpQ) hpne.symm
    exact mem_quadruplePrimes.mpr
      ⟨hmp, hcomp p hpQ m hmQ, hprime p hpQ⟩
  have heraseMass :
      (∑ p ∈ Q.erase m, 1 / (p : ℝ)) ≤ quadruplePrimeMass m := by
    rw [quadruplePrimeMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg heraseMin
      (fun p hp hnot ↦ by positivity)
  have hlogM : 0 < Real.log (m : ℝ) := hmPrime.log_pos
  have hlogMq : Real.log (m : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hmR (by exact_mod_cast Finset.min'_le Q q hq)
  have hlogmLeM : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hmR
    linarith
  have hinvM : 1 / (m : ℝ) ≤ 1 / Real.log (m : ℝ) :=
    one_div_le_one_div_of_le hlogM hlogmLeM
  have hmassMin : primeSetMass Q ≤ Kb / Real.log (m : ℝ) := by
    calc
      primeSetMass Q =
          (∑ p ∈ Q.erase m, 1 / (p : ℝ)) + 1 / (m : ℝ) := by
        rw [primeSetMass]
        exact (Finset.sum_erase_add Q (fun p : ℕ ↦ 1 / (p : ℝ)) hmQ).symm
      _ ≤ quadruplePrimeMass m + 1 / (m : ℝ) :=
        add_le_add heraseMass le_rfl
      _ ≤ K₀ / Real.log (m : ℝ) + 1 / Real.log (m : ℝ) :=
        add_le_add (hquad m hmPrime) hinvM
      _ = Kb / Real.log (m : ℝ) := by dsimp [Kb]; ring
  have hqLe : q ≤ 4 * m := hcomp q hq m hmQ
  have hlogqLe : Real.log (q : ℝ) ≤ 3 * Real.log (m : ℝ) := by
    have hlog4m : Real.log (q : ℝ) ≤ Real.log ((4 : ℝ) * m) :=
      Real.log_le_log (by exact_mod_cast hqPrime.pos)
        (by exact_mod_cast hqLe)
    rw [Real.log_mul (by norm_num) hmR.ne'] at hlog4m
    have hmTwo : (2 : ℝ) ≤ m := by exact_mod_cast hmPrime.two_le
    have hlogTwo : Real.log (2 : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) hmTwo
    have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlogFour] at hlog4m
    linarith
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  exact hmassMin.trans (by
    rw [div_le_div_iff₀ hlogM hqlog]
    dsimp [K]
    nlinarith)

/-! ## Comparison with Ford's varying logarithm -/

theorem fordVariableLogArgument_le_two_mul_prime_of_admissible
    {X y a p : ℕ} (hy : 1 ≤ y)
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    fordVariableLogArgument y a.primeFactors ≤ 2 * (p : ℝ) := by
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  have haPos : 0 < a := hdata.1
  have hpPos : 0 < p := hdata.2.2.2.1.pos
  have haSq : Squarefree a := hdata.2.2.2.2.1
  obtain ⟨d, hd, hydp, hdp⟩ := hdata.2.2.2.2.2.2.2
  have hdPos := Nat.pos_of_mem_divisors hd
  have hdDvd := Nat.dvd_of_mem_divisors hd
  have hdLeA : d ≤ a := Nat.le_of_dvd haPos hdDvd
  have hya : y ≤ a * p := by
    exact (Nat.le_of_lt hydp).trans (Nat.mul_le_mul_right p hdLeA)
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hpow : (y : ℝ) ^ (2 / 3 : ℝ) ≤ y :=
    Real.rpow_le_self_of_one_le hyR (by norm_num)
  have hfirst : (y : ℝ) ^ (2 / 3 : ℝ) / (a : ℝ) ≤ p := by
    rw [div_le_iff₀ haR]
    calc
      (y : ℝ) ^ (2 / 3 : ℝ) ≤ y := hpow
      _ ≤ (a : ℝ) * p := by
        have : (y : ℝ) ≤ (a * p : ℕ) := by exact_mod_cast hya
        simpa using this
      _ = (p : ℝ) * a := by ring
  have hprod : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  have hmax : primeSupportMax a.primeFactors ≤ p := by
    by_cases hS : a.primeFactors.Nonempty
    · have hmem := primeSupportMax_mem hS
      have hprime := Nat.prime_of_mem_primeFactors hmem
      exact (hdata.2.2.2.2.2.1 _ hprime
        (Nat.dvd_of_mem_primeFactors hmem)).le
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [primeSupportMax, hempty]
  unfold fordVariableLogArgument
  rw [hprod]
  have hmaxR : (primeSupportMax a.primeFactors : ℝ) ≤ p := by
    exact_mod_cast hmax
  nlinarith

theorem one_lt_fordVariableLogArgument_of_admissible
    {X y a p : ℕ} (hy : 2 ≤ y)
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    1 < fordVariableLogArgument y a.primeFactors := by
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  have haSq : Squarefree a := hdata.2.2.2.2.1
  have hprod : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  by_cases hS : a.primeFactors.Nonempty
  · have hpmax : (primeSupportMax a.primeFactors).Prime :=
      Nat.prime_of_mem_primeFactors (primeSupportMax_mem hS)
    have hmaxTwo : (2 : ℝ) ≤ primeSupportMax a.primeFactors := by
      exact_mod_cast hpmax.two_le
    unfold fordVariableLogArgument
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (hmaxTwo.trans (le_add_of_nonneg_left (by positivity)))
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
    have haOne : a = 1 := by
      rw [← hprod, hempty]
      simp
    have hyOne : (1 : ℝ) < y := by
      exact_mod_cast (show 1 < y by omega)
    have hpow : 1 < (y : ℝ) ^ (2 / 3 : ℝ) :=
      Real.one_lt_rpow hyOne (by norm_num)
    unfold fordVariableLogArgument
    rw [hempty]
    simpa [primeSupportMax] using hpow

theorem log_fordVariableLogArgument_le_two_log_prime_of_admissible
    {X y a p : ℕ} (hy : 2 ≤ y)
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    Real.log (fordVariableLogArgument y a.primeFactors) ≤
      2 * Real.log (p : ℝ) := by
  have hpPrime := (mem_fordAdmissibleLargestPrimePairs.mp hap).2.2.2.1
  have hargPos : 0 < fordVariableLogArgument y a.primeFactors :=
    (one_lt_fordVariableLogArgument_of_admissible hy hap).trans' zero_lt_one
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hmono : Real.log (fordVariableLogArgument y a.primeFactors) ≤
      Real.log ((2 : ℝ) * p) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hargPos)
      (by simpa only [Set.mem_Ioi] using mul_pos (by norm_num) hpR)
      (fordVariableLogArgument_le_two_mul_prime_of_admissible (by omega) hap)
  rw [Real.log_mul (by norm_num) hpR.ne'] at hmono
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hpPrime.two_le)
  linarith

/-! ## Exact partition of the prime fiber by witness bins -/

theorem fordAdmissiblePrimeFiberBins_pairwiseDisjoint (X y a : ℕ) :
    (fordWitnessBins X y a : Set ℕ).PairwiseDisjoint
      (fordAdmissiblePrimeFiberBin X y a) := by
  intro j hj k hk hjk
  change Disjoint (fordAdmissiblePrimeFiberBin X y a j)
    (fordAdmissiblePrimeFiberBin X y a k)
  rw [Finset.disjoint_left]
  intro p hpj hpk
  have hpj' := (mem_fordAdmissiblePrimeFiberBin.mp hpj).2
  have hpk' := (mem_fordAdmissiblePrimeFiberBin.mp hpk).2
  exact hjk (hpj'.symm.trans hpk')

theorem biUnion_fordAdmissiblePrimeFiberBins (X y a : ℕ) :
    (fordWitnessBins X y a).biUnion
      (fordAdmissiblePrimeFiberBin X y a) =
        fordAdmissiblePrimeFiber X y (2 * y) a := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨j, hj, hpj⟩ := hp
    exact (mem_fordAdmissiblePrimeFiberBin.mp hpj).1
  · intro hp
    rw [Finset.mem_biUnion]
    let j := Nat.log 2 (fordPrimeWitness y a p)
    exact ⟨j, mem_fordWitnessBins.mpr ⟨p, hp, rfl⟩,
      mem_fordAdmissiblePrimeFiberBin.mpr ⟨hp, rfl⟩⟩

theorem sum_fordAdmissiblePrimeFiber_eq_bins
    (X y a : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ fordAdmissiblePrimeFiber X y (2 * y) a, f p) =
      ∑ j ∈ fordWitnessBins X y a,
        ∑ p ∈ fordAdmissiblePrimeFiberBin X y a j, f p := by
  rw [← biUnion_fordAdmissiblePrimeFiberBins X y a,
    Finset.sum_biUnion (fordAdmissiblePrimeFiberBins_pairwiseDisjoint X y a)]

/-! ## Ford's short-prime estimate (equation (28d)) -/

theorem fordAdmissiblePrimeFiberBin_log_weight_le
    {K : ℝ}
    (hK : 0 < K)
    (hmass : ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q) →
      ∀ q ∈ Q, primeSetMass Q ≤ K / Real.log (q : ℝ))
    {X y a j : ℕ} (hy : 2 ≤ y) (hj : j ∈ fordWitnessBins X y a) :
    (∑ p ∈ fordAdmissiblePrimeFiberBin X y a j,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      4 * K / Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
  obtain ⟨q, hqFiber, hqLog⟩ := mem_fordWitnessBins.mp hj
  have hqBin : q ∈ fordAdmissiblePrimeFiberBin X y a j :=
    mem_fordAdmissiblePrimeFiberBin.mpr ⟨hqFiber, hqLog⟩
  have hqPair := (mem_fordAdmissiblePrimeFiber.mp hqFiber).2.2
  have hargOne := one_lt_fordVariableLogArgument_of_admissible hy hqPair
  have hargLog : 0 <
      Real.log (fordVariableLogArgument y a.primeFactors) :=
    Real.log_pos hargOne
  let Q := fordAdmissiblePrimeFiberBin X y a j
  have hprime : ∀ p ∈ Q, p.Prime := by
    intro p hp
    exact (mem_fordAdmissiblePrimeFiber.mp
      (mem_fordAdmissiblePrimeFiberBin.mp hp).1).1
  have hcomp : ∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q := by
    intro p hp q hq
    exact fordAdmissiblePrimeFiberBin_comparable hp hq
  have hpoint : ∀ p ∈ Q,
      1 / ((p : ℝ) * Real.log (p : ℝ)) ≤
        (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          (1 / (p : ℝ)) := by
    intro p hp
    have hpPrime := hprime p hp
    have hpLog : 0 < Real.log (p : ℝ) := hpPrime.log_pos
    have hpPair := (mem_fordAdmissiblePrimeFiber.mp
      (mem_fordAdmissiblePrimeFiberBin.mp hp).1).2.2
    have hlogCompare :=
      log_fordVariableLogArgument_le_two_log_prime_of_admissible hy hpPair
    have hinv : 1 / Real.log (p : ℝ) ≤
        2 / Real.log (fordVariableLogArgument y a.primeFactors) := by
      rw [div_le_div_iff₀ hpLog hargLog]
      linarith
    calc
      1 / ((p : ℝ) * Real.log (p : ℝ)) =
          (1 / (p : ℝ)) * (1 / Real.log (p : ℝ)) := by ring
      _ ≤ (1 / (p : ℝ)) *
          (2 / Real.log (fordVariableLogArgument y a.primeFactors)) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          (1 / (p : ℝ)) := by ring
  have hsum :
      (∑ p ∈ Q, 1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
        (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          primeSetMass Q := by
    calc
      (∑ p ∈ Q, 1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
          ∑ p ∈ Q,
            (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
              (1 / (p : ℝ)) :=
        Finset.sum_le_sum fun p hp ↦ hpoint p hp
      _ = (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          primeSetMass Q := by
        rw [primeSetMass, Finset.mul_sum]
  have hqPrime := hprime q hqBin
  have hqLogPos : 0 < Real.log (q : ℝ) := hqPrime.log_pos
  have hqMass := hmass Q hprime hcomp q hqBin
  have hqCompare :=
    log_fordVariableLogArgument_le_two_log_prime_of_admissible hy hqPair
  have hmassArg : primeSetMass Q ≤
      2 * K / Real.log (fordVariableLogArgument y a.primeFactors) := by
    apply hqMass.trans
    rw [div_le_div_iff₀ hqLogPos hargLog]
    nlinarith
  calc
    (∑ p ∈ fordAdmissiblePrimeFiberBin X y a j,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
        primeSetMass Q := hsum
    _ ≤ (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
        (2 * K / Real.log (fordVariableLogArgument y a.primeFactors)) := by
      exact mul_le_mul_of_nonneg_left hmassArg (by positivity)
    _ = 4 * K /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by ring

/-- Ford's Lemma 3.2 short-prime window estimate, in the exact finite form
needed after the largest-prime/rough-sieve shell reduction. -/
theorem exists_pos_admissiblePrimeFiber_log_weight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y X a : ℕ, 2 ≤ y →
      (∑ p ∈ fordAdmissiblePrimeFiber X y (2 * y) a,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      C * clusterLength a /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := exists_pos_comparable_primeSetMass_upper
  let C : ℝ := 8 * K / Real.log 2
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun y X a hy ↦ ?_⟩
  by_cases hB : (fordWitnessBins X y a).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hB
    obtain ⟨q₀, hq₀Fiber, hq₀Log⟩ := mem_fordWitnessBins.mp hj₀
    have hq₀Pair := (mem_fordAdmissiblePrimeFiber.mp hq₀Fiber).2.2
    have hargLog : 0 <
        Real.log (fordVariableLogArgument y a.primeFactors) :=
      Real.log_pos (one_lt_fordVariableLogArgument_of_admissible hy hq₀Pair)
    have hbins := fordWitnessBins_card_mul_log_two_le_two_clusterLength
      X y a
    rw [sum_fordAdmissiblePrimeFiber_eq_bins]
    calc
      (∑ j ∈ fordWitnessBins X y a,
          ∑ p ∈ fordAdmissiblePrimeFiberBin X y a j,
            1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
        ∑ _j ∈ fordWitnessBins X y a,
          4 * K /
            Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
        exact Finset.sum_le_sum fun j hj ↦
          fordAdmissiblePrimeFiberBin_log_weight_le hK hmass hy hj
      _ = ((fordWitnessBins X y a).card : ℝ) *
          (4 * K /
            Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * clusterLength a /
          Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
        rw [← mul_div_assoc]
        rw [div_le_div_iff₀ (sq_pos_of_pos hargLog)
          (sq_pos_of_pos hargLog)]
        dsimp [C]
        field_simp [hlogTwo.ne']
        nlinarith
  · have hBempty := Finset.not_nonempty_iff_eq_empty.mp hB
    have hFiberEmpty : fordAdmissiblePrimeFiber X y (2 * y) a = ∅ := by
      rw [← biUnion_fordAdmissiblePrimeFiberBins X y a, hBempty]
      simp
    rw [hFiberEmpty]
    simp only [Finset.sum_empty, zero_le]
    exact div_nonneg
      (mul_nonneg hC.le (clusterLength_nonneg a)) (sq_nonneg _)

end

end Erdos446

import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

/-!
# Exact definitions for Erdős problem 380

The greatest prime factor is taken after forming the entire interval product.
We use the harmless convention `largestPrimeFactor 0 = largestPrimeFactor 1 = 1`.
Bad intervals have positive endpoints, are nonempty, and have product greater
than one. The counting functions count points covered by arbitrary bad
intervals, including intervals whose right endpoint exceeds the cutoff.
-/

open scoped BigOperators Topology

namespace Erdos380

/-- Greatest prime factor, with value one at zero and one. -/
def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

@[simp] lemma largestPrimeFactor_zero : largestPrimeFactor 0 = 1 := by
  simp [largestPrimeFactor]

@[simp] lemma largestPrimeFactor_one : largestPrimeFactor 1 = 1 := by
  simp [largestPrimeFactor]

lemma one_le_largestPrimeFactor (n : ℕ) : 1 ≤ largestPrimeFactor n :=
  le_max_left _ _

lemma prime_le_largestPrimeFactor {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) : p ≤ largestPrimeFactor n := by
  exact (Finset.le_sup (f := id) (hp.mem_primeFactors hpn hn)).trans
    (le_max_right _ _)

lemma largestPrimeFactor_le {n y : ℕ} (hy : 1 ≤ y)
    (h : ∀ p, p.Prime → p ∣ n → p ≤ y) : largestPrimeFactor n ≤ y := by
  apply max_le hy
  apply Finset.sup_le
  intro p hp
  exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

lemma largestPrimeFactor_mem {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n ∈ n.primeFactors := by
  have hs : n.primeFactors.sup id ∈ n.primeFactors := by
    simpa using Finset.sup_mem_of_nonempty (f := id)
      (Nat.nonempty_primeFactors.mpr hn)
  have h1 : 1 ≤ n.primeFactors.sup id :=
    (Nat.prime_of_mem_primeFactors hs).one_le
  simpa [largestPrimeFactor, max_eq_right h1] using hs

lemma largestPrimeFactor_prime {n : ℕ} (hn : 1 < n) :
    (largestPrimeFactor n).Prime :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hn)

lemma largestPrimeFactor_dvd {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hn)

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) :
    largestPrimeFactor n ≤ n := by
  apply max_le hn
  exact Finset.sup_le fun _ hp => Nat.le_of_mem_primeFactors hp

@[simp] lemma largestPrimeFactor_of_prime {p : ℕ} (hp : p.Prime) :
    largestPrimeFactor p = p := by
  simp [largestPrimeFactor, hp.primeFactors, max_eq_right hp.one_le]

lemma largestPrimeFactor_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    largestPrimeFactor (n ^ k) = largestPrimeFactor n := by
  simp only [largestPrimeFactor, Nat.primeFactors_pow n hk]

lemma largestPrimeFactor_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    largestPrimeFactor (m * n) = max (largestPrimeFactor m) (largestPrimeFactor n) := by
  simp only [largestPrimeFactor, Nat.primeFactors_mul hm hn, Finset.sup_union]
  change max 1 (max (m.primeFactors.sup id) (n.primeFactors.sup id)) =
    max (max 1 (m.primeFactors.sup id)) (max 1 (n.primeFactors.sup id))
  omega

/-- Product of all integers in the inclusive interval. -/
def intervalProduct (u v : ℕ) : ℕ := ∏ n ∈ Finset.Icc u v, n

@[simp] lemma intervalProduct_singleton (n : ℕ) : intervalProduct n n = n := by
  simp [intervalProduct]

lemma intervalProduct_pos {u v : ℕ} (hu : 1 ≤ u) : 0 < intervalProduct u v := by
  apply Finset.prod_pos
  intro n hn
  exact lt_of_lt_of_le (by omega : 0 < u) (Finset.mem_Icc.mp hn).1

lemma dvd_intervalProduct {u v n : ℕ} (hn : n ∈ Finset.Icc u v) :
    n ∣ intervalProduct u v :=
  Finset.dvd_prod_of_mem id hn

/-- Largest prime factor of the whole interval product. -/
def intervalPrime (u v : ℕ) : ℕ := largestPrimeFactor (intervalProduct u v)

/-- The interval is positive, nonempty, and its largest prime factor is repeated. -/
def BadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ 1 < intervalProduct u v ∧
    intervalPrime u v ^ 2 ∣ intervalProduct u v

/-- An integer belongs to at least one bad interval, without bounding its endpoints. -/
def BadPoint (n : ℕ) : Prop :=
  ∃ u v : ℕ, BadInterval u v ∧ u ≤ n ∧ n ≤ v

/-- The singleton contribution, explicitly excluding zero and one. -/
def SingletonBad (n : ℕ) : Prop := 2 ≤ n ∧ largestPrimeFactor n ^ 2 ∣ n

@[simp] lemma badInterval_singleton_iff (n : ℕ) :
    BadInterval n n ↔ SingletonBad n := by
  simp only [BadInterval, intervalPrime, intervalProduct_singleton, le_refl,
    true_and, SingletonBad]
  omega

lemma SingletonBad.badPoint {n : ℕ} (hn : SingletonBad n) : BadPoint n :=
  ⟨n, n, (badInterval_singleton_iff n).mpr hn, le_rfl, le_rfl⟩

lemma BadPoint.pos {n : ℕ} (hn : BadPoint n) : 0 < n := by
  obtain ⟨u, v, hu, hun, hnv⟩ := hn
  exact lt_of_lt_of_le (by have := hu.1; omega : 0 < u) hun

lemma primeSquare_singletonBad {p : ℕ} (hp : p.Prime) : SingletonBad (p ^ 2) := by
  refine ⟨?_, ?_⟩
  · nlinarith [hp.two_le]
  · rw [largestPrimeFactor_pow p (by decide), largestPrimeFactor_of_prime hp]

noncomputable section

/-- Positive integers at most a natural cutoff lying in some bad interval. -/
def badPointsUpTo (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter BadPoint

/-- Integers at most a natural cutoff whose own greatest prime factor is repeated. -/
def singletonBadUpTo (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter SingletonBad

@[simp] lemma mem_badPointsUpTo {N n : ℕ} :
    n ∈ badPointsUpTo N ↔ 1 ≤ n ∧ n ≤ N ∧ BadPoint n := by
  classical
  simp [badPointsUpTo, and_assoc]

@[simp] lemma mem_singletonBadUpTo {N n : ℕ} :
    n ∈ singletonBadUpTo N ↔ 1 ≤ n ∧ n ≤ N ∧ SingletonBad n := by
  classical
  simp [singletonBadUpTo, and_assoc]

lemma singletonBadUpTo_subset_badPointsUpTo (N : ℕ) :
    singletonBadUpTo N ⊆ badPointsUpTo N := by
  intro n hn
  obtain ⟨hn1, hnN, hbad⟩ := mem_singletonBadUpTo.mp hn
  exact mem_badPointsUpTo.mpr ⟨hn1, hnN, hbad.badPoint⟩

/-- The exact counting function in the question, at a real cutoff. -/
def B (x : ℝ) : ℝ := ((badPointsUpTo ⌊x⌋₊).card : ℝ)

/-- The exact singleton comparison function, at a real cutoff. -/
def A (x : ℝ) : ℝ := ((singletonBadUpTo ⌊x⌋₊).card : ℝ)

lemma A_nonneg (x : ℝ) : 0 ≤ A x := Nat.cast_nonneg _

lemma B_nonneg (x : ℝ) : 0 ≤ B x := Nat.cast_nonneg _

lemma A_le_B (x : ℝ) : A x ≤ B x := by
  unfold A B
  exact_mod_cast Finset.card_le_card (singletonBadUpTo_subset_badPointsUpTo ⌊x⌋₊)

end

end Erdos380

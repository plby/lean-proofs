/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Smooth-number infrastructure for Erdős Problem 49

This file uses the non-strict convention that `n` is `y`-smooth when every
prime factor of `n` is at most `y`.  Mathlib's `Nat.smoothNumbers k` uses the
strict inequality `p < k`; consequently our predicate is exactly membership
in `Nat.smoothNumbers (y + 1)`.

The last section records a completely finite Euler-product identity.  It is
the algebraic core of Rankin's method: summing multiplicative weights over a
box of prime exponents factors as a product of finite geometric sums.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `n` is a positive `y`-smooth integer: all its prime factors are at most
`y`.  Requiring `n ≠ 0` is important, since Mathlib assigns the empty prime
factor set to zero. -/
def Smooth (y n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ≤ y

instance (y : ℕ) : DecidablePred (Smooth y) := fun _ ↦ inferInstance

@[simp] lemma smooth_zero (y : ℕ) : ¬ Smooth y 0 := by
  simp [Smooth]

@[simp] lemma smooth_one (y : ℕ) : Smooth y 1 := by
  simp [Smooth]

lemma smooth_ne_zero {y n : ℕ} (hn : Smooth y n) : n ≠ 0 := hn.1

lemma smooth_primeFactors_subset {y n : ℕ} (hn : Smooth y n) :
    n.primeFactors ⊆ Nat.primesLE y := by
  intro p hp
  exact Nat.mem_primesLE.mpr
    ⟨hn.2 p hp, Nat.prime_of_mem_primeFactors hp⟩

lemma smooth_iff_primeFactors_subset {y n : ℕ} :
    Smooth y n ↔ n ≠ 0 ∧ n.primeFactors ⊆ Nat.primesLE y := by
  constructor
  · intro hn
    exact ⟨hn.1, smooth_primeFactors_subset hn⟩
  · rintro ⟨hn0, hn⟩
    refine ⟨hn0, fun p hp ↦ ?_⟩
    exact (Nat.mem_primesLE.mp (hn hp)).1

/-- Bridge from the non-strict convention in this file to Mathlib's strict
smoothness convention. -/
lemma smooth_iff_mem_nat_smoothNumbers {y n : ℕ} :
    Smooth y n ↔ n ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers_iff_primeFactors_subset,
    smooth_iff_primeFactors_subset]
  constructor
  · rintro ⟨hn0, hn⟩
    refine ⟨hn0, fun p hp ↦ ?_⟩
    have hpy := (Nat.mem_primesLE.mp (hn hp)).1
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_iff.mpr hpy, Nat.prime_of_mem_primeFactors hp⟩
  · rintro ⟨hn0, hn⟩
    refine ⟨hn0, fun p hp ↦ ?_⟩
    have hp' := hn hp
    exact Nat.mem_primesLE.mpr
      ⟨Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hp').1,
        Nat.prime_of_mem_primeFactors hp⟩

lemma smooth_iff_prime_divisors {y n : ℕ} :
    Smooth y n ↔ n ≠ 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ y := by
  constructor
  · rintro ⟨hn0, hn⟩
    refine ⟨hn0, fun p hp hpdvd ↦ ?_⟩
    exact hn p (hp.mem_primeFactors hpdvd hn0)
  · rintro ⟨hn0, hn⟩
    refine ⟨hn0, fun p hp ↦ ?_⟩
    exact hn p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)

lemma smooth_mono {x y n : ℕ} (hxy : x ≤ y) (hn : Smooth x n) :
    Smooth y n := by
  refine ⟨hn.1, fun p hp ↦ (hn.2 p hp).trans hxy⟩

lemma smooth_self {n : ℕ} (hn : n ≠ 0) : Smooth n n := by
  refine ⟨hn, fun p hp ↦ Nat.le_of_mem_primeFactors hp⟩

lemma smooth_of_dvd {y m n : ℕ} (hn : Smooth y n) (hmn : m ∣ n) :
    Smooth y m := by
  rw [smooth_iff_mem_nat_smoothNumbers] at hn ⊢
  exact Nat.mem_smoothNumbers_of_dvd hn hmn

lemma smooth_mul {y m n : ℕ} (hm : Smooth y m) (hn : Smooth y n) :
    Smooth y (m * n) := by
  rw [smooth_iff_mem_nat_smoothNumbers] at hm hn ⊢
  exact Nat.mul_mem_smoothNumbers hm hn

lemma smooth_pow {y n e : ℕ} (hn : Smooth y n) : Smooth y (n ^ e) := by
  induction e with
  | zero => simp
  | succ e ih => simpa [pow_succ] using smooth_mul ih hn

lemma smooth_prime_iff {y p : ℕ} (hp : p.Prime) :
    Smooth y p ↔ p ≤ y := by
  simp [Smooth, hp, hp.ne_zero]

/-- Unique-factorization reconstruction, stated in the form used by finite
Euler-product arguments. -/
lemma smooth_factorization_reconstruction {y n : ℕ} (hn : Smooth y n) :
    n = ∏ p ∈ Nat.primesLE y, p ^ n.factorization p := by
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization hn.1
    _ = ∏ p ∈ Nat.primesLE y, p ^ n.factorization p := by
      apply Finset.prod_subset (smooth_primeFactors_subset hn)
      intro p hpP hpnot
      have hpnotSupport : p ∉ n.factorization.support := by
        simpa only [Nat.support_factorization] using hpnot
      rw [Finsupp.notMem_support_iff.mp hpnotSupport, pow_zero]

/-- The finite set of `y`-smooth positive integers at most `x`. -/
def smoothUpTo (x y : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (Smooth y)

@[simp] lemma mem_smoothUpTo {x y n : ℕ} :
    n ∈ smoothUpTo x y ↔ n ≤ x ∧ Smooth y n := by
  simp [smoothUpTo, Nat.lt_succ_iff, and_comm]

lemma smoothUpTo_eq_nat_smoothNumbersUpTo (x y : ℕ) :
    smoothUpTo x y = Nat.smoothNumbersUpTo x (y + 1) := by
  ext n
  simp [mem_smoothUpTo, Nat.mem_smoothNumbersUpTo,
    smooth_iff_mem_nat_smoothNumbers]

lemma smoothUpTo_mono_left {x x' y : ℕ} (hxx' : x ≤ x') :
    smoothUpTo x y ⊆ smoothUpTo x' y := by
  intro n hn
  exact mem_smoothUpTo.mpr
    ⟨(mem_smoothUpTo.mp hn).1.trans hxx', (mem_smoothUpTo.mp hn).2⟩

lemma smoothUpTo_mono_right {x y y' : ℕ} (hyy' : y ≤ y') :
    smoothUpTo x y ⊆ smoothUpTo x y' := by
  intro n hn
  exact mem_smoothUpTo.mpr
    ⟨(mem_smoothUpTo.mp hn).1, smooth_mono hyy' (mem_smoothUpTo.mp hn).2⟩

/-- A useful unconditional finite bound supplied by Mathlib: a smooth integer
is a square times a squarefree product of allowed primes. -/
lemma smoothUpTo_card_le_sqrt (x y : ℕ) :
    (smoothUpTo x y).card ≤ 2 ^ (Nat.primesLE y).card * x.sqrt := by
  rw [smoothUpTo_eq_nat_smoothNumbersUpTo]
  simpa only [Nat.primesLE] using
    Nat.smoothNumbersUpTo_card_le x (y + 1)

/-! ## Finite Euler products -/

/-- A box of exponent vectors, with each exponent between `0` and `K`. -/
abbrev ExponentBox (P : Finset ℕ) (K : ℕ) :=
  (p : P) → Fin (K + 1)

/-- The integer represented by an exponent vector. -/
def exponentProduct (P : Finset ℕ) {K : ℕ} (e : ExponentBox P K) : ℕ :=
  ∏ p : P, (p : ℕ) ^ (e p : ℕ)

/-- A finite Euler product with local geometric sums truncated at exponent
`K`. -/
def finiteEulerBox (P : Finset ℕ) (K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P, ∑ e ∈ Finset.range (K + 1), w p ^ e

/-- Expanding the product of finite geometric sums gives the sum over all
bounded exponent vectors. -/
lemma sum_exponentBox_eq_finiteEulerBox (P : Finset ℕ) (K : ℕ)
    (w : ℕ → ℝ) :
    (∑ e : ExponentBox P K, ∏ p : P, w p ^ (e p : ℕ)) =
      finiteEulerBox P K w := by
  unfold finiteEulerBox
  rw [← Finset.prod_attach]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  exact
    (Fintype.prod_sum
      (fun p : P ↦ fun e : Fin (K + 1) ↦ w p ^ (e : ℕ))).symm

/-- Cardinality of the exponent box. -/
lemma card_exponentBox (P : Finset ℕ) (K : ℕ) :
    Fintype.card (ExponentBox P K) = (K + 1) ^ P.card := by
  simp

end

end Erdos49

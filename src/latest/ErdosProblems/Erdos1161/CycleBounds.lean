import ErdosProblems.Erdos1161.CycleIndex
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Finite cycle-count bounds for Erdős Problem 1161

This file packages the cycle-count estimates used in the large-order
anticoncentration argument.  All quantities are finite cardinalities or exact
rational normalizations; no probability space is introduced.
-/

open scoped BigOperators

namespace Erdos1161

noncomputable section

/-! ## Total cycle count and its finite fibers -/

/-- The number of cycles, including fixed points, of a permutation. -/
def totalCycleCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (fullCycleType σ).card

/-- The number of permutations of `Fin n` having exactly `ell` cycles. -/
def exactCycleCount (n ell : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ ↦ totalCycleCount σ = ell)).card

/-- Permutations with `ell` cycles, all of whose cycle lengths lie in `I`. -/
def restrictedCycleCount (n ell : ℕ) (I : Finset ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ ↦ (fullCycleType σ).card = ell ∧
      ∀ j ∈ fullCycleType σ, j ∈ I)).card

/-- Permutations of order exactly `m` with exactly `ell` cycles. -/
def cycleOrderCount (n m ell : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ ↦ orderOf σ = m ∧ totalCycleCount σ = ell)).card

/-- Permutations whose order is divisible by `m` and which have exactly
`ell` cycles. -/
def cycleOrderMultipleCount (n m ell : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ ↦ m ∣ orderOf σ ∧ totalCycleCount σ = ell)).card

/-- Permutations whose order divides `m` and which have exactly `ell`
cycles. -/
def cycleOrderDividesCount (n m ell : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ ↦ orderOf σ ∣ m ∧ totalCycleCount σ = ell)).card

theorem restrictedCycleCount_le_exactCycleCount (n ell : ℕ) (I : Finset ℕ) :
    restrictedCycleCount n ell I ≤ exactCycleCount n ell := by
  apply Finset.card_le_card
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨Finset.mem_univ _, hσ.2.1⟩

theorem cycleOrderCount_le_exactCycleCount (n m ell : ℕ) :
    cycleOrderCount n m ell ≤ exactCycleCount n ell := by
  apply Finset.card_le_card
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨Finset.mem_univ _, hσ.2.2⟩

theorem cycleOrderCount_le_cycleOrderDividesCount (n m ell : ℕ) :
    cycleOrderCount n m ell ≤ cycleOrderDividesCount n m ell := by
  apply Finset.card_le_card
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨Finset.mem_univ _, hσ.2.1 ▸ dvd_rfl, hσ.2.2⟩

theorem cycleOrderCount_le_cycleOrderMultipleCount (n m ell : ℕ) :
    cycleOrderCount n m ell ≤ cycleOrderMultipleCount n m ell := by
  apply Finset.card_le_card
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨Finset.mem_univ _, hσ.2.1 ▸ dvd_rfl, hσ.2.2⟩

/-- For positive `m`, restricting all cycle lengths to the divisors of `m`
is exactly the event that the permutation order divides `m`. -/
theorem restrictedCycleCount_divisors_eq_cycleOrderDividesCount
    {n m ell : ℕ} (hm : m ≠ 0) :
    restrictedCycleCount n ell m.divisors = cycleOrderDividesCount n m ell := by
  apply congrArg Finset.card
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [orderOf_dvd_iff_forall_mem_fullCycleType_dvd]
  simp only [Nat.mem_divisors]
  constructor
  · rintro ⟨hcard, hdiv⟩
    exact ⟨fun j hj ↦ (hdiv j hj).1, hcard⟩
  · rintro ⟨hdiv, hcard⟩
    exact ⟨hcard, fun j hj ↦ ⟨hdiv j hj, hm⟩⟩

/-- The finite harmonic sum over the positive divisors of `m`. -/
def divisorReciprocalSum (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (d : ℝ)⁻¹

theorem divisorReciprocalSum_eq_divisorSum_div (m : ℕ) (hm : m ≠ 0) :
    divisorReciprocalSum m =
      (ArithmeticFunction.sigma 1 m : ℝ) / (m : ℝ) := by
  rw [divisorReciprocalSum, ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [pow_one]
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  rw [Nat.cast_div hdvd (by exact_mod_cast hdpos.ne')]
  field_simp

/-! ## A deterministic few-cycle bound -/

/-- Each cycle length is at most the degree. -/
theorem mem_fullCycleType_le_degree {n j : ℕ} {σ : Equiv.Perm (Fin n)}
    (hj : j ∈ fullCycleType σ) : j ≤ n := by
  rw [← sum_fullCycleType σ]
  exact Multiset.le_sum_of_mem hj

/-- The order of a permutation is at most the product of its cycle lengths,
and hence at most `n` raised to the number of cycles. -/
theorem orderOf_le_pow_totalCycleCount {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    orderOf σ ≤ n ^ totalCycleCount σ := by
  have hprod : (fullCycleType σ).prod ≤ n ^ (fullCycleType σ).card :=
    Multiset.prod_le_pow_card _ n fun j hj ↦ mem_fullCycleType_le_degree hj
  have hdvd : orderOf σ ∣ (fullCycleType σ).prod := by
    rw [← lcm_fullCycleType]
    exact (Multiset.lcm_dvd).2 fun _ hj ↦ Multiset.dvd_prod hj
  exact (Nat.le_of_dvd (Multiset.prod_pos fun j hj ↦
    Nat.zero_lt_one.trans_le (one_le_of_mem_fullCycleType hj)) hdvd).trans hprod

/-- In particular, an order larger than `n^ell` cannot occur on `ell`
cycles.  This is the emptiness observation used for the middle cycle-count
regime in the large-order proof. -/
theorem cycleOrderCount_eq_zero_of_pow_lt {n m ell : ℕ}
    (hlarge : n ^ ell < m) : cycleOrderCount n m ell = 0 := by
  rw [cycleOrderCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _
  rintro ⟨horder, hcycles⟩
  have hbound := orderOf_le_pow_totalCycleCount σ
  rw [horder, hcycles] at hbound
  omega

/-- The unsigned first-kind Stirling generating polynomial, evaluated in an
arbitrary commutative semiring. -/
def stirlingCycleGeneratingSum {R : Type*} [CommSemiring R] (n : ℕ) (z : R) : R :=
  ∑ ell ∈ Finset.range (n + 1), (Nat.stirlingFirst n ell : R) * z ^ ell

theorem stirlingCycleGeneratingSum_zero {R : Type*} [CommSemiring R] (z : R) :
    stirlingCycleGeneratingSum 0 z = 1 := by
  simp [stirlingCycleGeneratingSum]

theorem stirlingCycleGeneratingSum_succ {R : Type*} [CommSemiring R]
    (n : ℕ) (z : R) :
    stirlingCycleGeneratingSum (n + 1) z =
      (z + n) * stirlingCycleGeneratingSum n z := by
  cases n with
  | zero => norm_num [stirlingCycleGeneratingSum, Nat.stirlingFirst,
      Finset.sum_range_succ]
  | succ n =>
      have hshift :
          (∑ k ∈ Finset.range (n + 2),
              (Nat.stirlingFirst (n + 1) (k + 1) : R) * z ^ (k + 1)) =
            ∑ k ∈ Finset.range (n + 2),
              (Nat.stirlingFirst (n + 1) k : R) * z ^ k := by
        conv_lhs => rw [Finset.sum_range_succ]
        conv_rhs => rw [Finset.sum_range_succ']
        have hend : Nat.stirlingFirst (n + 1) (n + 2) = 0 :=
          Nat.stirlingFirst_eq_zero_of_lt (by omega)
        simp [hend]
      rw [stirlingCycleGeneratingSum, stirlingCycleGeneratingSum,
        Finset.sum_range_succ']
      simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, zero_mul]
      have hrec (k : ℕ) :
          Nat.stirlingFirst (n + 2) (k + 1) =
            (n + 1) * Nat.stirlingFirst (n + 1) (k + 1) +
              Nat.stirlingFirst (n + 1) k := by
        exact Nat.stirlingFirst_succ_succ (n + 1) k
      simp_rw [hrec, Nat.cast_add, Nat.cast_mul, add_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hshift]
      have hz :
          (∑ k ∈ Finset.range (n + 2),
              (Nat.stirlingFirst (n + 1) k : R) * z ^ (k + 1)) =
            z * ∑ k ∈ Finset.range (n + 2),
              (Nat.stirlingFirst (n + 1) k : R) * z ^ k := by
        rw [mul_comm z, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]
        ring
      rw [hz]
      push_cast
      ring

/-- The exact cycle-count generating identity
`sum_ell s(n,ell) z^ell = z(z+1)...(z+n-1)`. -/
theorem stirlingCycleGeneratingSum_eq_prod {R : Type*} [CommSemiring R]
    (n : ℕ) (z : R) :
    stirlingCycleGeneratingSum n z =
      ∏ j ∈ Finset.range n, (z + j) := by
  induction n with
  | zero => simp [stirlingCycleGeneratingSum]
  | succ n ih =>
      rw [stirlingCycleGeneratingSum_succ, ih, Finset.prod_range_succ]
      ring

theorem prod_two_add_range (n : ℕ) :
    (∏ j ∈ Finset.range n, (2 + j)) = (n + 1).factorial := by
  rw [← Nat.ascFactorial_eq_prod_range]
  simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n

/-- At `z=2`, the generating function is exactly `(n+1)!`. -/
theorem stirlingCycleGeneratingSum_two (n : ℕ) :
    stirlingCycleGeneratingSum n (2 : ℕ) = (n + 1).factorial := by
  rw [stirlingCycleGeneratingSum_eq_prod]
  simpa only [Nat.cast_id] using prod_two_add_range n

/-- The number of cycle-count coefficients above the threshold `t`. -/
def stirlingCycleTail (n t : ℕ) : ℕ :=
  ∑ ell ∈ (Finset.range (n + 1)).filter (fun ell ↦ t < ell),
    Nat.stirlingFirst n ell

/-- Finite Markov inequality at `z=2`.  After dividing by `n!`, this is
`P(c(π_n)>t) ≤ (n+1)/2^t`. -/
theorem two_pow_mul_stirlingCycleTail_le (n t : ℕ) :
    2 ^ t * stirlingCycleTail n t ≤ (n + 1).factorial := by
  rw [stirlingCycleTail, Finset.mul_sum]
  calc
    (∑ ell ∈ (Finset.range (n + 1)).filter (fun ell ↦ t < ell),
        2 ^ t * Nat.stirlingFirst n ell) ≤
        ∑ ell ∈ (Finset.range (n + 1)).filter (fun ell ↦ t < ell),
          Nat.stirlingFirst n ell * 2 ^ ell := by
      apply Finset.sum_le_sum
      intro ell hell
      rw [Finset.mem_filter] at hell
      have hp : 2 ^ t ≤ 2 ^ ell :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.le_of_lt hell.2)
      simpa [mul_comm] using Nat.mul_le_mul_right (Nat.stirlingFirst n ell) hp
    _ ≤ ∑ ell ∈ Finset.range (n + 1), Nat.stirlingFirst n ell * 2 ^ ell := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (n + 1).factorial := stirlingCycleGeneratingSum_two n

end

end Erdos1161

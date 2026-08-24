import Mathlib

/-!
An interval bound forces small doubling at a high-fold dyadic scale.
All scale selection is finite; no asymptotic small-doubling input is assumed.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem nsmul_subset_nat_interval (A : Finset ℤ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (h : ℕ) :
    h • A ⊆ Finset.Icc 0 ((h * N : ℕ) : ℤ) := by
  induction h with
  | zero =>
    intro x hx
    change x ∈ ({0} : Finset ℤ) at hx
    have hx0 : x = 0 := Finset.mem_singleton.mp hx
    subst x
    simp
  | succ h ih =>
    intro x hx
    rw [succ_nsmul] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨hu0, hu1⟩ := Finset.mem_Icc.mp (ih hu)
    obtain ⟨hv0, hv1⟩ := Finset.mem_Icc.mp (hA hv)
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · push_cast at hu1 ⊢
      nlinarith

theorem card_nsmul_le_nat_interval (A : Finset ℤ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (h : ℕ) :
    (h • A).card ≤ h * N + 1 := by
  have hlen : (Finset.Icc (0 : ℤ) ((h * N : ℕ) : ℤ)).card = h * N + 1 := by
    rw [Int.card_Icc, sub_zero]
    rw [show ((h * N : ℕ) : ℤ) + 1 = ((h * N + 1 : ℕ) : ℤ) by
      simp only [Nat.cast_add, Nat.cast_one]]
    exact Int.toNat_natCast _
  exact (Finset.card_le_card (nsmul_subset_nat_interval A N hA h)).trans_eq hlen

/-- If every step grew by more than `K`, the endpoint would exceed its
geometric-growth budget. -/
theorem exists_slow_multiplicative_step (f : ℕ → ℕ) (a t K : ℕ)
    (ht : 0 < t) (hbudget : f (a + t) ≤ K ^ t * f a) :
    ∃ j < t, f (a + j + 1) ≤ K * f (a + j) := by
  by_contra hnone
  push Not at hnone
  have hlow (n : ℕ) (hn : n ≤ t) : K ^ n * f a ≤ f (a + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        K ^ (n + 1) * f a = K * (K ^ n * f a) := by rw [pow_succ]; ring
        _ ≤ K * f (a + n) := Nat.mul_le_mul_left K (ih (by omega))
        _ ≤ f (a + (n + 1)) := by simpa only [Nat.add_assoc] using (hnone n (by omega)).le
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hstrict : K ^ (n + 1) * f a < f (a + (n + 1)) := by
    calc
      K ^ (n + 1) * f a = K * (K ^ n * f a) := by rw [pow_succ]; ring
      _ ≤ K * f (a + n) := Nat.mul_le_mul_left K (hlow n (by omega))
      _ < f (a + (n + 1)) := by simpa only [Nat.add_assoc] using hnone n (by omega)
  exact (not_lt_of_ge (by simpa only [Nat.succ_eq_add_one] using hbudget)) hstrict

theorem dyadic_nsmul_succ (A : Finset ℤ) (k : ℕ) :
    (2 ^ (k + 1)) • A = (2 ^ k) • A + (2 ^ k) • A := by
  rw [pow_succ, mul_nsmul, two_nsmul]

/-- A finite dyadic scale with small doubling, from a cardinality budget. -/
theorem exists_dyadic_small_doubling (A : Finset ℤ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (hzero : 0 ∈ A)
    (a t K : ℕ) (ht : 0 < t) (hbudget : 2 ^ (a + t) * N + 1 ≤ K ^ t) :
    ∃ k, a ≤ k ∧ k < a + t ∧
      ((2 ^ k) • A + (2 ^ k) • A).card ≤ K * ((2 ^ k) • A).card := by
  let f : ℕ → ℕ := fun k => ((2 ^ k) • A).card
  have hf : 1 ≤ f a := Finset.card_pos.mpr ⟨0, Finset.zero_mem_nsmul hzero⟩
  have hend : f (a + t) ≤ K ^ t * f a := by
    calc
      f (a + t) ≤ 2 ^ (a + t) * N + 1 := card_nsmul_le_nat_interval A N hA _
      _ ≤ K ^ t := hbudget
      _ ≤ K ^ t * f a := by simpa only [mul_one] using Nat.mul_le_mul_left (K ^ t) hf
  obtain ⟨j, hj, hsmall⟩ := exists_slow_multiplicative_step f a t K ht hend
  refine ⟨a + j, by omega, by omega, ?_⟩
  change ((2 ^ (a + j + 1)) • A).card ≤ K * ((2 ^ (a + j)) • A).card at hsmall
  rwa [dyadic_nsmul_succ] at hsmall

theorem dyadic_polynomial_growth_budget (N b t : ℕ) (ht : 0 < t)
    (hN : N ≤ (2 ^ t) ^ b) :
    2 ^ (t + t) * N + 1 ≤ (2 ^ (b + 3)) ^ t := by
  let X := (2 ^ t) ^ (b + 2)
  have hX : 0 < X := by positivity
  have hpow : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ht
  have hupper : 2 ^ (t + t) * N ≤ X := by
    calc
      2 ^ (t + t) * N ≤ 2 ^ (t + t) * (2 ^ t) ^ b := Nat.mul_le_mul_left _ hN
      _ = X := by dsimp [X]; rw [pow_add, pow_add, pow_two]; ring
  have heq : (2 ^ (b + 3)) ^ t = X * 2 ^ t := by
    dsimp [X]
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [heq]
  nlinarith

/-- In a polynomial-sized ambient interval there is always a small-doubling
scale between `2^t` and `2^(2*t)`. The doubling constant depends only on `b`. -/
theorem exists_polynomial_window_small_doubling (A : Finset ℤ) (N b t : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (hzero : 0 ∈ A)
    (ht : 0 < t) (hN : N ≤ (2 ^ t) ^ b) :
    ∃ k, t ≤ k ∧ k < t + t ∧
      ((2 ^ k) • A + (2 ^ k) • A).card ≤
        2 ^ (b + 3) * ((2 ^ k) • A).card := by
  exact exists_dyadic_small_doubling A N hA hzero t t (2 ^ (b + 3)) ht
    (dyadic_polynomial_growth_budget N b t ht hN)

end Erdos587.CFP

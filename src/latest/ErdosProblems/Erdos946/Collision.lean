/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SieveSupply
import Mathlib.Algebra.Order.Group.Int.Sum

/-! # The prime-factor collision and its divisor-count consequence -/

open scoped BigOperators ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.Collision

noncomputable section

theorem sum_ge_oneHundredThirtySix_of_injective (f : Fin 16 → ℕ)
    (hpos : ∀ i, 0 < f i) (hinj : Function.Injective f) :
    136 ≤ ∑ i : Fin 16, f i := by
  let g : Fin 16 → ℤ := fun i ↦ (f i : ℤ)
  have hginj : Function.Injective g := fun i j h ↦ hinj (Int.ofNat_inj.mp h)
  let S := Finset.univ.image g
  have hcard : S.card = 16 := by
    rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin]
  have hbound : ∀ x ∈ S, (1 : ℤ) ≤ x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    change (1 : ℤ) ≤ (f i : ℤ)
    exact_mod_cast (Nat.succ_le_of_lt (hpos i))
  have hsum := Finset.sum_range_le_sum hbound
  rw [hcard] at hsum
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero] at hsum
  have hsumS : (∑ x ∈ S, x) = ∑ i : Fin 16, (f i : ℤ) := by
    exact Finset.sum_image (fun i _ j _ hij ↦ hginj hij)
  rw [hsumS] at hsum
  exact_mod_cast hsum

theorem exists_collision_of_sum_le (f : Fin 16 → ℕ)
    (hpos : ∀ i, 0 < f i) (hsum : (∑ i : Fin 16, f i) ≤ 130) :
    ∃ i j : Fin 16, i ≠ j ∧ f i = f j := by
  by_contra h
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  have hlarge := sum_ge_oneHundredThirtySix_of_injective f hpos hinj
  omega

theorem sigma_zero_eq_pow_cardFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    σ 0 n = 2 ^ Ω n := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn.ne_zero]
  have heq : (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
      ∏ _p ∈ n.primeFactors, (2 : ℕ) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  rw [heq, Finset.prod_const]
  congr 1
  rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hn.nodup_primeFactorsList]
  rfl

theorem cardFactors_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hpos : ∀ i ∈ s, f i ≠ 0) : Ω (∏ i ∈ s, f i) = ∑ i ∈ s, Ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ArithmeticFunction.cardFactors_mul (hpos i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))]

theorem exists_equal_sigma_of_squarefree_product (f : Fin 16 → ℕ)
    (hpos : ∀ i, 1 < f i) (hsq : Squarefree (∏ i, f i))
    (hcount : Ω (∏ i, f i) ≤ 130) :
    ∃ i j : Fin 16, i ≠ j ∧ σ 0 (f i) = σ 0 (f j) := by
  have hΩpos : ∀ i, 0 < Ω (f i) := fun i ↦
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (hpos i)
  rw [cardFactors_finset_prod _ _ (fun i _ ↦ (Nat.zero_lt_one.trans (hpos i)).ne')] at hcount
  obtain ⟨i, j, hij, hΩ⟩ := exists_collision_of_sum_le (fun i ↦ Ω (f i)) hΩpos hcount
  have hsqi : Squarefree (f i) := hsq.squarefree_of_dvd
    (Finset.dvd_prod_of_mem f (Finset.mem_univ i))
  have hsqj : Squarefree (f j) := hsq.squarefree_of_dvd
    (Finset.dvd_prod_of_mem f (Finset.mem_univ j))
  exact ⟨i, j, hij, by rw [sigma_zero_eq_pow_cardFactors_of_squarefree hsqi,
    sigma_zero_eq_pow_cardFactors_of_squarefree hsqj, hΩ]⟩

end

end Erdos946.Collision

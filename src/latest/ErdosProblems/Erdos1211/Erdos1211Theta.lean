import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import ErdosProblems.Erdos1211.Erdos1211RoughShell

open Finset BigOperators

namespace ThetaBound

def J : ℕ := 128

def C0 : ℕ := 256 * J

def cutoffQ : ℕ := 4 * C0 ^ 2

def factor (n : ℕ) : ℚ := ((n - 1 : ℕ) : ℚ) / n

def invFactor (n : ℕ) : ℚ := (n : ℚ) / (n - 1 : ℕ)

def compositeIndices (Q : ℕ) : Finset ℕ :=
  (Icc 2 Q).filter fun n ↦ ¬n.Prime

lemma factor_eq_one_sub_inv {n : ℕ} (hn : 1 ≤ n) :
    factor n = 1 - (n : ℚ)⁻¹ := by
  simp only [factor]
  rw [Nat.cast_sub hn]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

lemma factor_pos {n : ℕ} (hn : 2 ≤ n) : 0 < factor n := by
  simp only [factor]
  exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

lemma factor_le_one {n : ℕ} : factor n ≤ 1 := by
  simp only [factor]
  by_cases hn : n = 0
  · simp [hn]
  exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    (Nat.cast_le.mpr (Nat.sub_le n 1))

lemma one_le_invFactor {n : ℕ} (hn : 2 ≤ n) : 1 ≤ invFactor n := by
  simp only [invFactor]
  apply (one_le_div (Nat.cast_pos.mpr (by omega))).mpr
  exact Nat.cast_le.mpr (Nat.sub_le n 1)

lemma factor_mul_invFactor {n : ℕ} (hn : 2 ≤ n) :
    factor n * invFactor n = 1 := by
  simp only [factor, invFactor]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn10 : (((n - 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  field_simp

lemma full_factor_product (Q : ℕ) (hQ : 2 ≤ Q) :
    (∏ n ∈ Icc 2 Q, factor n) = 1 / Q := by
  induction Q, hQ using Nat.le_induction with
  | base => norm_num [factor]
  | succ Q hQ ih =>
      rw [Finset.prod_Icc_succ_top hQ.step, ih]
      simp only [factor]
      rw [Nat.add_sub_cancel]
      push_cast
      have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
      have hQ1 : ((Q + 1 : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (show Q + 1 ≠ 0 by omega)
      field_simp

lemma primorial_totient_ratio (Q : ℕ) :
    (((primorial Q).totient : ℚ) / (primorial Q : ℚ)) =
      ∏ p ∈ Nat.primesLE Q, factor p := by
  have hM : ((primorial Q : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (primorial_pos Q).ne'
  rw [Nat.totient_eq_mul_prod_factors, primeFactors_primorial]
  rw [mul_div_cancel_left₀ _ hM]
  apply Finset.prod_congr rfl
  intro p hp
  exact (factor_eq_one_sub_inv (Nat.prime_of_mem_primesLE hp).one_le).symm

lemma split_full_factor_product (Q : ℕ) :
    (∏ n ∈ Icc 2 Q, factor n) =
      (∏ p ∈ Nat.primesLE Q, factor p) *
        ∏ n ∈ compositeIndices Q, factor n := by
  rw [Nat.primesLE_eq_filter_Icc_two]
  exact (Finset.prod_filter_mul_prod_filter_not (Icc 2 Q) Nat.Prime factor).symm

lemma composite_factor_mul_inv (Q : ℕ) :
    (∏ n ∈ compositeIndices Q, factor n) *
      (∏ n ∈ compositeIndices Q, invFactor n) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro n hn
  have hn' := (Finset.mem_filter.mp hn).1
  exact factor_mul_invFactor (Finset.mem_Icc.mp hn').1

lemma primorial_ratio_mul_eq_composite_inv (Q : ℕ) (hQ : 2 ≤ Q) :
    (Q : ℚ) * (((primorial Q).totient : ℚ) / (primorial Q : ℚ)) =
      ∏ n ∈ compositeIndices Q, invFactor n := by
  let P : ℚ := ∏ p ∈ Nat.primesLE Q, factor p
  let C : ℚ := ∏ n ∈ compositeIndices Q, factor n
  let I : ℚ := ∏ n ∈ compositeIndices Q, invFactor n
  have hfull : P * C = 1 / (Q : ℚ) := by
    rw [← split_full_factor_product Q]
    exact full_factor_product Q hQ
  have hCI : C * I = 1 := composite_factor_mul_inv Q
  have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hratio :
      (((primorial Q).totient : ℚ) / (primorial Q : ℚ)) = P :=
    primorial_totient_ratio Q
  rw [hratio]
  dsimp only [P, C, I] at hfull hCI ⊢
  have hQPC : (Q : ℚ) * (P * C) = 1 := by
    rw [hfull]
    field_simp
  calc
    (Q : ℚ) * P = (Q : ℚ) * P * (C * I) := by rw [hCI, mul_one]
    _ = ((Q : ℚ) * (P * C)) * I := by ring
    _ = I := by rw [hQPC, one_mul]

def evenCompositeIndices (m : ℕ) : Finset ℕ :=
  (Icc 2 m).image fun k ↦ 2 * k

lemma evenCompositeIndices_subset (m : ℕ) :
    evenCompositeIndices m ⊆ compositeIndices (2 * m) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
  have hk' := Finset.mem_Icc.mp hk
  simp only [compositeIndices, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    Nat.not_prime_mul (by omega) (by omega)⟩

lemma evenComposite_product (m : ℕ) :
    (∏ n ∈ evenCompositeIndices m, invFactor n) =
      ∏ k ∈ Icc 2 m, invFactor (2 * k) := by
  rw [evenCompositeIndices, Finset.prod_image]
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left (by omega) hab

lemma even_inv_product_le_composite_inv (m : ℕ) :
    (∏ k ∈ Icc 2 m, invFactor (2 * k)) ≤
      ∏ n ∈ compositeIndices (2 * m), invFactor n := by
  rw [← evenComposite_product]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · exact evenCompositeIndices_subset m
  · intro n hn
    exact (one_le_invFactor (Finset.mem_Icc.mp
      ((Finset.mem_filter.mp (evenCompositeIndices_subset m hn)).1)).1).trans'
        zero_le_one
  · intro n hn hneven
    have hnIcc := (Finset.mem_filter.mp hn).1
    exact one_le_invFactor (Finset.mem_Icc.mp hnIcc).1

lemma ratio_succ_le_even_invFactor_sq {k : ℕ} (hk : 2 ≤ k) :
    ((k + 1 : ℕ) : ℚ) / k ≤ invFactor (2 * k) ^ 2 := by
  simp only [invFactor]
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have htwoKsub0 : (((2 * k - 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (show 2 * k - 1 ≠ 0 by omega)
  push_cast
  field_simp
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hid : ((k : ℚ) + 1) * (2 * k - 1) ^ 2 =
      4 * (k : ℚ) ^ 3 - 3 * k + 1 := by ring
  have hcast : (((2 * k - 1 : ℕ) : ℚ)) = 2 * (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hcast, hid]
  nlinarith

lemma ratio_product_telescope (m : ℕ) (hm : 2 ≤ m) :
    (∏ k ∈ Icc 2 m, (((k + 1 : ℕ) : ℚ) / k)) =
      ((m + 1 : ℕ) : ℚ) / 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top hm.step, ih]
      push_cast
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hm10 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp

lemma even_inv_product_sq_lower (m : ℕ) (hm : 2 ≤ m) :
    (((∏ k ∈ Icc 2 m, invFactor (2 * k)) : ℚ) ^ 2) ≥
      ((m + 1 : ℕ) : ℚ) / 2 := by
  have hprod :
      (∏ k ∈ Icc 2 m, (((k + 1 : ℕ) : ℚ) / k)) ≤
        ∏ k ∈ Icc 2 m, invFactor (2 * k) ^ 2 := by
    apply Finset.prod_le_prod
    · intro k hk
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro k hk
      exact ratio_succ_le_even_invFactor_sq (Finset.mem_Icc.mp hk).1
  have htel := ratio_product_telescope m hm
  calc
    ((m + 1 : ℕ) : ℚ) / 2 =
        ∏ k ∈ Icc 2 m, (((k + 1 : ℕ) : ℚ) / k) := by
      exact htel.symm
    _ ≤ ∏ k ∈ Icc 2 m, invFactor (2 * k) ^ 2 := hprod
    _ = (∏ k ∈ Icc 2 m, invFactor (2 * k)) ^ 2 := by
      exact Finset.prod_pow (Icc 2 m) 2 (fun k ↦ invFactor (2 * k))

lemma cast_lt_even_inv_product {C m : ℕ} (hm : 2 ≤ m)
    (hC : (C : ℚ) ^ 2 < ((m + 1 : ℕ) : ℚ) / 2) :
    (C : ℚ) < ∏ k ∈ Icc 2 m, invFactor (2 * k) := by
  have hsq := even_inv_product_sq_lower m hm
  have hnonneg : 0 ≤ ∏ k ∈ Icc 2 m, invFactor (2 * k) := by
    apply Finset.prod_nonneg
    intro k hk
    exact (one_le_invFactor (by
      have hk' := Finset.mem_Icc.mp hk
      omega)).trans' (by norm_num)
  have hCnonneg : (0 : ℚ) ≤ C := Nat.cast_nonneg C
  nlinarith

theorem cast_lt_two_mul_primorial_totient_ratio {C m : ℕ} (hm : 2 ≤ m)
    (hC : (C : ℚ) ^ 2 < ((m + 1 : ℕ) : ℚ) / 2) :
    (C : ℚ) <
      ((2 * m : ℕ) : ℚ) *
        (((primorial (2 * m)).totient : ℚ) / (primorial (2 * m) : ℚ)) := by
  calc
    (C : ℚ) < ∏ k ∈ Icc 2 m, invFactor (2 * k) :=
      cast_lt_even_inv_product hm hC
    _ ≤ ∏ n ∈ compositeIndices (2 * m), invFactor n :=
      even_inv_product_le_composite_inv m
    _ = ((2 * m : ℕ) : ℚ) *
        (((primorial (2 * m)).totient : ℚ) / (primorial (2 * m) : ℚ)) := by
      rw [primorial_ratio_mul_eq_composite_inv]
      omega

theorem C_mul_primorial_le_two_mul_totient {C m : ℕ} (hm : 2 ≤ m)
    (hC : (C : ℚ) ^ 2 < ((m + 1 : ℕ) : ℚ) / 2) :
    C * primorial (2 * m) ≤ (2 * m) * (primorial (2 * m)).totient := by
  have hratio := cast_lt_two_mul_primorial_totient_ratio hm hC
  have hMposQ : (0 : ℚ) < (primorial (2 * m) : ℕ) :=
    Nat.cast_pos.mpr (primorial_pos (2 * m))
  have hcross :
      (C : ℚ) * (primorial (2 * m) : ℕ) <
        ((2 * m : ℕ) : ℚ) * ((primorial (2 * m)).totient : ℚ) := by
    calc
      (C : ℚ) * (primorial (2 * m) : ℕ) <
          (((2 * m : ℕ) : ℚ) *
            (((primorial (2 * m)).totient : ℚ) /
              (primorial (2 * m) : ℚ))) * (primorial (2 * m) : ℕ) :=
        mul_lt_mul_of_pos_right hratio hMposQ
      _ = ((2 * m : ℕ) : ℚ) * ((primorial (2 * m)).totient : ℚ) := by
        field_simp
  exact_mod_cast hcross.le

theorem finite_theta_lower_bound :
    C0 * RoughShellCount.roughModulus cutoffQ ≤
      cutoffQ * (RoughShellCount.roughModulus cutoffQ).totient := by
  have hC0 : 0 < C0 := by norm_num [C0, J]
  have hm : 2 ≤ 2 * C0 ^ 2 := by norm_num [C0, J]
  have hC : (C0 : ℚ) ^ 2 < (((2 * C0 ^ 2 + 1 : ℕ) : ℚ) / 2) := by
    norm_num [C0, J]
  have h := C_mul_primorial_le_two_mul_totient
    (C := C0) (m := 2 * C0 ^ 2) hm hC
  have hrough : RoughShellCount.roughModulus cutoffQ = primorial cutoffQ :=
    (primorial_eq_prod_primesLE cutoffQ).symm
  rw [hrough]
  have harg : 2 * (2 * C0 ^ 2) = cutoffQ := by
    simp only [cutoffQ]
    ring
  rw [← harg]
  exact h

end ThetaBound

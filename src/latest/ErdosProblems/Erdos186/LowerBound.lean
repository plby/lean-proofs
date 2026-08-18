/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Foundations

/-!
# Erdős Problem 186: Bosznay's lower bound

We formalize Bosznay's construction

`b(q,i) = i * q^3 + i(i+1)/2`, for `1 ≤ i < q`.

The second term is represented by the recursive triangular-number function,
which lets us do the no-carry and strict-convexity arguments entirely in
natural and integer arithmetic.  The final result is the lower half of the
resolution of Erdős Problem 186:

`N^(1/4) = O(F(N))`.
-/

namespace Erdos186

open Finset Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

/-- The triangular number `i(i+1)/2`, defined without natural-number
division in order to expose its recursion to the simplifier. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | i + 1 => triangular i + (i + 1)

@[simp] theorem triangular_zero : triangular 0 = 0 := rfl

@[simp] theorem triangular_succ (i : ℕ) :
    triangular (i + 1) = triangular i + (i + 1) := rfl

/-- The division-free closed formula for a triangular number. -/
theorem two_mul_triangular (i : ℕ) :
    2 * triangular i = i * (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [triangular_succ]
      rw [Nat.mul_add, ih]
      ring

theorem triangular_mono : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro i
  simp

theorem triangular_le_sq {i : ℕ} (hi : 1 ≤ i) :
    triangular i ≤ i ^ 2 := by
  have hformula := two_mul_triangular i
  nlinarith

/-- The `i`-th element of Bosznay's construction at scale `q`. -/
def bosznayValue (q i : ℕ) : ℕ :=
  i * q ^ 3 + triangular i

/-- Bosznay's finite construction at scale `q`. -/
def bosznaySet (q : ℕ) : Finset ℕ :=
  (Finset.Ico 1 q).image (bosznayValue q)

theorem bosznayValue_strictMono {q : ℕ} (hq : 0 < q) :
    StrictMono (bosznayValue q) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hq3 : 0 < q ^ 3 := pow_pos hq 3
  have hmul : i * q ^ 3 < (i + 1) * q ^ 3 := by
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self i) hq3
  change i * q ^ 3 + triangular i <
    (i + 1) * q ^ 3 + triangular (i + 1)
  exact Nat.add_lt_add_of_lt_of_le hmul
    (triangular_mono (Nat.le_succ i))

theorem bosznayValue_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (bosznayValue q) :=
  (bosznayValue_strictMono hq).injective

/-- The construction has exactly `q-1` elements. -/
@[simp] theorem card_bosznaySet {q : ℕ} (hq : 0 < q) :
    (bosznaySet q).card = q - 1 := by
  rw [bosznaySet, Finset.card_image_of_injective _ (bosznayValue_injective hq)]
  simp

theorem triangular_lt_sq {q i : ℕ} (hi1 : 1 ≤ i) (hiq : i < q) :
    triangular i < q ^ 2 := by
  calc
    triangular i ≤ i ^ 2 := triangular_le_sq hi1
    _ < q ^ 2 := by nlinarith

/-- Every displayed Bosznay value lies in `[1,q^4]`. -/
theorem bosznayValue_mem_Icc {q i : ℕ} (hq : 2 ≤ q)
    (hi : i ∈ Finset.Ico 1 q) :
    bosznayValue q i ∈ Finset.Icc 1 (q ^ 4) := by
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hiq : i < q := (Finset.mem_Ico.mp hi).2
  have hqpos : 0 < q := by omega
  have hq3pos : 0 < q ^ 3 := pow_pos hqpos 3
  have hil : i ≤ q - 1 := by omega
  have ht : triangular i < q ^ 3 := by
    have h₁ := triangular_lt_sq hi1 hiq
    have h₂ : q ^ 2 < q ^ 3 := by
      rw [show q ^ 3 = q ^ 2 * q by ring]
      nlinarith [pow_pos hqpos 2]
    exact h₁.trans h₂
  rw [Finset.mem_Icc]
  constructor
  · unfold bosznayValue
    have : 0 < i * q ^ 3 := Nat.mul_pos (by omega) hq3pos
    omega
  · unfold bosznayValue
    calc
      i * q ^ 3 + triangular i ≤ (q - 1) * q ^ 3 + q ^ 3 := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right (q ^ 3) hil)
          (Nat.le_of_lt ht)
      _ = q ^ 4 := by
        have : q - 1 + 1 = q := by omega
        calc
          (q - 1) * q ^ 3 + q ^ 3 = (q - 1 + 1) * q ^ 3 := by ring
          _ = q ^ 4 := by rw [this]; ring

/-- The whole construction lies in the required interval. -/
theorem bosznaySet_subset_Icc {q : ℕ} (hq : 2 ≤ q) :
    bosznaySet q ⊆ Finset.Icc 1 (q ^ 4) := by
  intro x hx
  rw [bosznaySet] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact bosznayValue_mem_Icc hq hi

/-- A uniform upper bound for a sum of the triangular remainders.  This is
the quantitative input in the base-`q^3` no-carry argument. -/
theorem sum_triangular_lt_cube {q : ℕ} (hq : 2 ≤ q) {T : Finset ℕ}
    (hT : T ⊆ Finset.Ico 1 q) (hTne : T.Nonempty) :
    T.sum triangular < q ^ 3 := by
  have hsum : T.sum triangular < T.sum (fun _ ↦ q ^ 2) := by
    apply Finset.sum_lt_sum_of_nonempty hTne
    intro i hi
    have hi' := Finset.mem_Ico.mp (hT hi)
    exact triangular_lt_sq hi'.1 hi'.2
  have hcard : T.card ≤ q - 1 := by
    calc
      T.card ≤ (Finset.Ico 1 q).card := Finset.card_le_card hT
      _ = q - 1 := by simp
  calc
    T.sum triangular < T.card * q ^ 2 := by simpa using hsum
    _ ≤ (q - 1) * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hcard
    _ < q ^ 3 := by
      have hqpos : 0 < q := by omega
      calc
        (q - 1) * q ^ 2 < q * q ^ 2 :=
          Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hqpos 2)
        _ = q ^ 3 := by ring

theorem card_mul_triangular_lt_cube {q i : ℕ} (hq : 2 ≤ q)
    {T : Finset ℕ} (hT : T ⊆ Finset.Ico 1 q)
    (hi : i ∈ Finset.Ico 1 q) :
    T.card * triangular i < q ^ 3 := by
  have hcard : T.card ≤ q - 1 := by
    calc
      T.card ≤ (Finset.Ico 1 q).card := Finset.card_le_card hT
      _ = q - 1 := by simp
  have hit := Finset.mem_Ico.mp hi
  have htri : triangular i < q ^ 2 := triangular_lt_sq hit.1 hit.2
  have hqpos : 0 < q := by omega
  calc
    T.card * triangular i < q * q ^ 2 := by
      exact Nat.mul_lt_mul_of_le_of_lt (hcard.trans (Nat.sub_le q 1)) htri hqpos
    _ = q ^ 3 := by ring

/-- Equality of averages in the Bosznay set has no carry from the triangular
coordinate into the linear coordinate. -/
theorem bosznay_no_carry {q i : ℕ} (hq : 2 ≤ q)
    (hi : i ∈ Finset.Ico 1 q) {T : Finset ℕ}
    (hT : T ⊆ Finset.Ico 1 q) (hTcard : 2 ≤ T.card)
    (havg : T.card * bosznayValue q i = T.sum (bosznayValue q)) :
    T.card * i = T.sum id ∧
      T.card * triangular i = T.sum triangular := by
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hleft : T.card * triangular i < q ^ 3 :=
    card_mul_triangular_lt_cube hq hT hi
  have hright : T.sum triangular < q ^ 3 :=
    sum_triangular_lt_cube hq hT hTne
  have hexpand :
      (T.card * i) * q ^ 3 + T.card * triangular i =
        (T.sum id) * q ^ 3 + T.sum triangular := by
    calc
      (T.card * i) * q ^ 3 + T.card * triangular i =
          T.card * bosznayValue q i := by
        simp only [bosznayValue, Nat.mul_add]
        ring
      _ = T.sum (bosznayValue q) := havg
      _ = (T.sum id) * q ^ 3 + T.sum triangular := by
        change (∑ x ∈ T, (x * q ^ 3 + triangular x)) = _
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        rfl
  have hrem : T.card * triangular i = T.sum triangular := by
    have hmod := congrArg (fun n : ℕ ↦ n % q ^ 3) hexpand
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hleft,
      Nat.mod_eq_of_lt hright] using hmod
  constructor
  · have hcoeff : (T.card * i) * q ^ 3 = (T.sum id) * q ^ 3 := by
      exact Nat.add_right_cancel (hexpand.trans (congrArg ((T.sum id) * q ^ 3 + ·) hrem.symm))
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega : 0 < q) 3) hcoeff
  · exact hrem

/-- Strict convexity of the triangular sequence: equal first and second
moments force every index to equal the proposed mean. -/
theorem eq_of_sum_id_and_triangular {i : ℕ} {T : Finset ℕ}
    (hlin : T.card * i = T.sum id)
    (htri : T.card * triangular i = T.sum triangular) :
    ∀ j ∈ T, j = i := by
  have hlinZ : ((T.card : ℤ) * (i : ℤ)) = ∑ j ∈ T, (j : ℤ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hlin
  have htriZ : ((T.card : ℤ) * (triangular i : ℤ)) =
      ∑ j ∈ T, (triangular j : ℤ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast htri
  have hsquareZ : ((T.card : ℤ) * (i : ℤ) ^ 2) =
      ∑ j ∈ T, (j : ℤ) ^ 2 := by
    have hiFormula : (2 : ℤ) * (triangular i : ℤ) =
        (i : ℤ) * ((i : ℤ) + 1) := by
      exact_mod_cast two_mul_triangular i
    have hsumFormula :
        ∑ j ∈ T, (2 : ℤ) * (triangular j : ℤ) =
          ∑ j ∈ T, (j : ℤ) * ((j : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact_mod_cast two_mul_triangular j
    rw [← Finset.mul_sum] at hsumFormula
    rw [← htriZ] at hsumFormula
    have hmoment :
        (T.card : ℤ) * ((i : ℤ) * ((i : ℤ) + 1)) =
          ∑ j ∈ T, (j : ℤ) * ((j : ℤ) + 1) := by
      calc
        (T.card : ℤ) * ((i : ℤ) * ((i : ℤ) + 1)) =
            2 * ((T.card : ℤ) * (triangular i : ℤ)) := by
          rw [← hiFormula]
          ring
        _ = ∑ j ∈ T, (j : ℤ) * ((j : ℤ) + 1) := hsumFormula
    calc
      (T.card : ℤ) * (i : ℤ) ^ 2 =
          (T.card : ℤ) * ((i : ℤ) * ((i : ℤ) + 1)) -
            (T.card : ℤ) * (i : ℤ) := by ring
      _ = (∑ j ∈ T, (j : ℤ) * ((j : ℤ) + 1)) -
            ∑ j ∈ T, (j : ℤ) := by rw [hmoment, ← hlinZ]
      _ = ∑ j ∈ T, (j : ℤ) ^ 2 := by
        have hdecomp :
            (∑ j ∈ T, (j : ℤ) * ((j : ℤ) + 1)) =
              (∑ j ∈ T, (j : ℤ) ^ 2) + ∑ j ∈ T, (j : ℤ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hdecomp]
        ring
  have hvariance : ∑ j ∈ T, ((j : ℤ) - (i : ℤ)) ^ 2 = 0 := by
    calc
      ∑ j ∈ T, ((j : ℤ) - (i : ℤ)) ^ 2 =
          (∑ j ∈ T, (j : ℤ) ^ 2) -
            2 * (i : ℤ) * (∑ j ∈ T, (j : ℤ)) +
              (T.card : ℤ) * (i : ℤ) ^ 2 := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul]
        rw [show (∑ x ∈ T, (2 : ℤ) * (x : ℤ) * (i : ℤ)) =
            2 * (i : ℤ) * ∑ x ∈ T, (x : ℤ) by
          rw [mul_comm 2 (i : ℤ), Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring]
      _ = 0 := by rw [← hsquareZ, ← hlinZ]; ring
  intro j hj
  have hallzero : ∀ k ∈ T, ((k : ℤ) - (i : ℤ)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (s := T)
      (fun (k : ℕ) hk ↦ sq_nonneg ((k : ℤ) - (i : ℤ)))).mp hvariance
  have hjzero := hallzero j hj
  have : (j : ℤ) = (i : ℤ) := by nlinarith
  exact_mod_cast this

/-- The index form of the Bosznay nonaveraging argument. -/
theorem bosznay_no_average_indices {q i : ℕ} (hq : 2 ≤ q)
    (hi : i ∈ Finset.Ico 1 q) {T : Finset ℕ}
    (hT : T ⊆ Finset.Ico 1 q) (hTcard : 2 ≤ T.card) (hiT : i ∉ T) :
    T.card * bosznayValue q i ≠ T.sum (bosznayValue q) := by
  intro havg
  obtain ⟨hlin, htri⟩ := bosznay_no_carry hq hi hT hTcard havg
  have hEq := eq_of_sum_id_and_triangular hlin htri
  obtain ⟨j, hj⟩ := T.nonempty_of_ne_empty (by
    intro h
    subst T
    simp at hTcard)
  have : j = i := hEq j hj
  exact hiT (this ▸ hj)

/-- Bosznay's construction is nonaveraging. -/
theorem isNonaveraging_bosznaySet {q : ℕ} (hq : 2 ≤ q) :
    IsNonaveraging (bosznaySet q) := by
  intro a ha S hS hScard
  rw [bosznaySet] at ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  let T := (Finset.Ico 1 q).filter fun j ↦ bosznayValue q j ∈ S
  have hqpos : 0 < q := by omega
  have hinj := bosznayValue_injective hqpos
  have himage : T.image (bosznayValue q) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
    · intro hx
      have hxA : x ∈ bosznaySet q := by
        have := hS hx
        exact (Finset.mem_erase.mp this).2
      rw [bosznaySet] at hxA
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxA
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hx⟩, rfl⟩
  have hTsub : T ⊆ Finset.Ico 1 q := Finset.filter_subset _ _
  have hTcardEq : T.card = S.card := by
    rw [← himage, Finset.card_image_of_injective _ hinj]
  have hTcard : 2 ≤ T.card := hTcardEq.symm ▸ hScard
  have hiT : i ∉ T := by
    intro hiT
    have hvalS : bosznayValue q i ∈ S := (Finset.mem_filter.mp hiT).2
    have := hS hvalS
    exact (Finset.mem_erase.mp this).1 rfl
  intro havg
  apply bosznay_no_average_indices hq hi hTsub hTcard hiT
  have hsum : S.sum id = T.sum (bosznayValue q) := by
    rw [← himage, Finset.sum_image]
    · simp
    · exact hinj.injOn
  rw [hTcardEq]
  exact havg.trans hsum

/-- The finite Bosznay lower bound at fourth powers. -/
theorem bosznay_card_le_F {q : ℕ} (hq : 2 ≤ q) :
    q - 1 ≤ F (q ^ 4) := by
  rw [← card_bosznaySet (by omega : 0 < q)]
  exact card_le_F_of_subset (bosznaySet_subset_Icc hq)
    (isNonaveraging_bosznaySet hq)

/-- The integer scale at which the Bosznay construction is embedded into
`{1,...,N}`. -/
def bosznayScale (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 4 : ℝ)⌋₊

theorem rpow_one_fourth_pow_four (N : ℕ) :
    ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (N : ℝ) := by
  convert Real.rpow_inv_natCast_pow (x := (N : ℝ)) (by positivity)
    (by norm_num : (4 : ℕ) ≠ 0) using 1
  all_goals norm_num

theorem bosznayScale_pow_le (N : ℕ) :
    bosznayScale N ^ 4 ≤ N := by
  have hxnonneg : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hfloor : (bosznayScale N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    exact Nat.floor_le hxnonneg
  have hpow : (bosznayScale N : ℝ) ^ 4 ≤
      ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) hfloor 4
  rw [rpow_one_fourth_pow_four] at hpow
  exact_mod_cast hpow

theorem four_le_rpow_one_fourth {N : ℕ} (hN : 256 ≤ N) :
    (4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hcast : (256 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 256) hcast
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  norm_num [show (256 : ℝ) = 4 ^ 4 by norm_num,
    ← Real.rpow_natCast] at hrpow
  exact hrpow

theorem four_le_bosznayScale {N : ℕ} (hN : 256 ≤ N) :
    4 ≤ bosznayScale N := by
  apply Nat.le_floor
  exact four_le_rpow_one_fourth hN

/-- A convenient explicit pointwise version of Bosznay's asymptotic lower
bound.  The constant `2` is not optimized. -/
theorem rpow_one_fourth_le_two_mul_F {N : ℕ} (hN : 256 ≤ N) :
    (N : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (F N : ℝ) := by
  let q := bosznayScale N
  have hq4 : q ^ 4 ≤ N := bosznayScale_pow_le N
  have hq : 4 ≤ q := four_le_bosznayScale hN
  have hqF : q - 1 ≤ F N :=
    (bosznay_card_le_F (q := q) (by omega)).trans (F_mono hq4)
  have hxlt : (N : ℝ) ^ (1 / 4 : ℝ) < (q : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 4 : ℝ))
  have hqreal : (q : ℝ) + 1 ≤ 2 * ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show q + 1 ≤ 2 * (q - 1) by omega)
  have hcast : ((q - 1 : ℕ) : ℝ) ≤ (F N : ℝ) := by exact_mod_cast hqF
  linarith

/-- Bosznay's construction gives the lower asymptotic
`N^(1/4) ≪ F(N)`. -/
theorem bosznay_lower_bound :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (F N : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, Filter.eventually_atTop.2 ⟨256, ?_⟩⟩
  intro N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (F N : ℝ))]
  exact rpow_one_fourth_le_two_mul_F hN

end

end Erdos186

import ErdosProblems.Erdos1038.ResidualWidthConvex
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Formal Lagrange inversion for residual inverse widths

This module proves the scalar formal Lagrange inversion formula needed for
the finite residual inverse map.  It then expands the relevant binomial
product and identifies its coefficients exactly with the positive monomial
formula in `ResidualWidthConvex`.
-/

set_option warningAsError false

open scoped BigOperators
open Finset

noncomputable section

namespace PowerSeries

abbrev RPS := PowerSeries ℝ

private def unitOfConstantOne (phi : RPS)
    (hphi : constantCoeff phi = 1) : RPSˣ :=
  ⟨phi, phi⁻¹,
    PowerSeries.mul_inv_cancel phi (by simp [hphi]),
    PowerSeries.inv_mul_cancel phi (by simp [hphi])⟩

private lemma unitOfConstantOne_val (phi : RPS)
    (hphi : constantCoeff phi = 1) :
    ↑(unitOfConstantOne phi hphi) = phi := rfl

private lemma unitOfConstantOne_inv_val (phi : RPS)
    (hphi : constantCoeff phi = 1) :
    ↑(unitOfConstantOne phi hphi)⁻¹ = phi⁻¹ := rfl

lemma derivative_kernel (U : RPSˣ) {p : ℕ} (hp : 0 < p) :
    coeff p ((↑(U ^ (p + 1)) : RPS) *
      d⁄dX ℝ (X * (↑(U⁻¹) : RPS))) = 0 := by
  change coeff p ((↑(U ^ (p + 1)) : RPS) *
      (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) = 0
  rw [(PowerSeries.derivative ℝ).leibniz]
  rw [show (PowerSeries.derivative ℝ) (↑(U⁻¹) : RPS) =
      -(↑(U⁻¹) : RPS) ^ 2 * (PowerSeries.derivative ℝ) (↑U : RPS) by
        exact PowerSeries.derivative_inv U,
    show (PowerSeries.derivative ℝ) (X : RPS) = 1 by
      exact PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one, mul_add]
  rw [show (↑(U ^ (p + 1)) : RPS) *
      (X * (-((↑(U⁻¹) : RPS) ^ 2) *
        (PowerSeries.derivative ℝ) (↑U : RPS))) =
      -X * (↑(U ^ (p - 1)) : RPS) *
        (PowerSeries.derivative ℝ) (↑U : RPS) by
    rw [show p + 1 = (p - 1) + 2 by omega, pow_add]
    simp only [Units.val_pow_eq_pow_val]
    calc
      (↑(U ^ (p - 1) * U ^ 2) : RPS) *
          (X * (-((↑(U⁻¹) : RPS) ^ 2) *
            (PowerSeries.derivative ℝ) (↑U : RPS))) =
          -X * (↑(U ^ (p - 1) * U ^ 2 * (U⁻¹) ^ 2) : RPS) *
            (PowerSeries.derivative ℝ) (↑U : RPS) := by
        simp only [Units.val_pow_eq_pow_val, Units.val_mul]
        ring
      _ = _ := by simp]
  rw [show (↑(U ^ (p + 1)) : RPS) * (↑(U⁻¹) : RPS) =
      (↑(U ^ p) : RPS) by
    simp only [← Units.val_mul]
    rw [pow_succ]
    simp]
  rw [show -X * (↑(U ^ (p - 1)) : RPS) *
        (PowerSeries.derivative ℝ) (↑U : RPS) + (↑(U ^ p) : RPS) =
      (↑(U ^ p) : RPS) -
        X * ((↑(U ^ (p - 1)) : RPS) *
          (PowerSeries.derivative ℝ) (↑U : RPS)) by ring]
  rw [map_sub, show p = (p - 1) + 1 by omega, coeff_succ_X_mul]
  have hder := congrArg (coeff (p - 1))
    ((PowerSeries.derivative ℝ).leibniz_pow (a := (↑U : RPS)) p)
  change coeff (p - 1) ((PowerSeries.derivative ℝ) ((↑U : RPS) ^ p)) =
    coeff (p - 1) (p • ((↑U : RPS) ^ (p - 1)) •
      (PowerSeries.derivative ℝ) (↑U : RPS)) at hder
  rw [map_nsmul] at hder
  simp only [coeff_derivative, smul_eq_mul, nsmul_eq_mul,
    Units.val_pow_eq_pow_val] at hder ⊢
  have hp1 : p - 1 + 1 = p := by omega
  rw [hp1] at hder ⊢
  have hpCast : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hp1
  rw [hpCast] at hder
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith

lemma derivative_kernel_zero (U : RPSˣ) :
    coeff 0 ((↑U : RPS) *
      (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) = 1 := by
  rw [(PowerSeries.derivative ℝ).leibniz]
  rw [show (PowerSeries.derivative ℝ) (↑(U⁻¹) : RPS) =
      -(↑(U⁻¹) : RPS) ^ 2 * (PowerSeries.derivative ℝ) (↑U : RPS) by
        exact PowerSeries.derivative_inv U,
    show (PowerSeries.derivative ℝ) (X : RPS) = 1 by
      exact PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one, mul_add, map_add]
  rw [show (↑U : RPS) * (X *
        (-((↑(U⁻¹) : RPS) ^ 2) *
          (PowerSeries.derivative ℝ) (↑U : RPS))) =
      X * ((↑U : RPS) *
        (-((↑(U⁻¹) : RPS) ^ 2) *
          (PowerSeries.derivative ℝ) (↑U : RPS))) by ring,
    coeff_zero_X_mul]
  simp only [zero_add]
  rw [show (↑U : RPS) * (↑(U⁻¹) : RPS) = 1 by
    simp only [← Units.val_mul]
    simp]
  simp

lemma substitution_kernel (U : RPSˣ) {n m : ℕ} (hm : m ≤ n) :
    coeff n (((X : RPS) * (↑(U⁻¹) : RPS)) ^ m *
      ((↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) =
      if m = n then 1 else 0 := by
  let p := n - m
  have hnp : n + 1 = m + (p + 1) := by omega
  rw [show ((X : RPS) * (↑(U⁻¹) : RPS)) ^ m *
        ((↑(U ^ (n + 1)) : RPS) *
          (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) =
      X ^ m * ((↑(U ^ (p + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) by
    have hcancel : ((↑(U⁻¹) : RPS) ^ m) * (↑(U ^ m) : RPS) = 1 := by
      simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      simp
    rw [mul_pow, hnp, pow_add]
    simp only [Units.val_pow_eq_pow_val]
    calc
      X ^ m * (↑(U⁻¹) : RPS) ^ m *
          ((↑(U ^ m) : RPS) * (↑(U ^ (p + 1)) : RPS) *
            (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) =
          X ^ m *
            ((((↑(U⁻¹) : RPS) ^ m) * (↑(U ^ m) : RPS)) *
              ((↑(U ^ (p + 1)) : RPS) *
                (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) := by ring
      _ = _ := by
        rw [hcancel, one_mul]
        simp only [Units.val_pow_eq_pow_val]]
  rw [coeff_X_pow_mul', if_pos hm]
  by_cases hmn : m = n
  · subst m
    simpa [p] using! derivative_kernel_zero U
  · have hp : 0 < p := Nat.sub_pos_of_lt (lt_of_le_of_ne hm hmn)
    rw [if_neg hmn]
    exact derivative_kernel U hp

lemma unit_derivative_kernel_eq (U : RPSˣ) {n : ℕ} (hn : 0 < n) :
    (↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)) =
      (↑(U ^ n) : RPS) - X *
        ((↑(U ^ (n - 1)) : RPS) *
          (PowerSeries.derivative ℝ) (↑U : RPS)) := by
  rw [(PowerSeries.derivative ℝ).leibniz]
  rw [show (PowerSeries.derivative ℝ) (↑(U⁻¹) : RPS) =
      -(↑(U⁻¹) : RPS) ^ 2 * (PowerSeries.derivative ℝ) (↑U : RPS) by
        exact PowerSeries.derivative_inv U,
    show (PowerSeries.derivative ℝ) (X : RPS) = 1 by
      exact PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one, mul_add]
  rw [show (↑(U ^ (n + 1)) : RPS) *
      (X * (-((↑(U⁻¹) : RPS) ^ 2) *
        (PowerSeries.derivative ℝ) (↑U : RPS))) =
      -X * (↑(U ^ (n - 1)) : RPS) *
        (PowerSeries.derivative ℝ) (↑U : RPS) by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    simp only [Units.val_pow_eq_pow_val]
    calc
      (↑(U ^ (n - 1) * U ^ 2) : RPS) *
          (X * (-((↑(U⁻¹) : RPS) ^ 2) *
            (PowerSeries.derivative ℝ) (↑U : RPS))) =
          -X * (↑(U ^ (n - 1) * U ^ 2 * (U⁻¹) ^ 2) : RPS) *
            (PowerSeries.derivative ℝ) (↑U : RPS) := by
        simp only [Units.val_pow_eq_pow_val, Units.val_mul]
        ring
      _ = _ := by simp]
  rw [show (↑(U ^ (n + 1)) : RPS) * (↑(U⁻¹) : RPS) =
      (↑(U ^ n) : RPS) by
    simp only [← Units.val_mul]
    rw [pow_succ]
    simp]
  ring

lemma lagrange_rhs_kernel (U : RPSˣ) {n : ℕ} (hn : 0 < n) :
    coeff (n - 1) ((↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) =
      (n : ℝ)⁻¹ * coeff (n - 1) (↑(U ^ n) : RPS) := by
  rw [unit_derivative_kernel_eq U hn, map_sub]
  by_cases hn1 : n = 1
  · subst n
    norm_num [coeff_zero_X_mul]
  · have hn2 : 2 ≤ n := by omega
    rw [show n - 1 = (n - 2) + 1 by omega, coeff_succ_X_mul]
    have hder := congrArg (coeff (n - 2))
      ((PowerSeries.derivative ℝ).leibniz_pow (a := (↑U : RPS)) n)
    change coeff (n - 2) ((PowerSeries.derivative ℝ) ((↑U : RPS) ^ n)) =
      coeff (n - 2) (n • ((↑U : RPS) ^ (n - 1)) •
        (PowerSeries.derivative ℝ) (↑U : RPS)) at hder
    rw [map_nsmul] at hder
    simp only [coeff_derivative, smul_eq_mul, nsmul_eq_mul,
      Units.val_pow_eq_pow_val] at hder ⊢
    have hnidx : n - 2 + 1 = n - 1 := by omega
    rw [hnidx] at hder
    have hnCast : ((n - 2 : ℕ) : ℝ) + 1 = (n - 1 : ℕ) := by
      exact_mod_cast hnidx
    rw [hnCast] at hder
    rw [hnidx]
    have hnidx2 : n - 1 + 1 = n := by omega
    have hnCast2 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast hnidx2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    calc
      ((coeff (n - 1)) ((↑U : RPS) ^ n) -
          (coeff (n - 2)) ((↑U : RPS) ^ (n - 1) *
            (PowerSeries.derivative ℝ) (↑U : RPS))) * (n : ℝ) =
          (coeff (n - 1)) ((↑U : RPS) ^ n) * n -
            n * (coeff (n - 2)) ((↑U : RPS) ^ (n - 1) *
              (PowerSeries.derivative ℝ) (↑U : RPS)) := by ring
      _ = (coeff (n - 1)) ((↑U : RPS) ^ n) * n -
          (coeff (n - 1)) ((↑U : RPS) ^ n) * (n - 1 : ℕ) := by
        rw [hder]
      _ = (coeff (n - 1)) ((↑U : RPS) ^ n) := by
        rw [← hnCast2]
        ring

lemma subst_kernel_coeff (U : RPSˣ) (w : RPS) (n : ℕ) :
    coeff n ((w.subst (X * (↑(U⁻¹) : RPS))) *
        ((↑(U ^ (n + 1)) : RPS) *
          (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) =
      coeff n w := by
  let f : RPS := X * (↑(U⁻¹) : RPS)
  let K : RPS := (↑(U ^ (n + 1)) : RPS) *
    (PowerSeries.derivative ℝ) f
  let tail : RPS := mk fun i ↦ coeff (i + (n + 1)) w
  have hf0 : constantCoeff f = 0 := by
    simp [f]
  let hf : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hwdecomp : w = tail * X ^ (n + 1) + (trunc (n + 1) w : RPS) := by
    simpa [tail] using! eq_shift_mul_X_pow_add_trunc (n + 1) w
  have htail : coeff n (((tail * X ^ (n + 1)).subst f) * K) = 0 := by
    rw [subst_mul hf, subst_pow hf, subst_X hf]
    rw [show (tail.subst f * f ^ (n + 1)) * K =
        X ^ (n + 1) *
          (tail.subst f * ((↑(U⁻¹) : RPS) ^ (n + 1)) * K) by
      dsimp [f]
      rw [mul_pow]
      ring]
    rw [coeff_X_pow_mul', if_neg (by omega)]
  have hpoly : ((trunc (n + 1) w : RPS).subst f) =
      ∑ i ∈ Finset.range (n + 1), C (coeff i w) * f ^ i := by
    rw [subst_coe hf]
    exact eval₂_trunc_eq_sum_range f C (n + 1) w
  calc
    coeff n ((w.subst (X * (↑(U⁻¹) : RPS))) *
        ((↑(U ^ (n + 1)) : RPS) *
          (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) =
        coeff n ((w.subst f) * K) := by rfl
    _ = coeff n ((((tail * X ^ (n + 1)).subst f) +
          ((trunc (n + 1) w : RPS).subst f)) * K) := by
      rw [← subst_add hf, ← hwdecomp]
    _ = coeff n (((trunc (n + 1) w : RPS).subst f) * K) := by
      rw [add_mul, map_add, htail, zero_add]
    _ = coeff n ((∑ i ∈ Finset.range (n + 1),
          C (coeff i w) * f ^ i) * K) := by rw [hpoly]
    _ = ∑ i ∈ Finset.range (n + 1), coeff i w *
          (if i = n then 1 else 0) := by
      rw [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (C (coeff i w) * f ^ i) * K =
          C (coeff i w) * (f ^ i * K) by ring, coeff_C_mul]
      congr 1
      change coeff n (((X : RPS) * (↑(U⁻¹) : RPS)) ^ i *
        ((↑(U ^ (n + 1)) : RPS) *
          (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) = _
      exact substitution_kernel U (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = coeff n w := by simp

theorem lagrange_coeff_of_subst_eq_X (U : RPSˣ) (w : RPS)
    (hw : w.subst (X * (↑(U⁻¹) : RPS)) = X) {n : ℕ} (hn : 0 < n) :
    coeff n w = (n : ℝ)⁻¹ * coeff (n - 1) (↑(U ^ n) : RPS) := by
  let K : RPS := (↑(U ^ (n + 1)) : RPS) *
    (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))
  have hmul := congrArg (fun g : RPS ↦ coeff n (g * K)) hw
  change coeff n ((w.subst (X * (↑(U⁻¹) : RPS))) *
      ((↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) =
    coeff n (X * ((↑(U ^ (n + 1)) : RPS) *
      (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) at hmul
  rw [subst_kernel_coeff U w n] at hmul
  have hx : coeff n (X * ((↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS)))) =
      coeff (n - 1) ((↑(U ^ (n + 1)) : RPS) *
        (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))) := by
    let L : RPS := (↑(U ^ (n + 1)) : RPS) *
      (PowerSeries.derivative ℝ) (X * (↑(U⁻¹) : RPS))
    have hidx : n - 1 + 1 = n := by omega
    calc
      coeff n (X * L) = coeff (n - 1 + 1) (X * L) := by rw [hidx]
      _ = coeff (n - 1) L := coeff_succ_X_mul (n - 1) L
  rw [hx] at hmul
  exact hmul.trans (lagrange_rhs_kernel U hn)

noncomputable def lagrangeInverseCoeff (U : RPSˣ) (n : ℕ) : ℝ :=
  (if n = 1 then 1 else 0) -
    ∑ j : Fin n, lagrangeInverseCoeff U j *
      coeff n (((X : RPS) * (↑(U⁻¹) : RPS)) ^ (j : ℕ))
termination_by n
decreasing_by exact j.isLt

noncomputable def lagrangeInverseSeries (U : RPSˣ) : RPS :=
  mk (lagrangeInverseCoeff U)

@[simp]
lemma coeff_lagrangeInverseSeries (U : RPSˣ) (n : ℕ) :
    coeff n (lagrangeInverseSeries U) = lagrangeInverseCoeff U n := by
  simp [lagrangeInverseSeries]

@[simp]
lemma coeff_zero_lagrangeInverseSeries (U : RPSˣ) :
    coeff 0 (lagrangeInverseSeries U) = 0 := by
  rw [coeff_lagrangeInverseSeries, lagrangeInverseCoeff]
  norm_num

lemma constantCoeff_unit_inv_eq_one (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) :
    constantCoeff (↑(U⁻¹) : RPS) = 1 := by
  have hunitprod : (↑(U⁻¹) : RPS) * (↑U : RPS) = 1 := by
    simp only [← Units.val_mul]
    simp
  have hmul := congrArg constantCoeff hunitprod
  rw [map_mul, hU, mul_one, map_one] at hmul
  exact hmul

lemma coeff_forward_pow_eq_zero_of_lt (U : RPSˣ)
    {n m : ℕ} (hnm : n < m) :
    coeff n (((X : RPS) * (↑(U⁻¹) : RPS)) ^ m) = 0 := by
  rw [mul_pow, coeff_X_pow_mul', if_neg hnm.not_ge]

lemma coeff_forward_pow_diag (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) (n : ℕ) :
    coeff n (((X : RPS) * (↑(U⁻¹) : RPS)) ^ n) = 1 := by
  rw [mul_pow, coeff_X_pow_mul', if_pos le_rfl]
  simp only [tsub_self]
  rw [coeff_zero_eq_constantCoeff, map_pow,
    constantCoeff_unit_inv_eq_one U hU, one_pow]

theorem lagrangeInverseSeries_subst_forward (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) :
    (lagrangeInverseSeries U).subst (X * (↑(U⁻¹) : RPS)) = X := by
  let f : RPS := X * (↑(U⁻¹) : RPS)
  have hf0 : constantCoeff f = 0 := by simp [f]
  let hf : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  ext n
  rw [coeff_subst' hf]
  rw [finsum_eq_sum_of_support_subset
    (s := Finset.range (n + 1))]
  · simp only [coeff_lagrangeInverseSeries, smul_eq_mul]
    rw [Finset.sum_range_succ]
    rw [show ∑ j ∈ Finset.range n,
          lagrangeInverseCoeff U j * coeff n (f ^ j) =
        ∑ j : Fin n, lagrangeInverseCoeff U j * coeff n (f ^ (j : ℕ)) by
      exact (Fin.sum_univ_eq_sum_range _ n).symm]
    rw [coeff_forward_pow_diag U hU]
    rw [lagrangeInverseCoeff]
    simp only [f, mul_pow, mul_one]
    rw [coeff_X]
    ring
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmn
    have hlt : n < m := by omega
    have hz : coeff n (f ^ m) = 0 := by
      exact coeff_forward_pow_eq_zero_of_lt U hlt
    exact (Function.mem_support.mp hm) (by simp [hz])

/-- Substitution by the normalized forward series used in Lagrange
inversion is injective. -/
theorem subst_forward_injective (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) :
    Function.Injective
      (fun w : RPS ↦ w.subst (X * (↑(U⁻¹) : RPS))) := by
  intro w₁ w₂ hw
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let f : RPS := X * (↑(U⁻¹) : RPS)
      have hf0 : constantCoeff f = 0 := by simp [f]
      let hf : PowerSeries.HasSubst f :=
        PowerSeries.HasSubst.of_constantCoeff_zero' hf0
      have hsupp (w : RPS) :
          Function.support (fun m ↦ coeff m w • coeff n (f ^ m)) ⊆
            (Finset.range (n + 1) : Set ℕ) := by
        intro m hm
        rw [Finset.mem_coe, Finset.mem_range]
        by_contra hmn
        have hlt : n < m := by omega
        have hz : coeff n (f ^ m) = 0 := by
          exact coeff_forward_pow_eq_zero_of_lt U hlt
        exact (Function.mem_support.mp hm) (by simp [hz])
      have heq := congrArg (coeff n) hw
      change coeff n (w₁.subst f) = coeff n (w₂.subst f) at heq
      rw [coeff_subst' hf, coeff_subst' hf,
        finsum_eq_sum_of_support_subset
          (fun m ↦ coeff m w₁ • coeff n (f ^ m)) (hsupp w₁),
        finsum_eq_sum_of_support_subset
          (fun m ↦ coeff m w₂ • coeff n (f ^ m)) (hsupp w₂)] at heq
      simp only [smul_eq_mul] at heq
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        coeff_forward_pow_diag U hU] at heq
      have hlower :
          ∑ m ∈ Finset.range n, coeff m w₁ * coeff n (f ^ m) =
            ∑ m ∈ Finset.range n, coeff m w₂ * coeff n (f ^ m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [ih m (Finset.mem_range.mp hm)]
      rw [hlower] at heq
      linarith

/-- Fixed-point form of the formal inverse equation. -/
theorem lagrangeInverseSeries_fixedPoint (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) :
    lagrangeInverseSeries U =
      X * (↑U : RPS).subst (lagrangeInverseSeries U) := by
  let w : RPS := lagrangeInverseSeries U
  have hw0 : constantCoeff w = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_zero_lagrangeInverseSeries U
  let hwSubst : PowerSeries.HasSubst w :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hw0
  let f : RPS := X * (↑(U⁻¹) : RPS)
  have hf0 : constantCoeff f = 0 := by simp [f]
  let hf : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  apply subst_forward_injective U hU
  change w.subst f = (X * ((↑U : RPS).subst w)).subst f
  rw [show w.subst f = X by
    exact lagrangeInverseSeries_subst_forward U hU]
  rw [PowerSeries.subst_mul hf, PowerSeries.subst_X hf,
    PowerSeries.subst_comp_subst_apply hwSubst hf (↑U : RPS)]
  rw [show w.subst f = X by
    exact lagrangeInverseSeries_subst_forward U hU]
  rw [← PowerSeries.map_algebraMap_eq_subst_X]
  simp [f]

theorem coeff_lagrangeInverseSeries_lagrange (U : RPSˣ)
    (hU : constantCoeff (↑U : RPS) = 1) {n : ℕ} (hn : 0 < n) :
    coeff n (lagrangeInverseSeries U) =
      (n : ℝ)⁻¹ * coeff (n - 1) (↑(U ^ n) : RPS) := by
  exact lagrange_coeff_of_subst_eq_X U (lagrangeInverseSeries U)
    (lagrangeInverseSeries_subst_forward U hU) hn

lemma real_multichoose_eq_ascPochhammer_div (a : ℝ) (r : ℕ) :
    Ring.multichoose a r =
      (ascPochhammer ℝ r).eval a / (r.factorial : ℝ) := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a r
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hfac).mpr
  rw [mul_comm]
  exact h

noncomputable def lagrangeFactorSeries (a d : ℝ) : RPS :=
  rescale (-d⁻¹) (binomialSeries ℝ (-a))

lemma coeff_lagrangeFactorSeries (a d : ℝ) (r : ℕ) :
    coeff r (lagrangeFactorSeries a d) =
      (ascPochhammer ℝ r).eval a / (r.factorial : ℝ) * d⁻¹ ^ r := by
  rw [lagrangeFactorSeries, coeff_rescale, binomialSeries_coeff]
  simp only [smul_eq_mul, mul_one, Ring.choose_neg', Units.smul_def,
    zsmul_eq_mul]
  rw [Int.cast_negOnePow_natCast]
  rw [real_multichoose_eq_ascPochhammer_div]
  rw [neg_pow]
  have hsign : (-1 : ℝ) ^ r * (-1 : ℝ) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((-1 : ℝ) ^ r * d⁻¹ ^ r) *
        ((-1 : ℝ) ^ r *
          ((ascPochhammer ℝ r).eval a / (r.factorial : ℝ))) =
        ((-1 : ℝ) ^ r * (-1 : ℝ) ^ r) *
          (((ascPochhammer ℝ r).eval a / (r.factorial : ℝ)) *
            d⁻¹ ^ r) := by ring
    _ = _ := by rw [hsign, one_mul]

lemma lagrangeFactorSeries_constantCoeff (a d : ℝ) :
    constantCoeff (lagrangeFactorSeries a d) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_lagrangeFactorSeries]
  norm_num

lemma binomialSeries_pow (a : ℝ) (n : ℕ) :
    (binomialSeries ℝ a) ^ n = binomialSeries ℝ ((n : ℝ) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← binomialSeries_add]
      congr 2
      push_cast
      ring

lemma lagrangeFactorSeries_pow (a d : ℝ) (n : ℕ) :
    (lagrangeFactorSeries a d) ^ n =
      lagrangeFactorSeries ((n : ℝ) * a) d := by
  rw [lagrangeFactorSeries, lagrangeFactorSeries, ← map_pow,
    binomialSeries_pow]
  congr 2
  ring

noncomputable def lagrangePhi {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) : RPS :=
  ∏ i, lagrangeFactorSeries (a i) (d i)

lemma lagrangePhi_constantCoeff {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) :
    constantCoeff (lagrangePhi a d) = 1 := by
  classical
  simp [lagrangePhi, lagrangeFactorSeries_constantCoeff]

/-- The binomial Lagrange kernel, packaged as a unit of formal power
series using its constant coefficient `1`. -/
noncomputable def lagrangePhiUnit {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) : RPSˣ :=
  unitOfConstantOne (lagrangePhi a d) (lagrangePhi_constantCoeff a d)

@[simp]
lemma lagrangePhiUnit_val {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) :
    ↑(lagrangePhiUnit a d) = lagrangePhi a d := by
  rfl

/-- The formal inverse at zero of `X / lagrangePhi`. -/
noncomputable def lagrangeInversePowerSeries
    {iota : Type*} [Fintype iota] (a d : iota → ℝ) : RPS :=
  lagrangeInverseSeries (lagrangePhiUnit a d)

@[simp]
lemma coeff_zero_lagrangeInversePowerSeries
    {iota : Type*} [Fintype iota] (a d : iota → ℝ) :
    coeff 0 (lagrangeInversePowerSeries a d) = 0 := by
  exact coeff_zero_lagrangeInverseSeries (lagrangePhiUnit a d)

theorem coeff_lagrangeInversePowerSeries
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    {n : ℕ} (hn : 0 < n) :
    coeff n (lagrangeInversePowerSeries a d) =
      (n : ℝ)⁻¹ * coeff (n - 1) ((lagrangePhi a d) ^ n) := by
  simpa [lagrangeInversePowerSeries] using!
    coeff_lagrangeInverseSeries_lagrange (lagrangePhiUnit a d)
      (by
        change constantCoeff (lagrangePhi a d) = 1
        exact lagrangePhi_constantCoeff a d) hn

theorem lagrangeInversePowerSeries_fixedPoint
    {iota : Type*} [Fintype iota] (a d : iota → ℝ) :
    lagrangeInversePowerSeries a d =
      X * (lagrangePhi a d).subst (lagrangeInversePowerSeries a d) := by
  exact lagrangeInverseSeries_fixedPoint (lagrangePhiUnit a d) <| by
    change constantCoeff (lagrangePhi a d) = 1
    exact lagrangePhi_constantCoeff a d

lemma lagrangePhi_pow {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (n : ℕ) :
    (lagrangePhi a d) ^ n =
      ∏ i, lagrangeFactorSeries ((n : ℝ) * a i) (d i) := by
  classical
  rw [lagrangePhi, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact lagrangeFactorSeries_pow (a i) (d i) n

lemma sum_finsuppAntidiag_eq_lagrangeMultiIndices
    {iota : Type*} [Fintype iota] [DecidableEq iota] (n : ℕ) (hn : 0 < n)
    (F : iota → ℕ → ℝ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset iota) (n - 1),
        ∏ i, F i (l i)) =
      ∑ r ∈ Erdos1038.lagrangeMultiIndices iota n,
        ∏ i, F i (r i : ℕ) := by
  classical
  let s := Finset.finsuppAntidiag (Finset.univ : Finset iota) (n - 1)
  let t := Erdos1038.lagrangeMultiIndices iota n
  let toR : ∀ l, l ∈ s → (iota → Fin n) := fun l hl i ↦
    ⟨l i, by
      have hle : l i ≤ ∑ j, l j :=
        Finset.single_le_sum (fun j _ ↦ Nat.zero_le (l j)) (Finset.mem_univ i)
      have hsum : ∑ j, l j = n - 1 :=
        (Finset.mem_finsuppAntidiag.mp hl).1
      omega⟩
  let toL : (iota → Fin n) → (iota →₀ ℕ) := fun r ↦
    Finsupp.equivFunOnFinite.symm fun i ↦ (r i : ℕ)
  have htoR (l : iota →₀ ℕ) (hl : l ∈ s) : toR l hl ∈ t := by
    have hsum : ∑ i, l i = n - 1 :=
      (Finset.mem_finsuppAntidiag.mp hl).1
    simpa [t, Erdos1038.lagrangeMultiIndices, toR] using! hsum
  have htoL (r : iota → Fin n) (hr : r ∈ t) : toL r ∈ s := by
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · have hrsum : ∑ i, (r i : ℕ) = n - 1 := by
        simpa [t, Erdos1038.lagrangeMultiIndices] using! hr
      simpa [toL] using! hrsum
    · exact fun i hi ↦ Finset.mem_univ i
  rw [show Finset.finsuppAntidiag (Finset.univ : Finset iota) (n - 1) = s by rfl,
    show Erdos1038.lagrangeMultiIndices iota n = t by rfl]
  apply Finset.sum_bij' toR (fun r _ ↦ toL r) htoR (fun r hr ↦ htoL r hr)
  · intro l hl
    apply Finsupp.ext
    intro i
    simp [toL, toR]
  · intro r hr
    funext i
    apply Fin.ext
    simp [toL, toR]
  · intro l hl
    apply Finset.prod_congr rfl
    intro i hi
    simp [toR]

lemma coeff_lagrangePhi_pow
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a d : iota → ℝ) {n : ℕ} (hn : 0 < n) :
    coeff (n - 1) ((lagrangePhi a d) ^ n) =
      ∑ r ∈ Erdos1038.lagrangeMultiIndices iota n,
        ∏ i, ((ascPochhammer ℝ (r i : ℕ)).eval ((n : ℝ) * a i) /
          ((r i : ℕ).factorial : ℝ)) * (d i)⁻¹ ^ (r i : ℕ) := by
  classical
  rw [lagrangePhi_pow, PowerSeries.coeff_prod]
  let F : iota → ℕ → ℝ := fun i r ↦
    coeff r (lagrangeFactorSeries ((n : ℝ) * a i) (d i))
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset iota) (n - 1),
      ∏ i, F i (l i)) = _
  rw [sum_finsuppAntidiag_eq_lagrangeMultiIndices n hn F]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.prod_congr rfl
  intro i hi
  simpa [F] using! coeff_lagrangeFactorSeries
    ((n : ℝ) * a i) (d i) (r i : ℕ)

end PowerSeries

namespace Erdos1038

lemma inverseMonomial_add {iota : Type*} [Fintype iota]
    (gamma delta d : iota → ℝ) :
    inverseMonomial (fun i ↦ gamma i + delta i) d =
      inverseMonomial gamma d * inverseMonomial delta d := by
  rw [inverseMonomial, inverseMonomial, inverseMonomial, ← Real.exp_add]
  congr 1
  rw [← neg_add, ← Finset.sum_add_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inverseMonomial_nat_eq_prod_inv_pow
    {iota : Type*} [Fintype iota] (d : iota → ℝ)
    (hd : d ∈ positiveCoordinates iota) (r : iota → ℕ) :
    inverseMonomial (fun i ↦ (r i : ℝ)) d =
      ∏ i, (d i)⁻¹ ^ r i := by
  rw [inverseMonomial]
  have hneg : -(∑ i, (r i : ℝ) * Real.log (d i)) =
      ∑ i, -((r i : ℝ) * Real.log (d i)) := by
    rw [Finset.sum_neg_distrib]
  rw [hneg, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show -((r i : ℝ) * Real.log (d i)) =
      (r i : ℝ) * (-Real.log (d i)) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (hd i)]

lemma inverseMonomial_lagrangeExponent_split
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    (n : ℕ) (r : iota → Fin n) :
    inverseMonomial (lagrangeExponent a n r) d =
      inverseMonomial (fun i ↦ (n : ℝ) * a i) d *
        ∏ i, (d i)⁻¹ ^ (r i : ℕ) := by
  change inverseMonomial
      (fun i ↦ (n : ℝ) * a i + ((r i : ℕ) : ℝ)) d = _
  rw [inverseMonomial_add]
  rw [inverseMonomial_nat_eq_prod_inv_pow d hd
    (fun i ↦ (r i : ℕ))]

theorem scaledLagrangeCoefficient_eq_mul_coeff_phi_pow
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    {n : ℕ} (hn : 0 < n) :
    scaledLagrangeCoefficient a n d =
      inverseMonomial (fun i ↦ (n : ℝ) * a i) d *
        ((n : ℝ)⁻¹ * PowerSeries.coeff (n - 1)
          ((PowerSeries.lagrangePhi a d) ^ n)) := by
  rw [PowerSeries.coeff_lagrangePhi_pow a d hn]
  unfold scaledLagrangeCoefficient scaledLagrangeTerm
    scaledLagrangePrefactor
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [inverseMonomial_lagrangeExponent_split a d hd n r]
  rw [Finset.prod_mul_distrib]
  ring

end Erdos1038

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalFiniteEuler
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Reciprocal roots of the rational Artin polynomial

The Artin polynomial has constant coefficient one, hence the reverse is
monic.  Factoring that reverse over `ℂ` writes the Artin polynomial as a
product of reciprocal linear factors.  Their division-free logarithmic
derivative has coefficients equal to negative reciprocal-root power sums.
-/

namespace Erdos387

open Polynomial PowerSeries
open scoped BigOperators PowerSeries

namespace RationalWeil

theorem reverse_reverse_of_coeff_zero_ne_zero
    {R : Type*} [Semiring R] {A : R[X]} (hA0 : A.coeff 0 ≠ 0) :
    A.reverse.reverse = A := by
  have htrail : A.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr hA0)
  rw [reverse, reverse_natDegree, htrail, Nat.sub_zero]
  exact reflect_reflect

theorem monic_reverse_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff).reverse.Monic := by
  rw [Monic, reverse_leadingCoeff,
    trailingCoeff_eq_coeff_zero (by
      rw [coeff_zero_artinLPolynomial coeff hne]
      exact one_ne_zero),
    coeff_zero_artinLPolynomial coeff hne]

theorem reverse_multiset_prod_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (s : Multiset R[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons F s ih => simp [reverse_mul_of_domain, ih]

theorem reverse_X_sub_C (a : ℂ) :
    (Polynomial.X - Polynomial.C a : ℂ[X]).reverse =
      1 - Polynomial.C a * Polynomial.X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_one_X,
    reflect_C, pow_one]

theorem artinLPolynomial_eq_prod_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    artinLPolynomial coeff =
      ((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ (1 : ℂ[X]) - Polynomial.C a * Polynomial.X)).prod := by
  let A := artinLPolynomial coeff
  let Q := A.reverse
  have hA0 : A.coeff 0 ≠ 0 := by
    change (artinLPolynomial coeff).coeff 0 ≠ 0
    rw [coeff_zero_artinLPolynomial coeff hne]
    exact one_ne_zero
  have hQmonic : Q.Monic := monic_reverse_artinLPolynomial coeff hne
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hfactor := hsplit.eq_prod_roots_of_monic hQmonic
  have hreversed := congrArg reverse hfactor
  rw [reverse_reverse_of_coeff_zero_ne_zero hA0] at hreversed
  rw [reverse_multiset_prod_of_domain] at hreversed
  simpa only [Q, A, Multiset.map_map, Function.comp_apply,
    reverse_X_sub_C] using hreversed

theorem card_roots_reverse_artinLPolynomial_lt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    Multiset.card (artinLPolynomial coeff).reverse.roots <
      2 * (InverseRational.poleSupport coeff).card := by
  rw [Polynomial.splits_iff_card_roots.mp
    (IsAlgClosed.splits (artinLPolynomial coeff).reverse)]
  exact (reverse_natDegree_le _).trans_lt
    (natDegree_artinLPolynomial_lt coeff hne)

/-- One reciprocal-root factor `1-aX`. -/
noncomputable def reciprocalRootFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

/-- The local logarithmic-derivative term `-aX/(1-aX)`. -/
noncomputable def reciprocalRootLogTerm (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a

noncomputable def reciprocalRootProduct
    (s : Multiset ℂ) : PowerSeries ℂ :=
  (s.map reciprocalRootFactor).prod

noncomputable def reciprocalRootLogDerivative
    (s : Multiset ℂ) : PowerSeries ℂ :=
  (s.map reciprocalRootLogTerm).sum

@[simp]
theorem reciprocalRootProduct_cons (a : ℂ) (s : Multiset ℂ) :
    reciprocalRootProduct (a ::ₘ s) =
      reciprocalRootFactor a * reciprocalRootProduct s := by
  simp [reciprocalRootProduct]

@[simp]
theorem reciprocalRootLogDerivative_cons
    (a : ℂ) (s : Multiset ℂ) :
    reciprocalRootLogDerivative (a ::ₘ s) =
      reciprocalRootLogTerm a + reciprocalRootLogDerivative s := by
  simp [reciprocalRootLogDerivative]

theorem X_mul_derivative_reciprocalRootFactor (a : ℂ) :
    PowerSeries.X *
        PowerSeries.derivative ℂ (reciprocalRootFactor a) =
      reciprocalRootFactor a * reciprocalRootLogTerm a := by
  have hinverse : localEuler 1 a * reciprocalRootFactor a = 1 := by
    simpa only [reciprocalRootFactor, pow_one] using
      (localEuler_mul_one_sub (R := ℂ) a (e := 1) one_ne_zero)
  have hderivative :
      PowerSeries.derivative ℂ (reciprocalRootFactor a) =
        PowerSeries.C (-a) := by
    change PowerSeries.derivative ℂ
      (1 - PowerSeries.C a * PowerSeries.X) = _
    rw [map_sub, ← map_one (PowerSeries.C (R := ℂ)),
      PowerSeries.derivative_C, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, zero_sub, map_neg]
  rw [hderivative]
  calc
    PowerSeries.X * PowerSeries.C (-a) =
        PowerSeries.C (-a) * PowerSeries.X := mul_comm _ _
    _ = PowerSeries.C (-a) * PowerSeries.X *
        (localEuler 1 a * reciprocalRootFactor a) := by
      rw [hinverse, mul_one]
    _ = reciprocalRootFactor a * reciprocalRootLogTerm a := by
      simp only [reciprocalRootLogTerm]
      ac_rfl

theorem coeff_reciprocalRootLogTerm (a : ℂ) {n : Nat}
    (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogTerm a) = -(a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [reciprocalRootLogTerm]
  rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
      PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc]]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    coeff_localEuler a one_ne_zero, if_pos (one_dvd k)]
  simp only [Nat.div_one]
  rw [pow_succ]
  ring

theorem X_mul_derivative_reciprocalRootProduct
    (s : Multiset ℂ) :
    PowerSeries.X *
        PowerSeries.derivative ℂ (reciprocalRootProduct s) =
      reciprocalRootProduct s * reciprocalRootLogDerivative s := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [reciprocalRootProduct, reciprocalRootLogDerivative,
        PowerSeries.derivative_one]
  | cons a s ih =>
      rw [reciprocalRootProduct_cons,
        reciprocalRootLogDerivative_cons]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      calc
        PowerSeries.X *
            (reciprocalRootFactor a *
                PowerSeries.derivative ℂ (reciprocalRootProduct s) +
              reciprocalRootProduct s *
                PowerSeries.derivative ℂ (reciprocalRootFactor a)) =
            reciprocalRootFactor a *
                (PowerSeries.X *
                  PowerSeries.derivative ℂ (reciprocalRootProduct s)) +
              reciprocalRootProduct s *
                (PowerSeries.X *
                  PowerSeries.derivative ℂ (reciprocalRootFactor a)) := by
          rw [mul_add]
          congr 1 <;> ac_rfl
        _ = reciprocalRootFactor a *
              (reciprocalRootProduct s * reciprocalRootLogDerivative s) +
            reciprocalRootProduct s *
              (reciprocalRootFactor a * reciprocalRootLogTerm a) := by
          rw [ih, X_mul_derivative_reciprocalRootFactor]
        _ = reciprocalRootFactor a * reciprocalRootProduct s *
            (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) := by
          rw [mul_add]
          ac_rfl

theorem coeff_reciprocalRootLogDerivative
    (s : Multiset ℂ) {n : Nat} (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogDerivative s) =
      -(s.map (fun a ↦ a ^ n)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, Multiset.map_cons,
        Multiset.sum_cons]
      change PowerSeries.coeff n
          (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) =
        -(a ^ n + (s.map (fun z ↦ z ^ n)).sum)
      rw [map_add, coeff_reciprocalRootLogTerm a hn, ih]
      rw [neg_add]

theorem constantCoeff_reciprocalRootLogDerivative
    (s : Multiset ℂ) :
    PowerSeries.constantCoeff (reciprocalRootLogDerivative s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, map_add, ih, add_zero,
        reciprocalRootLogTerm]
      rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
          PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc], PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero]

theorem coe_artinLPolynomial_eq_reciprocalRootProduct
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    (artinLPolynomial coeff : PowerSeries ℂ) =
      reciprocalRootProduct (artinLPolynomial coeff).reverse.roots := by
  let s := (artinLPolynomial coeff).reverse.roots
  calc
    (artinLPolynomial coeff : PowerSeries ℂ) =
        (((s.map
          (fun a ↦ 1 - Polynomial.C a * Polynomial.X)).prod :
            Polynomial ℂ) : PowerSeries ℂ) :=
      congrArg (fun F : Polynomial ℂ ↦ (F : PowerSeries ℂ))
        (artinLPolynomial_eq_prod_roots coeff hne)
    _ = (s.map
          (fun a ↦ ((((1 : Polynomial ℂ) -
            Polynomial.C a * Polynomial.X) : Polynomial ℂ) :
              PowerSeries ℂ))).prod := by
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [ih]
    _ = reciprocalRootProduct s := by
      rw [reciprocalRootProduct]
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro a ha
      rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
        Polynomial.coe_C, Polynomial.coe_X]
      rfl

theorem X_mul_derivative_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    PowerSeries.X * PowerSeries.derivative ℂ
        (artinLPolynomial coeff : PowerSeries ℂ) =
      (artinLPolynomial coeff : PowerSeries ℂ) *
        reciprocalRootLogDerivative
          (artinLPolynomial coeff).reverse.roots := by
  rw [coe_artinLPolynomial_eq_reciprocalRootProduct coeff hne]
  exact X_mul_derivative_reciprocalRootProduct _

end RationalWeil

end Erdos387

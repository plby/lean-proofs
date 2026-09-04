/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.DeltaPower
import ErdosProblems.Erdos240.IntegerValuedPolynomial
import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# The sharp denominator in van der Poorten--Loxton Lemma 1

This file proves independently that the exponent of `lcm(1, ..., h)` in
the normalized derivative denominator is exactly the derivative order.
-/

noncomputable section

open scoped Polynomial

namespace Erdos240.SharpDeltaIndependent

open Finset Polynomial
open Erdos240Delta
open Erdos240.DeltaPower
open Erdos240.IntegerValuedPolynomial

/-- The sharply normalized derivative polynomial. -/
def sharpDerivativePoly (h lambda m : ℕ) : ℚ[X] :=
  C ((Nat.lcmUpto h : ℚ) ^ m) *
    hasseDeriv m (delta h ^ lambda)

theorem sharpDerivativePoly_eval_int (h lambda m : ℕ) (z : ℤ) :
    ∃ w : ℤ, (sharpDerivativePoly h lambda m).eval (z : ℚ) = (w : ℚ) := by
  obtain ⟨w, hw⟩ :=
    exists_int_lcmUpto_pow_mul_eval_delta_pow_hasse h lambda m z
  refine ⟨w, ?_⟩
  simpa [sharpDerivativePoly] using hw

/-- At every `p`-adic integral argument, the sharply normalized derivative
has norm at most one.  This is obtained from its integral values on the
dense set of natural numbers. -/
theorem norm_eval₂_sharpDerivativePoly_le_one
    {p : ℕ} [Fact p.Prime] (h lambda m : ℕ) (y : ℤ_[p]) :
    ‖eval₂ (algebraMap ℚ ℚ_[p]) (y : ℚ_[p])
        (sharpDerivativePoly h lambda m)‖ ≤ 1 := by
  refine PadicInt.denseRange_natCast.induction_on y ?_ ?_
  · exact isClosed_Iic.preimage
      ((Polynomial.continuous_eval₂ (sharpDerivativePoly h lambda m)
        (algebraMap ℚ ℚ_[p])).comp continuous_subtype_val).norm
  · intro n
    obtain ⟨w, hw⟩ := sharpDerivativePoly_eval_int h lambda m (n : ℤ)
    have hw' :
        eval₂ (algebraMap ℚ ℚ_[p]) ((n : ℤ_[p]) : ℚ_[p])
            (sharpDerivativePoly h lambda m) = (w : ℚ_[p]) := by
      calc
        eval₂ (algebraMap ℚ ℚ_[p]) ((n : ℤ_[p]) : ℚ_[p])
              (sharpDerivativePoly h lambda m) =
            algebraMap ℚ ℚ_[p]
              ((sharpDerivativePoly h lambda m).eval (n : ℚ)) := by
                rw [show ((n : ℤ_[p]) : ℚ_[p]) =
                  algebraMap ℚ ℚ_[p] (n : ℚ) by norm_num,
                  Polynomial.eval₂_at_apply]
        _ = algebraMap ℚ ℚ_[p] (w : ℚ) := by
          exact congrArg (algebraMap ℚ ℚ_[p])
            (by simpa only [Int.cast_natCast] using hw)
        _ = (w : ℚ_[p]) := by norm_num
    rw [hw']
    exact Padic.norm_int_le_one w

/-- The rational number whose integrality is the sharp form of Lemma 1. -/
def sharpClearedValue (h lambda m q x : ℕ) : ℚ :=
  (q : ℚ) ^ (2 * h * lambda) *
    (Nat.lcmUpto h : ℚ) ^ m *
      (poweredDeltaHasse h lambda m).eval ((x : ℚ) / q)

theorem norm_sharpClearedValue_le_one_of_not_dvd
    {p : ℕ} [Fact p.Prime] (h lambda m q x : ℕ) (hpq : ¬p ∣ q) :
    ‖(sharpClearedValue h lambda m q x : ℚ_[p])‖ ≤ 1 := by
  have hcop : p.Coprime q := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpq
  have hqnorm : ‖(q : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr hcop
  have hynorm : ‖(x : ℚ_[p]) / (q : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, hqnorm, div_one]
    exact Padic.norm_int_le_one (x : ℤ)
  let y : ℤ_[p] := ⟨(x : ℚ_[p]) / (q : ℚ_[p]), hynorm⟩
  have heval :
      eval₂ (algebraMap ℚ ℚ_[p]) (y : ℚ_[p])
          (sharpDerivativePoly h lambda m) =
        algebraMap ℚ ℚ_[p]
          ((sharpDerivativePoly h lambda m).eval ((x : ℚ) / q)) := by
    rw [show (y : ℚ_[p]) =
        algebraMap ℚ ℚ_[p] ((x : ℚ) / q) by
      dsimp only [y]
      norm_num,
      Polynomial.eval₂_at_apply]
  have hsharp := norm_eval₂_sharpDerivativePoly_le_one h lambda m y
  rw [heval] at hsharp
  have hvalue :
      sharpClearedValue h lambda m q x =
        (q : ℚ) ^ (2 * h * lambda) *
          (sharpDerivativePoly h lambda m).eval ((x : ℚ) / q) := by
    simp only [sharpClearedValue, sharpDerivativePoly, poweredDeltaHasse, poweredDelta,
      Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hvalue]
  push_cast
  rw [norm_mul, norm_pow, hqnorm, one_pow, one_mul]
  exact hsharp

theorem norm_sharpClearedValue_le_one_of_dvd
    {p : ℕ} [Fact p.Prime] (h lambda m q x : ℕ)
    (hq : q ≠ 0) (hpq : p ∣ q) :
    ‖(sharpClearedValue h lambda m q x : ℚ_[p])‖ ≤ 1 := by
  let H : ℚ :=
    (poweredDeltaHasse h lambda m).eval ((x : ℚ) / q)
  by_cases hH : H = 0
  · simp [sharpClearedValue, H, hH]
  obtain ⟨w, hw⟩ :=
    exists_int_cleared_poweredDeltaHasse_factorial h lambda m q (x : ℤ) hq
  have hwH :
      (q : ℚ) ^ (h * lambda - m) * ((h.factorial : ℚ) ^ lambda) * H =
        (w : ℚ) := by
    simpa only [H, Int.cast_natCast] using hw
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz, Int.cast_zero] at hwH
    have hqpow : (q : ℚ) ^ (h * lambda - m) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)
    have hfpow : ((h.factorial : ℚ) ^ lambda) ≠ 0 := by positivity
    exact hH ((mul_eq_zero.mp hwH).resolve_left (mul_ne_zero hqpow hfpow))
  have hvq : 1 ≤ padicValNat p q := one_le_padicValNat_of_dvd hq hpq
  have hvf : padicValNat p h.factorial ≤ h :=
    padicValNat_factorial_le p h
  have hkeyNat :
      lambda * padicValNat p h.factorial ≤
        (h * lambda) * padicValNat p q := by
    calc
      lambda * padicValNat p h.factorial ≤ lambda * h :=
        Nat.mul_le_mul_left lambda hvf
      _ = h * lambda := Nat.mul_comm _ _
      _ ≤ (h * lambda) * padicValNat p q := by
        exact Nat.le_mul_of_pos_right _ hvq
  have hwval := congrArg (padicValRat p) hwH
  have hwval' :
      ((h * lambda - m : ℕ) : ℤ) * (padicValNat p q : ℤ) +
          (lambda : ℤ) * (padicValNat p h.factorial : ℤ) +
          padicValRat p H =
        (padicValInt p w : ℤ) := by
    simpa [padicValRat.mul, hH, hw0, hq, Nat.factorial_ne_zero,
      padicValRat.pow, padicValRat.of_nat, padicValRat.of_int] using hwval
  rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
  have hkey :
      (lambda : ℤ) * (padicValNat p h.factorial : ℤ) ≤
        (h * lambda : ℕ) * (padicValNat p q : ℤ) := by
    exact_mod_cast hkeyNat
  have htarget :
      padicValRat p (sharpClearedValue h lambda m q x) =
        ((2 * h * lambda : ℕ) : ℤ) * (padicValNat p q : ℤ) +
          (m : ℤ) * (padicValNat p (Nat.lcmUpto h) : ℤ) +
          padicValRat p H := by
    have hqcast : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have hLcast : (Nat.lcmUpto h : ℚ) ≠ 0 := by
      exact_mod_cast Nat.lcmUpto_ne_zero h
    have hqpow : (q : ℚ) ^ (2 * h * lambda) ≠ 0 := pow_ne_zero _ hqcast
    have hLpow : (Nat.lcmUpto h : ℚ) ^ m ≠ 0 := pow_ne_zero _ hLcast
    simp only [sharpClearedValue, H]
    rw [padicValRat.mul (mul_ne_zero hqpow hLpow) hH,
      padicValRat.mul hqpow hLpow, padicValRat.pow, padicValRat.pow,
      padicValRat.of_nat, padicValRat.of_nat]
  rw [htarget]
  have hwval_nonneg : (0 : ℤ) ≤ padicValInt p w := by positivity
  have hsub :
      ((h * lambda - m : ℕ) : ℤ) * (padicValNat p q : ℤ) ≤
        (h * lambda : ℕ) * (padicValNat p q : ℤ) := by
    gcongr
    exact_mod_cast Nat.sub_le (h * lambda) m
  have hLnonneg : (0 : ℤ) ≤
      (m : ℤ) * (padicValNat p (Nat.lcmUpto h) : ℤ) := by positivity
  let A : ℤ := (h * lambda : ℕ) * (padicValNat p q : ℤ)
  let B : ℤ := ((h * lambda - m : ℕ) : ℤ) * (padicValNat p q : ℤ)
  let F : ℤ := (lambda : ℤ) * (padicValNat p h.factorial : ℤ)
  let M : ℤ := (m : ℤ) * (padicValNat p (Nat.lcmUpto h) : ℤ)
  let W : ℤ := padicValInt p w
  let V : ℤ := padicValRat p H
  have hBA : B ≤ A := by simpa [A, B] using hsub
  have hFA : F ≤ A := by simpa [A, F] using hkey
  have hM0 : 0 ≤ M := by simpa [M] using hLnonneg
  have hW0 : 0 ≤ W := by simpa [W] using hwval_nonneg
  have hEq : B + F + V = W := by simpa [B, F, V, W] using hwval'
  have htwo :
      ((2 * h * lambda : ℕ) : ℤ) * (padicValNat p q : ℤ) = 2 * A := by
    simp only [A]
    push_cast
    ring
  rw [htwo]
  omega

theorem norm_sharpClearedValue_le_one
    {p : ℕ} [Fact p.Prime] (h lambda m q x : ℕ) (hq : q ≠ 0) :
    ‖(sharpClearedValue h lambda m q x : ℚ_[p])‖ ≤ 1 := by
  by_cases hpq : p ∣ q
  · exact norm_sharpClearedValue_le_one_of_dvd h lambda m q x hq hpq
  · exact norm_sharpClearedValue_le_one_of_not_dvd h lambda m q x hpq

theorem sharpClearedValue_den_eq_one
    (h lambda m q x : ℕ) (hq : q ≠ 0) :
    (sharpClearedValue h lambda m q x).den = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpd
  let : Fact p.Prime := ⟨hp⟩
  have hnorm := norm_sharpClearedValue_le_one h lambda m q x hq (p := p)
  have hunit := PadicInt.isUnit_den (sharpClearedValue h lambda m q x) hnorm
  have hnorm_one :
      ‖((sharpClearedValue h lambda m q x).den : ℤ_[p])‖ = 1 :=
    PadicInt.isUnit_iff.mp hunit
  have hnorm_lt :
      ‖((sharpClearedValue h lambda m q x).den : ℤ_[p])‖ < 1 :=
    PadicInt.norm_natCast_lt_one_iff.mpr hpd
  exact (ne_of_lt hnorm_lt) hnorm_one

/-- **Sharp van der Poorten--Loxton Lemma 1 (rational argument).**

The lcm exponent is exactly the Hasse-derivative order `m`; the additional
`q^(2*h*lambda)` is the source's uniform rational-grid denominator. -/
theorem exists_int_cleared_poweredDeltaHasse_lcm
    (h lambda m q x : ℕ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * h * lambda) *
          (Nat.lcmUpto h : ℚ) ^ m *
          (poweredDeltaHasse h lambda m).eval ((x : ℚ) / q) = (w : ℚ) := by
  let r := sharpClearedValue h lambda m q x
  have hrden : r.den = 1 := sharpClearedValue_den_eq_one h lambda m q x hq
  refine ⟨r.num, ?_⟩
  change r = (r.num : ℚ)
  exact (Rat.coe_int_num_of_den_eq_one hrden).symm

#print axioms Erdos240.SharpDeltaIndependent.exists_int_cleared_poweredDeltaHasse_lcm

end Erdos240.SharpDeltaIndependent

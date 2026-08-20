/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Basic
import DedekindResidue.ExplicitFormula.PrimeSide
import PrimeNumberTheoremAnd.Wiener

/-!
# Dirichlet series of the ideal von Mangoldt coefficient

This file regroups the absolutely convergent prime-power expansion proved in AINTLIB by its
integer norm.  The result is the standard identity

`L(Λ_K, s) = -ζ'_K(s) / ζ_K(s)` for `1 < re s`.
-/

open NumberField
open scoped BigOperators

namespace Erdos980.NaturalChebotarev.IdealMangoldt

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The zero-based exponent convention used in a geometric series is equivalent to a positive
prime-ideal exponent. -/
def primeIdealPowerEquiv : PrimeIdeal K × ℕ ≃ PrimeIdealPower K where
  toFun pk := ⟨(pk.1, pk.2 + 1), by omega⟩
  invFun x := (x.1.1, x.1.2 - 1)
  left_inv pk := by
    apply Prod.ext
    · rfl
    · simp
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt x.2))

/-- A prime-ideal power's contribution to the complex Dirichlet series. -/
def primePowerTerm (s : ℂ) (x : PrimeIdealPower K) : ℂ :=
  (x.weight : ℂ) * (x.norm : ℂ) ^ (-s)

/-- The `n`th term of the ideal von Mangoldt Dirichlet series. -/
def coefficientTerm (s : ℂ) (n : ℕ) : ℂ :=
  (idealMangoldt K n : ℂ) * (n : ℂ) ^ (-s)

private theorem primePowerTerm_equiv (s : ℂ) (pk : PrimeIdeal K × ℕ) :
    primePowerTerm K s (primeIdealPowerEquiv K pk) =
      Complex.log (Ideal.absNorm pk.1.1 : ℂ) *
        (Ideal.absNorm pk.1.1 : ℂ) ^ (-((pk.2 + 1 : ℕ) : ℂ) * s) := by
  have hNpos : (0 : ℝ) < (Ideal.absNorm pk.1.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2)
      (DedekindResidue.two_le_absNorm_of_prime (K := K) (𝔭 := pk.1)))
  have hlog : ((Real.log (Ideal.absNorm pk.1.1 : ℝ) : ℝ) : ℂ) =
      Complex.log (Ideal.absNorm pk.1.1 : ℂ) := by
    rw [show (Ideal.absNorm pk.1.1 : ℂ) = ((Ideal.absNorm pk.1.1 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_log hNpos.le]
  rw [primePowerTerm, PrimeIdealPower.weight, PrimeIdealPower.norm]
  change ((Real.log (Ideal.absNorm pk.1.1 : ℝ) : ℝ) : ℂ) *
      ((Ideal.absNorm pk.1.1 ^ (pk.2 + 1) : ℕ) : ℂ) ^ (-s) = _
  rw [hlog, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
  congr 2
  ring

/-- The prime-power family is absolutely summable throughout `re s > 1`. -/
theorem summable_primePowerTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (primePowerTerm K s) := by
  let f : PrimeIdeal K × ℕ → ℂ := fun pk ↦
    Complex.log (Ideal.absNorm pk.1.1 : ℂ) *
      (Ideal.absNorm pk.1.1 : ℂ) ^ (-((pk.2 + 1 : ℕ) : ℂ) * s)
  have hnorm : ∀ pk : PrimeIdeal K × ℕ,
      ‖f pk‖ = Real.log (Ideal.absNorm pk.1.1) *
        (Ideal.absNorm pk.1.1 : ℝ) ^ (-((pk.2 + 1 : ℕ) : ℝ) * s.re) := by
    intro pk
    have h2 := DedekindResidue.two_le_absNorm_of_prime (K := K) (𝔭 := pk.1)
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by exact_mod_cast (by omega)
    have hlogeq : ‖Complex.log (Ideal.absNorm pk.1.1 : ℂ)‖ =
        Real.log (Ideal.absNorm pk.1.1) := by
      rw [show (Ideal.absNorm pk.1.1 : ℂ) = ((Ideal.absNorm pk.1.1 : ℝ) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hN1)]
    simp only [f]
    rw [norm_mul, hlogeq, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 2
    rw [show -((pk.2 + 1 : ℕ) : ℂ) = ((-((pk.2 + 1 : ℕ) : ℝ) : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul]
  have hf : Summable f := by
    apply Summable.of_norm
    exact (DedekindResidue.summable_primeIdeal_pow_log_rpow K hs).congr
      fun pk ↦ (hnorm pk).symm
  apply (primeIdealPowerEquiv K).summable_iff.mp
  exact hf.congr fun pk ↦ (primePowerTerm_equiv K s pk).symm

/-- Regrouping one norm fiber gives its ideal von Mangoldt coefficient. -/
theorem tsum_normFiber_primePowerTerm (s : ℂ) (n : ℕ) :
    (∑' x : normFiber K n, primePowerTerm K s x.1) = coefficientTerm K s n := by
  rw [tsum_fintype]
  simp only [primePowerTerm, coefficientTerm]
  calc
    (∑ x : normFiber K n, (x.1.weight : ℂ) * (x.1.norm : ℂ) ^ (-s)) =
        ∑ x : normFiber K n, (x.1.weight : ℂ) * (n : ℂ) ^ (-s) := by
          exact Finset.sum_congr rfl fun x _ ↦ by rw [x.2]
    _ = ((∑ x : normFiber K n, x.1.weight : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
    _ = (idealMangoldt K n : ℂ) * (n : ℂ) ^ (-s) := rfl

/-- Absolute convergence of the ℕ-indexed von Mangoldt Dirichlet series on `re s > 1`. -/
theorem summable_coefficientTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (coefficientTerm K s) := by
  let e : (Σ n, normFiber K n) ≃ PrimeIdealPower K :=
    Equiv.sigmaFiberEquiv (PrimeIdealPower.norm : PrimeIdealPower K → ℕ)
  have hp := summable_primePowerTerm K hs
  have hσ : Summable (fun p : Σ n, normFiber K n ↦ primePowerTerm K s (e p)) :=
    (e.summable_iff (f := primePowerTerm K s)).mpr hp
  refine hσ.sigma.congr fun n ↦ ?_
  rw [show (∑' c : normFiber K n, primePowerTerm K s (e ⟨n, c⟩)) =
      ∑' c : normFiber K n, primePowerTerm K s c.1 by
    apply tsum_congr
    intro c
    rfl]
  exact tsum_normFiber_primePowerTerm K s n

/-- Regrouping the prime-power series by norm produces the coefficient Dirichlet series. -/
theorem tsum_coefficientTerm_eq_tsum_primePowerTerm {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, coefficientTerm K s n) =
      ∑' x : PrimeIdealPower K, primePowerTerm K s x := by
  let e : (Σ n, normFiber K n) ≃ PrimeIdealPower K :=
    Equiv.sigmaFiberEquiv (PrimeIdealPower.norm : PrimeIdealPower K → ℕ)
  have hp := summable_primePowerTerm K hs
  have hσ : Summable (fun p : Σ n, normFiber K n ↦ primePowerTerm K s (e p)) :=
    (e.summable_iff (f := primePowerTerm K s)).mpr hp
  calc
    (∑' n : ℕ, coefficientTerm K s n) =
        ∑' n : ℕ, ∑' x : normFiber K n, primePowerTerm K s x.1 := by
          exact tsum_congr fun n ↦ (tsum_normFiber_primePowerTerm K s n).symm
    _ = ∑' p : Σ n, normFiber K n, primePowerTerm K s (e p) := hσ.tsum_sigma.symm
    _ = ∑' x : PrimeIdealPower K, primePowerTerm K s x := e.tsum_eq _

/-- The prime-power series is the logarithmic derivative of the Dedekind zeta function. -/
theorem tsum_primePowerTerm_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    (∑' x : PrimeIdealPower K, primePowerTerm K s x) =
      -(logDeriv (NumberField.dedekindZeta K) s) := by
  rw [← (primeIdealPowerEquiv K).tsum_eq (primePowerTerm K s)]
  calc
    (∑' pk : PrimeIdeal K × ℕ, primePowerTerm K s (primeIdealPowerEquiv K pk)) =
        ∑' pk : PrimeIdeal K × ℕ,
          Complex.log (Ideal.absNorm pk.1.1 : ℂ) *
            (Ideal.absNorm pk.1.1 : ℂ) ^ (-((pk.2 + 1 : ℕ) : ℂ) * s) :=
      tsum_congr fun pk ↦ primePowerTerm_equiv K s pk
    _ = -(logDeriv (NumberField.dedekindZeta K) s) :=
      (DedekindResidue.neg_logDeriv_dedekindZeta_eq_tsum_prod K hs).symm

/-- The ℕ-indexed coefficient series equals `-ζ'_K/ζ_K` on `re s > 1`. -/
theorem tsum_coefficientTerm_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, coefficientTerm K s n) =
      -(logDeriv (NumberField.dedekindZeta K) s) :=
  (tsum_coefficientTerm_eq_tsum_primePowerTerm K hs).trans
    (tsum_primePowerTerm_eq_neg_logDeriv K hs)

/-- The usual `LSeries.term` family for `idealMangoldt` is summable on `re s > 1`. -/
theorem lSeriesSummable_idealMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealMangoldt K n : ℂ)) s := by
  have h := summable_coefficientTerm K hs
  apply h.congr
  intro n
  rw [LSeries.term]
  by_cases hn : n = 0
  · subst n
    simp [coefficientTerm]
  · simp only [hn, ↓reduceIte, coefficientTerm, Complex.cpow_neg, div_eq_mul_inv]

/-- Wiener--Ikehara-facing form of absolute convergence on every real line `σ > 1`. -/
theorem summable_nterm_idealMangoldt {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n ↦ (idealMangoldt K n : ℂ)) σ) := by
  have h := (lSeriesSummable_idealMangoldt K (s := (σ : ℂ)) (by simpa using hσ)).norm
  exact h.congr fun n ↦ by
    simpa using norm_term_eq_nterm_re
      (f := fun n ↦ (idealMangoldt K n : ℂ)) (s := (σ : ℂ)) (n := n)

/-- The `LSeries` of the ideal von Mangoldt coefficient is the negative logarithmic derivative
of the Dedekind zeta function. -/
theorem LSeries_idealMangoldt_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (idealMangoldt K n : ℂ)) s =
      -(logDeriv (NumberField.dedekindZeta K) s) := by
  rw [show LSeries (fun n ↦ (idealMangoldt K n : ℂ)) s =
      ∑' n : ℕ, coefficientTerm K s n by
    unfold LSeries
    apply tsum_congr
    intro n
    rw [LSeries.term]
    by_cases hn : n = 0
    · subst n
      simp [coefficientTerm]
    · simp only [hn, ↓reduceIte, coefficientTerm, Complex.cpow_neg, div_eq_mul_inv]]
  exact tsum_coefficientTerm_eq_neg_logDeriv K hs

/-- Expanded form: the same identity written literally as `-ζ'_K(s)/ζ_K(s)`. -/
theorem LSeries_idealMangoldt_eq_neg_deriv_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (idealMangoldt K n : ℂ)) s =
      -(deriv (NumberField.dedekindZeta K) s / NumberField.dedekindZeta K s) := by
  simpa only [logDeriv_apply] using LSeries_idealMangoldt_eq_neg_logDeriv K hs

end

end Erdos980.NaturalChebotarev.IdealMangoldt

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveProgressionBudget
import ErdosProblems.Erdos48.PowerSievePrimeChainAssembly
import ErdosProblems.Erdos48.PowerSieveDyadicBadRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Absorption of the pointwise power-sieve envelope

This file closes the last numerical estimate in the pointwise progression
budget.  The principal beta-sieve term is summed with the fixed-product
reciprocal-totient estimate.  The two Bombieri--Vinogradov remainder terms
are absorbed respectively by the hundredth logarithmic power and by the
twenty-`L` power gap between the residual scale and the endpoint.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

open BoundedGaps.Maynard

private def powerSieveEta (Aβ : ℝ) (S : ℕ) : ℝ :=
  (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)

private theorem powerSieveEta_nonneg
    {Aβ : ℝ} (hAβ : 0 ≤ Aβ) (S : ℕ) :
    0 ≤ powerSieveEta Aβ S := by
  unfold powerSieveEta
  positivity

private theorem log_powerSieveX_eq (n L : ℕ) :
    Real.log (powerSieveX n L : ℝ) =
      ((240 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [powerSieveX, Nat.cast_pow, Real.log_pow]

private theorem log_powerSieveCofactorBound_eq (n L : ℕ) :
    Real.log (powerSieveCofactorBound n L : ℝ) =
      14 * Real.log (n : ℝ) := by
  rw [powerSieveCofactorBound, Nat.cast_pow, Real.log_pow]
  norm_num

private theorem log_powerSieveResidualCutoff_eq (n L : ℕ) :
    Real.log (powerSieveResidualCutoff n L : ℝ) =
      ((100 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [powerSieveResidualCutoff, Nat.cast_pow, Real.log_pow]

private theorem log_powerSieveSmallPrimeBound_eq (n L S : ℕ) :
    Real.log (powerSieveSmallPrimeBound n L S : ℝ) =
      ((L / (S + 1) : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [powerSieveSmallPrimeBound, Nat.cast_pow, Real.log_pow]

private theorem half_div_le_nat_div_cast
    {L S : ℕ} (hSL : S + 1 ≤ L) :
    (L : ℝ) / (2 * (S + 1 : ℝ)) ≤ (L / (S + 1) : ℕ) := by
  have hd : 0 < S + 1 := by omega
  have hk : 1 ≤ L / (S + 1) := by
    rw [Nat.one_le_iff_ne_zero]
    exact (Nat.div_pos hSL (by omega)).ne'
  have hlt : L < (L / (S + 1) + 1) * (S + 1) :=
    by simpa [mul_comm] using Nat.lt_mul_div_succ L hd
  have hnat : L ≤ 2 * (S + 1) * (L / (S + 1)) := by
    nlinarith
  have hreal : (L : ℝ) ≤
      (2 * (S + 1 : ℝ)) * ((L / (S + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (S + 1 : ℝ))).2
    (by simpa [mul_comm] using hreal)

private theorem quotient_mul_modulus_le_two_mul_endpoint
    {x d b : ℕ} (hx : 1 ≤ x) (hd : 0 < d) (hb : 0 < b) :
    ((((x + 1) / (d * b) : ℕ) : ℝ)) * ((d * b : ℕ) : ℝ) ≤
      2 * (x : ℝ) := by
  have hnat : d * b * ((x + 1) / (d * b)) ≤ x + 1 :=
    Nat.mul_div_le (x + 1) (d * b)
  have hcast : (((d * b) * ((x + 1) / (d * b)) : ℕ) : ℝ) ≤
      (x + 1 : ℕ) := by exact_mod_cast hnat
  have hxone : ((x + 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
    exact_mod_cast (show x + 1 ≤ 2 * x by omega)
  calc
    ((((x + 1) / (d * b) : ℕ) : ℝ)) * ((d * b : ℕ) : ℝ) =
        (((d * b) * ((x + 1) / (d * b)) : ℕ) : ℝ) := by
          push_cast
          ring
    _ ≤ ((x + 1 : ℕ) : ℝ) := hcast
    _ ≤ 2 * (x : ℝ) := hxone

/-- A finite, reusable upper bound for the exact pointwise envelope.  It
separates the beta-sieve main term, the pointwise BV error, and the residual
BV error. -/
theorem powerSievePointwiseEnvelope_le_crude_of_root_le
    {Aβ Cπ CV CBV : ℝ} {S n L Q q r : ℕ}
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV) (hCBV : 0 ≤ CBV)
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hSL : S + 1 ≤ L)
    (hQ : 1 ≤ Q) (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hqSmooth : q ≤ powerSieveSmoothBound n L)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
      (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ)) +
      (2 * CBV * (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100) +
      (powerSieveCofactorBound n L : ℝ) * CBV *
        (powerSieveResidualCutoff n L : ℝ) := by
  let x := powerSieveX n L
  let d := q * r
  let B := powerSieveCofactorBound n L
  let z := powerSieveResidualCutoff n L
  let y := powerSieveSmallPrimeBound n L S
  let eta := powerSieveEta Aβ S
  have hnOne : 1 ≤ n := by omega
  have hxOne : 1 ≤ x := by
    dsimp [x, powerSieveX]
    exact Nat.one_le_pow _ _ (by omega)
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  have hdPos : 0 < d := by dsimp [d]; positivity
  have hBPos : 0 < B := by dsimp [B, powerSieveCofactorBound]; positivity
  have hzTwo : 2 ≤ z := by
    dsimp [z, powerSieveResidualCutoff]
    exact (show 2 ≤ n by omega).trans
      (Nat.le_pow (by omega : 0 < 100 * L))
  have hyOne : 1 < y := one_lt_powerSieveSmallPrimeBound (by omega) hSL
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hyOne)
  have hphiD : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hdPos
  have heta : 0 ≤ eta := by
    dsimp [eta]
    exact powerSieveEta_nonneg hAβ S
  let main : ℕ → ℝ := fun b ↦
    Cπ * ((((x + 1) / (d * b) : ℕ) : ℝ)) /
        Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) *
      ((1 + eta) *
        (CV * ((d * b : ℕ) : ℝ) /
          (Nat.totient (d * b) : ℝ) / Real.log (y : ℝ)))
  let err : ℕ → ℝ := fun b ↦
    CBV * ((((x + 1) / (d * b) : ℕ) : ℝ)) /
      Real.rpow
        (Real.log ((((x + 1) / (d * b) : ℕ) : ℝ))) 100
  let residual : ℝ :=
    CBV * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) 100
  have hmain :
      (∑ b ∈ Finset.Icc 1 B, main b) ≤
        (8 * Cπ * (1 + eta) * CV * (x : ℝ) *
            (1 + Real.log (B : ℝ))) /
          ((Nat.totient d : ℝ) * Real.log (z : ℝ) *
            Real.log (y : ℝ)) := by
    have hpoint : ∀ b ∈ Finset.Icc 1 B,
        main b ≤
          (2 * Cπ * (1 + eta) * CV * (x : ℝ) /
            (Real.log (z : ℝ) * Real.log (y : ℝ))) *
              ((Nat.totient (d * b) : ℝ))⁻¹ := by
      intro b hb
      have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
      have hquot := powerSieve_residualCutoff_le_quotient_of_root_le
        hn hL hqSmooth hqLower hqUpper hr hb
      have hlogU : Real.log (z : ℝ) ≤
          Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hquot
      have hphi : (0 : ℝ) < Nat.totient (d * b) := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hdPos hbPos)
      have hmul := quotient_mul_modulus_le_two_mul_endpoint
        hxOne hdPos hbPos
      dsimp only [main]
      calc
        Cπ * ((((x + 1) / (d * b) : ℕ) : ℝ)) /
              Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) *
            ((1 + eta) *
              (CV * ((d * b : ℕ) : ℝ) /
                (Nat.totient (d * b) : ℝ) / Real.log (y : ℝ))) =
            (Cπ * (1 + eta) * CV) *
              (((((x + 1) / (d * b) : ℕ) : ℝ)) *
                ((d * b : ℕ) : ℝ)) *
              (Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)))⁻¹ *
              (Real.log (y : ℝ))⁻¹ *
              ((Nat.totient (d * b) : ℝ))⁻¹ := by ring
        _ ≤ (Cπ * (1 + eta) * CV) * (2 * (x : ℝ)) *
              (Real.log (z : ℝ))⁻¹ *
              (Real.log (y : ℝ))⁻¹ *
              ((Nat.totient (d * b) : ℝ))⁻¹ := by
          gcongr
        _ = (2 * Cπ * (1 + eta) * CV * (x : ℝ) /
              (Real.log (z : ℝ) * Real.log (y : ℝ))) *
                ((Nat.totient (d * b) : ℝ))⁻¹ := by ring
    calc
      (∑ b ∈ Finset.Icc 1 B, main b) ≤
          ∑ b ∈ Finset.Icc 1 B,
            (2 * Cπ * (1 + eta) * CV * (x : ℝ) /
              (Real.log (z : ℝ) * Real.log (y : ℝ))) *
                ((Nat.totient (d * b) : ℝ))⁻¹ := by
        exact Finset.sum_le_sum fun b hb ↦ hpoint b hb
      _ = (2 * Cπ * (1 + eta) * CV * (x : ℝ) /
              (Real.log (z : ℝ) * Real.log (y : ℝ))) *
            (∑ b ∈ Finset.Icc 1 B,
              ((Nat.totient (d * b) : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * Cπ * (1 + eta) * CV * (x : ℝ) /
              (Real.log (z : ℝ) * Real.log (y : ℝ))) *
            ((Nat.totient d : ℝ)⁻¹ *
              (4 * (1 + Real.log (B : ℝ)))) := by
        gcongr
        exact sum_inv_totient_fixed_product_le_log hdPos hBPos
      _ = (8 * Cπ * (1 + eta) * CV * (x : ℝ) *
              (1 + Real.log (B : ℝ))) /
            ((Nat.totient d : ℝ) * Real.log (z : ℝ) *
              Real.log (y : ℝ)) := by field_simp; ring
  have herr :
      (∑ b ∈ Finset.Icc 1 B, err b) ≤
        (2 * CBV * (x : ℝ) * (1 + Real.log (B : ℝ))) /
          ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100) := by
    have hpoint : ∀ b ∈ Finset.Icc 1 B,
        err b ≤
          (2 * CBV * (x : ℝ) /
            ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100)) *
              (b : ℝ)⁻¹ := by
      intro b hb
      have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
      have hquot := powerSieve_residualCutoff_le_quotient_of_root_le
        hn hL hqSmooth hqLower hqUpper hr hb
      have hlogU : Real.log (z : ℝ) ≤
          Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hquot
      have hmul := quotient_mul_modulus_le_two_mul_endpoint
        hxOne hdPos hbPos
      have hphiLe : (Nat.totient d : ℝ) ≤ d := by
        exact_mod_cast Nat.totient_le d
      have hpow : Real.log (z : ℝ) ^ 100 ≤
          Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ 100 := by
        exact pow_le_pow_left₀ hlogz.le hlogU 100
      dsimp only [err]
      rw [show Real.rpow
        (Real.log ((((x + 1) / (d * b) : ℕ) : ℝ))) 100 =
          Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ (100 : ℕ) by
            rw [← Real.rpow_natCast]; norm_num]
      calc
        CBV * ((((x + 1) / (d * b) : ℕ) : ℝ)) /
              Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ 100 =
            CBV *
              (((((x + 1) / (d * b) : ℕ) : ℝ) * ((d * b : ℕ) : ℝ)) /
                (((d * b : ℕ) : ℝ) *
                  Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ 100)) := by
            field_simp
        _ = (CBV *
              ((((x + 1) / (d * b) : ℕ) : ℝ) * ((d * b : ℕ) : ℝ))) /
              (((d * b : ℕ) : ℝ) *
                Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ 100) := by
          ring
        _ ≤ (CBV * (2 * (x : ℝ))) /
              (((d * b : ℕ) : ℝ) *
                Real.log ((((x + 1) / (d * b) : ℕ) : ℝ)) ^ 100) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hmul hCBV
          · positivity
        _ ≤ CBV * (2 * (x : ℝ)) /
              (((d * b : ℕ) : ℝ) *
                Real.log (z : ℝ) ^ 100) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hpow (by positivity))
        _ ≤ CBV * (2 * (x : ℝ)) /
              (((Nat.totient d : ℝ) * (b : ℝ)) *
                Real.log (z : ℝ) ^ 100) := by
          gcongr
          push_cast
          nlinarith
        _ = (2 * CBV * (x : ℝ) /
              ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100)) *
                (b : ℝ)⁻¹ := by field_simp
    calc
      (∑ b ∈ Finset.Icc 1 B, err b) ≤
          ∑ b ∈ Finset.Icc 1 B,
            (2 * CBV * (x : ℝ) /
              ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100)) *
                (b : ℝ)⁻¹ := by
        exact Finset.sum_le_sum fun b hb ↦ hpoint b hb
      _ = (2 * CBV * (x : ℝ) /
              ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100)) *
            (∑ b ∈ Finset.Icc 1 B, (b : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * CBV * (x : ℝ) /
              ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100)) *
            (1 + Real.log (B : ℝ)) := by
        gcongr
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast] using harmonic_le_one_add_log B
      _ = (2 * CBV * (x : ℝ) * (1 + Real.log (B : ℝ))) /
            ((Nat.totient d : ℝ) * Real.log (z : ℝ) ^ 100) := by
        ring
  have hresidual :
      (∑ _b ∈ Finset.Icc 1 B, residual) ≤
        (B : ℝ) * CBV * (z : ℝ) := by
    have hlogOne : 1 ≤ Real.log (z : ℝ) := by
      rw [log_powerSieveResidualCutoff_eq]
      have hlogn : 1 ≤ Real.log (n : ℝ) := one_le_log_natCast hn
      have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
      push_cast
      nlinarith
    have hrpowOne : 1 ≤ Real.rpow (Real.log (z : ℝ)) 100 :=
      Real.one_le_rpow hlogOne (by norm_num)
    have hres : residual ≤ CBV * (z : ℝ) := by
      dsimp only [residual]
      exact div_le_self (mul_nonneg hCBV (by positivity)) hrpowOne
    calc
      (∑ _b ∈ Finset.Icc 1 B, residual) ≤
          ∑ _b ∈ Finset.Icc 1 B, CBV * (z : ℝ) := by
        exact Finset.sum_le_sum fun b hb ↦ hres
      _ = (B : ℝ) * CBV * (z : ℝ) := by
        have hcard : (Finset.Icc 1 B).card = B := by
          simp only [Nat.card_Icc]
          omega
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        push_cast
        ring
  dsimp only [powerSievePointwiseEnvelope]
  change (Finset.Icc 1 B).sum (fun b ↦ main b + err b + residual) ≤ _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact add_le_add (add_le_add hmain herr) hresidual

/-- Compatibility form for a complete dyadic shell. -/
theorem powerSievePointwiseEnvelope_le_crude
    {Aβ Cπ CV CBV : ℝ} {S n L Q q r : ℕ}
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV) (hCBV : 0 ≤ CBV)
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hSL : S + 1 ≤ L)
    (hQ : 1 ≤ Q) (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hQupper : 2 * Q ≤ powerSieveSmoothBound n L)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
      (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ)) +
      (2 * CBV * (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100) +
      (powerSieveCofactorBound n L : ℝ) * CBV *
        (powerSieveResidualCutoff n L : ℝ) :=
  powerSievePointwiseEnvelope_le_crude_of_root_le
    hAβ hCπ hCV hCBV hn hL hSL hQ hqLower hqUpper
      (hqUpper.trans hQupper) hr

private theorem scaled_fraction_le_twelfth
    {x p a D ell : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (hD : 0 < D) (hell : 0 < ell)
    (hnum : 12 * a * ell ≤ D) :
    a * x / (p * D) ≤ x / (12 * p * ell) := by
  rw [div_le_div_iff₀ (mul_pos hp hD)
    (mul_pos (mul_pos (by norm_num) hp) hell)]
  calc
    a * x * (12 * p * ell) = x * p * (12 * a * ell) := by ring
    _ ≤ x * p * D :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg hx hp.le)
    _ = x * (p * D) := by ring

/-- The exact envelope is at most one quarter of the progression main term
once the three displayed finite numerical inequalities hold. -/
theorem powerSievePointwiseEnvelope_le_quarter_of_numeric_of_root_le
    {Aβ Cπ CV CBV : ℝ} {S n L Q q r : ℕ}
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV) (hCBV : 0 ≤ CBV)
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hSL : S + 1 ≤ L)
    (hQ : 1 ≤ Q) (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hqSmooth : q ≤ powerSieveSmoothBound n L)
    (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hmainNum :
      12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
          Real.log (powerSieveX n L : ℝ) ≤
        Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ))
    (herrNum :
      24 * CBV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
          Real.log (powerSieveX n L : ℝ) ≤
        Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100)
    (hresNum :
      12 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) *
          ((powerSieveCofactorBound n L : ℝ) * CBV *
            (powerSieveResidualCutoff n L : ℝ)) ≤
        (powerSieveX n L : ℝ)) :
    powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
      (powerSieveX n L : ℝ) /
        (4 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ)) := by
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  have hphi : (0 : ℝ) < Nat.totient (q * r) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hqPos hrPos)
  have hlogx : 0 < Real.log (powerSieveX n L : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < powerSieveX n L by
      unfold powerSieveX
      exact one_lt_pow₀ (by omega) (by omega))
  have hlogz : 0 < Real.log (powerSieveResidualCutoff n L : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < powerSieveResidualCutoff n L by
      unfold powerSieveResidualCutoff
      exact one_lt_pow₀ (by omega) (by omega))
  have hyNat : 1 < powerSieveSmallPrimeBound n L S :=
    one_lt_powerSieveSmallPrimeBound (by omega : 2 ≤ n) hSL
  have hlogy : 0 < Real.log (powerSieveSmallPrimeBound n L S : ℝ) :=
    Real.log_pos (by exact_mod_cast hyNat)
  have hx : (0 : ℝ) ≤ powerSieveX n L := by positivity
  have hmain := scaled_fraction_le_twelfth hx hphi
    (mul_pos hlogz hlogy) hlogx hmainNum
  have herr := scaled_fraction_le_twelfth
    (x := (powerSieveX n L : ℝ))
    (p := (Nat.totient (q * r) : ℝ))
    (a := 2 * CBV *
      (1 + Real.log (powerSieveCofactorBound n L : ℝ)))
    (D := Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100)
    (ell := Real.log (powerSieveX n L : ℝ))
    hx hphi (pow_pos hlogz 100) hlogx (by
      calc
        12 * (2 * CBV *
            (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
              Real.log (powerSieveX n L : ℝ) =
          24 * CBV *
            (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
              Real.log (powerSieveX n L : ℝ) := by ring
        _ ≤ _ := herrNum)
  have hres :
      (powerSieveCofactorBound n L : ℝ) * CBV *
          (powerSieveResidualCutoff n L : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) := by
    rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hphi) hlogx)]
    calc
      ((powerSieveCofactorBound n L : ℝ) * CBV *
          (powerSieveResidualCutoff n L : ℝ)) *
            (12 * (Nat.totient (q * r) : ℝ) *
              Real.log (powerSieveX n L : ℝ)) =
        12 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) *
            ((powerSieveCofactorBound n L : ℝ) * CBV *
              (powerSieveResidualCutoff n L : ℝ)) := by ring
      _ ≤ _ := hresNum
  apply (powerSievePointwiseEnvelope_le_crude_of_root_le hAβ hCπ hCV hCBV hn hL
    hSL hQ hqLower hqUpper hqSmooth hr).trans
  have hmain' :
      (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ)) ≤
        (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) := by
    convert hmain using 1 <;> ring
  have herr' :
      (2 * CBV * (powerSieveX n L : ℝ) *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) /
        ((Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100) ≤
        (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) := by
    convert herr using 1 <;> ring
  have hsum := add_le_add (add_le_add hmain' herr') hres
  calc
    _ ≤ (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) +
        (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) +
        (powerSieveX n L : ℝ) /
          (12 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) := hsum
    _ = (powerSieveX n L : ℝ) /
        (4 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ)) := by field_simp; ring

/-- Compatibility numerical wrapper for a complete dyadic shell. -/
theorem powerSievePointwiseEnvelope_le_quarter_of_numeric
    {Aβ Cπ CV CBV : ℝ} {S n L Q q r : ℕ}
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV) (hCBV : 0 ≤ CBV)
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hSL : S + 1 ≤ L)
    (hQ : 1 ≤ Q) (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hQupper : 2 * Q ≤ powerSieveSmoothBound n L)
    (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hmainNum :
      12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
          Real.log (powerSieveX n L : ℝ) ≤
        Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ))
    (herrNum :
      24 * CBV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
          Real.log (powerSieveX n L : ℝ) ≤
        Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100)
    (hresNum :
      12 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) *
          ((powerSieveCofactorBound n L : ℝ) * CBV *
            (powerSieveResidualCutoff n L : ℝ)) ≤
        (powerSieveX n L : ℝ)) :
    powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
      (powerSieveX n L : ℝ) /
        (4 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ)) :=
  powerSievePointwiseEnvelope_le_quarter_of_numeric_of_root_le
    hAβ hCπ hCV hCBV hn hL hSL hQ hqLower hqUpper
      (hqUpper.trans hQupper) hr hmainNum herrNum hresNum

private theorem powerSieve_main_numeric
    {Aβ Cπ CV : ℝ} {S n L : ℕ}
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV)
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hSL : S + 1 ≤ L)
    (hLargeL :
      6912 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (S + 1 : ℝ) ≤ L) :
    12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
        (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
        Real.log (powerSieveX n L : ℝ) ≤
      Real.log (powerSieveResidualCutoff n L : ℝ) *
        Real.log (powerSieveSmallPrimeBound n L S : ℝ) := by
  let c : ℝ := Cπ * (1 + powerSieveEta Aβ S) * CV
  let ell : ℝ := Real.log (n : ℝ)
  let D : ℝ := S + 1
  have hc : 0 ≤ c := by
    dsimp [c]
    have heta := powerSieveEta_nonneg hAβ S
    positivity
  have hell : 1 ≤ ell := by
    dsimp [ell]
    exact one_le_log_natCast hn
  have hD : 0 < D := by dsimp [D]; positivity
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hB : 1 + Real.log (powerSieveCofactorBound n L : ℝ) ≤
      15 * ell := by
    rw [log_powerSieveCofactorBound_eq]
    dsimp [ell]
    linarith
  have hsmall : (L : ℝ) / (2 * D) * ell ≤
      Real.log (powerSieveSmallPrimeBound n L S : ℝ) := by
    rw [log_powerSieveSmallPrimeBound_eq]
    dsimp [D, ell]
    exact mul_le_mul_of_nonneg_right (half_div_le_nat_div_cast hSL)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  have hlarge : 6912 * c * D ≤ (L : ℝ) := by
    simpa only [c, D, mul_assoc] using hLargeL
  have hscaled := mul_le_mul_of_nonneg_right hlarge
    (show 0 ≤ 50 * (L : ℝ) * ell ^ 2 / D by positivity)
  calc
    12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
          Real.log (powerSieveX n L : ℝ) ≤
        345600 * c * (L : ℝ) * ell ^ 2 := by
      rw [log_powerSieveX_eq]
      push_cast
      calc
        12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
            (1 + Real.log (powerSieveCofactorBound n L : ℝ))) *
              (240 * (L : ℝ) * Real.log (n : ℝ)) ≤
          12 * (8 * Cπ * (1 + powerSieveEta Aβ S) * CV *
            (15 * ell)) * (240 * (L : ℝ) * ell) := by
              dsimp [ell]
              gcongr
              positivity [powerSieveEta_nonneg hAβ S]
        _ = 345600 * c * (L : ℝ) * ell ^ 2 := by
          dsimp [c]
          ring
    _ = (6912 * c * D) *
          (50 * (L : ℝ) * ell ^ 2 / D) := by
      field_simp
      ring
    _ ≤ (L : ℝ) * (50 * (L : ℝ) * ell ^ 2 / D) := hscaled
    _ = (100 * (L : ℝ) * ell) *
          ((L : ℝ) / (2 * D) * ell) := by
      field_simp
      ring
    _ ≤ (100 * (L : ℝ) * ell) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = Real.log (powerSieveResidualCutoff n L : ℝ) *
          Real.log (powerSieveSmallPrimeBound n L S : ℝ) := by
      rw [log_powerSieveResidualCutoff_eq]
      dsimp [ell]
      push_cast
      ring

private theorem eventually_const_mul_log_sq_le_nat_pow
    (D : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      D * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ k := by
  by_cases hD : D ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (mul_nonpos_of_nonpos_of_nonneg hD (sq_nonneg _)).trans
      (by positivity)
  · have hDpos : 0 < D := lt_of_not_ge hD
    have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hkreal).bound
        (show 0 < (1 / D : ℝ) by positivity)
    have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
    filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg
      (Real.rpow_nonneg (by positivity) _)] at hn
    have hmul := mul_le_mul_of_nonneg_left hn hDpos.le
    field_simp [hDpos.ne'] at hmul
    simpa only [Real.rpow_two, Real.rpow_natCast] using hmul

private theorem eventually_powerSieve_error_numeric
    (CBV : ℝ) (hCBV : 0 ≤ CBV) (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      24 * CBV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
          Real.log (powerSieveX n L : ℝ) ≤
        Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100 := by
  have hlarge : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 98) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (98 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconst : ∀ᶠ n : ℕ in atTop,
      86400 * CBV * (L : ℝ) ≤ Real.log (n : ℝ) ^ 98 :=
    hlarge.eventually_ge_atTop (86400 * CBV * (L : ℝ))
  filter_upwards [hconst, eventually_ge_atTop 4] with n hconst hn
  let ell : ℝ := Real.log (n : ℝ)
  have hell : 1 ≤ ell := by
    dsimp [ell]
    exact one_le_log_natCast hn
  have hB : 1 + Real.log (powerSieveCofactorBound n L : ℝ) ≤
      15 * ell := by
    rw [log_powerSieveCofactorBound_eq]
    dsimp [ell]
    linarith
  have hconst' :
      (86400 * CBV * (L : ℝ)) * ell ^ 2 ≤ ell ^ 100 := by
    have hmul := mul_le_mul_of_nonneg_right hconst (sq_nonneg ell)
    simpa only [ell, ← pow_add] using hmul
  calc
    24 * CBV *
          (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
          Real.log (powerSieveX n L : ℝ) ≤
        86400 * CBV * (L : ℝ) * ell ^ 2 := by
      rw [log_powerSieveX_eq]
      push_cast
      calc
        24 * CBV *
              (1 + Real.log (powerSieveCofactorBound n L : ℝ)) *
              (240 * (L : ℝ) * Real.log (n : ℝ)) ≤
            24 * CBV * (15 * ell) *
              (240 * (L : ℝ) * ell) := by
          gcongr
        _ = 86400 * CBV * (L : ℝ) * ell ^ 2 := by ring
    _ ≤ ell ^ 100 := by simpa only [mul_assoc] using hconst'
    _ ≤ (100 * (L : ℝ) * ell) ^ 100 := by
      gcongr
      nlinarith [show (1 : ℝ) ≤ L by exact_mod_cast hL]
    _ = Real.log (powerSieveResidualCutoff n L : ℝ) ^ 100 := by
      rw [log_powerSieveResidualCutoff_eq]
      dsimp [ell]
      push_cast
      rfl

private theorem eventually_powerSieve_residual_numeric
    (CBV : ℝ) (hCBV : 0 ≤ CBV) (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      12 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) *
          ((powerSieveCofactorBound n L : ℝ) * CBV *
            (powerSieveResidualCutoff n L : ℝ)) ≤
        (powerSieveX n L : ℝ) := by
  let D : ℝ := 2880 * CBV * (L : ℝ)
  filter_upwards
    [eventually_const_mul_log_sq_le_nat_pow D 6 (by norm_num),
      eventually_ge_atTop 4]
    with n hlog hn Q q r hQ hqLower hqUpper hqSmooth hr
  let ell : ℝ := Real.log (n : ℝ)
  have hell : 1 ≤ ell := by
    dsimp [ell]
    exact one_le_log_natCast hn
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hqrNat : q * r ≤ n ^ (120 * L) :=
    (powerSieve_root_mul_aux_le_of_root_le hn hL hqSmooth hqUpper hr).trans
      (pow_le_pow_right' (by omega : 1 ≤ n) (by omega))
  have hphi : (Nat.totient (q * r) : ℝ) ≤ (n : ℝ) ^ (120 * L) := by
    exact_mod_cast (Nat.totient_le (q * r)).trans hqrNat
  have hcoef : 2880 * CBV * (L : ℝ) * ell ≤ (n : ℝ) ^ 6 := by
    have hellSq : ell ≤ ell ^ 2 := by nlinarith
    calc
      2880 * CBV * (L : ℝ) * ell ≤
          2880 * CBV * (L : ℝ) * ell ^ 2 := by
        gcongr
      _ ≤ (n : ℝ) ^ 6 := by
        simpa only [D, mul_assoc] using hlog
  calc
    12 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) *
          ((powerSieveCofactorBound n L : ℝ) * CBV *
            (powerSieveResidualCutoff n L : ℝ)) ≤
        12 * ((n : ℝ) ^ (120 * L)) *
          (240 * (L : ℝ) * ell) *
          (((n : ℝ) ^ 14) * CBV * ((n : ℝ) ^ (100 * L))) := by
      rw [log_powerSieveX_eq]
      simp only [powerSieveCofactorBound, powerSieveResidualCutoff,
        Nat.cast_pow]
      push_cast
      gcongr
    _ = (2880 * CBV * (L : ℝ) * ell) *
          ((n : ℝ) ^ (120 * L) * (n : ℝ) ^ 14 *
            (n : ℝ) ^ (100 * L)) := by ring
    _ ≤ (n : ℝ) ^ 6 *
          ((n : ℝ) ^ (120 * L) * (n : ℝ) ^ 14 *
            (n : ℝ) ^ (100 * L)) := by
      gcongr
    _ = (n : ℝ) ^ (220 * L + 20) := by
      rw [show 220 * L + 20 = 6 + ((120 * L) + 14 + (100 * L)) by omega]
      simp only [pow_add]
    _ ≤ (n : ℝ) ^ (240 * L) :=
      pow_le_pow_right₀ hnReal (by omega)
    _ = (powerSieveX n L : ℝ) := by
      simp only [powerSieveX, Nat.cast_pow]

/-- For fixed sieve constants and depth, choosing `L` sufficiently large
absorbs the pointwise beta-sieve envelope uniformly over every admissible
dyadic root and every auxiliary prime. -/
theorem exists_eventually_powerSievePointwiseEnvelope_le_quarter_of_root_le
    (Aβ Cπ CV CBV : ℝ) (S : ℕ)
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV)
    (hCBV : 0 ≤ CBV) :
    ∃ L₀ : ℕ, S + 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
            (powerSieveX n L : ℝ) /
              (4 * (Nat.totient (q * r) : ℝ) *
                Real.log (powerSieveX n L : ℝ)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge
    (6912 * Cπ * (1 + powerSieveEta Aβ S) * CV * (S + 1 : ℝ))
  refine ⟨max (S + 1) m, le_max_left _ _, ?_⟩
  intro L hL₀
  have hSL : S + 1 ≤ L := (le_max_left (S + 1) m).trans hL₀
  have hL : 1 ≤ L := by omega
  have hmL : m ≤ L := (le_max_right (S + 1) m).trans hL₀
  have hLargeL :
      6912 * Cπ * (1 + powerSieveEta Aβ S) * CV *
          (S + 1 : ℝ) ≤ (L : ℝ) :=
    hm.trans (by exact_mod_cast hmL)
  filter_upwards
    [eventually_powerSieve_error_numeric CBV hCBV L hL,
      eventually_powerSieve_residual_numeric CBV hCBV L hL,
      eventually_ge_atTop 4]
    with n herr hres hn Q q r hQ hqLower hqUpper hqSmooth hr
  apply powerSievePointwiseEnvelope_le_quarter_of_numeric_of_root_le
    hAβ hCπ hCV hCBV hn hL hSL hQ hqLower hqUpper hqSmooth hr
  · exact powerSieve_main_numeric hAβ hCπ hCV hn hL hSL hLargeL
  · exact herr
  · exact hres Q q r hQ hqLower hqUpper hqSmooth hr

/-- Compatibility form of the eventual envelope bound for complete shells. -/
theorem exists_eventually_powerSievePointwiseEnvelope_le_quarter
    (Aβ Cπ CV CBV : ℝ) (S : ℕ)
    (hAβ : 0 ≤ Aβ) (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV)
    (hCBV : 0 ≤ CBV) :
    ∃ L₀ : ℕ, S + 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          2 * Q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
            (powerSieveX n L : ℝ) /
              (4 * (Nat.totient (q * r) : ℝ) *
                Real.log (powerSieveX n L : ℝ)) := by
  obtain ⟨L₀, hSL₀, hbound⟩ :=
    exists_eventually_powerSievePointwiseEnvelope_le_quarter_of_root_le
      Aβ Cπ CV CBV S hAβ hCπ hCV hCBV
  refine ⟨L₀, hSL₀, ?_⟩
  intro L hL₀
  filter_upwards [hbound L hL₀] with n hbound Q q r hQ hqLower
    hqUpper hQupper hr
  exact hbound Q q r hQ hqLower hqUpper (hqUpper.trans hQupper) hr

/-- The unconditional pointwise large-factor estimate in a possibly partial
top dyadic shell. -/
theorem exists_eventually_representedLargeFactorPrimes_le_pointwiseEnvelope_of_root_le :
    ∃ Aβ Cπ CV CBV : ℝ, ∃ S X₀ : ℕ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧ 0 ≤ CBV ∧
      101 ≤ S ∧ Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 ∧
      PrimeLevelWitness (1 / 4 : ℝ) 100 CBV X₀ ∧
      ∀ L : ℕ, S + 1 ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) ≤
            powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hpoint⟩ :=
    exists_powerSieve_representedLargeFactorPrimes_pointwise_upper_bound_of_root_le
  obtain ⟨S, hS, hlogAβ⟩ := exists_admissible_powerSieveDepth Aβ
  obtain ⟨CBV, X₀, hw⟩ :=
    exists_quarter_primeLevelWitness 100 (by norm_num)
  refine ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hw.1,
    hS, hlogAβ, hw, ?_⟩
  intro L hSL
  filter_upwards [eventually_ge_atTop (max X₀ 4)] with n hn
  intro Q q r hQ hqLower hqUpper hqSmooth hr
  have hnFour : 4 ≤ n := (le_max_right X₀ 4).trans hn
  have hX₀n : X₀ ≤ n := (le_max_left X₀ 4).trans hn
  have hX₀pow : X₀ ≤ n ^ L :=
    hX₀n.trans (Nat.le_pow (by omega : 0 < L))
  have hbound := hpoint (Bexp := (100 : ℝ)) (CBV := CBV)
    (X₀ := X₀) (n := n) (L := L) (S := S) (Q := Q)
    (q := q) (r := r) hnFour hS hSL hQ hqLower hqUpper hqSmooth hr
    hlogAβ hw hX₀pow
  simpa only [powerSievePointwiseEnvelope] using hbound

/-- The endpoint PNT errors and the concrete good-root weight fit the
progression budget under the literal root cutoff, including the top partial
shell. -/
theorem eventually_represented_add_goodRootWeight_le_budget_of_card_of_root_le
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (4 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
          powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r := by
  filter_upwards
    [eventually_represented_add_goodRootWeight_le_budget_of_bounds L hL,
      eventually_powerSieve_psi_sub_theta_le L hL,
      eventually_powerSieve_log_product_sq_le L hL,
      eventually_ge_atTop 4]
    with n hbudget hprimePower hlogError hn Q q r hQ hqLower hqUpper
      hqSmooth hr hrepresented
  have hqrUpper : q * r ≤ n ^ (120 * L - 2) :=
    powerSieve_root_mul_aux_le_of_root_le hn hL hqSmooth hqUpper hr
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  exact hbudget Q q r hQ hqLower hqUpper hr hrepresented
    (hlogError (q * r) (Nat.mul_pos hqPos hrPos) hqrUpper)
    (hprimePower (q * r) (Nat.mul_pos hqPos hrPos) hqrUpper)

/-- Fully unconditional represented-plus-weight budget under the actual root
cutoff.  This is the interface required by the endpoint-split prefix input,
including its final partial dyadic shell. -/
theorem exists_eventually_represented_add_goodRootWeight_le_budget_of_root_le :
    ∃ Aβ Cπ CV CBV : ℝ, ∃ S X₀ L₀ : ℕ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧ 0 ≤ CBV ∧
      101 ≤ S ∧ Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 ∧
      PrimeLevelWitness (1 / 4 : ℝ) 100 CBV X₀ ∧
      S + 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) +
              powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
            powerSieveProgressionBudget (powerSieveX n L) q r := by
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hCBV, hS,
      hlogAβ, hw, hrepresented⟩ :=
    exists_eventually_representedLargeFactorPrimes_le_pointwiseEnvelope_of_root_le
  obtain ⟨L₀, hSL₀, henvelope⟩ :=
    exists_eventually_powerSievePointwiseEnvelope_le_quarter_of_root_le
      Aβ Cπ CV CBV S (zero_le_one.trans hAβ) hCπ.le hCV.le hCBV
  refine ⟨Aβ, Cπ, CV, CBV, S, X₀, L₀, hAβ, hCπ, hCV, hCBV,
    hS, hlogAβ, hw, hSL₀, ?_⟩
  intro L hL₀
  have hSL : S + 1 ≤ L := hSL₀.trans hL₀
  have hL : 1 ≤ L := by omega
  filter_upwards
    [hrepresented L hSL, henvelope L hL₀,
      eventually_represented_add_goodRootWeight_le_budget_of_card_of_root_le L hL]
    with n hrepresented henvelope hbudget Q q r hQ hqLower hqUpper hqSmooth hr
  apply hbudget Q q r hQ hqLower hqUpper hqSmooth hr
  exact (hrepresented Q q r hQ hqLower hqUpper hqSmooth hr).trans
    (henvelope Q q r hQ hqLower hqUpper hqSmooth hr)

/-- Direct specialization to the numerical field of
`PowerSieveEndpointSplitPrefixInput`.  Membership in the literal bad-root
set supplies `q ≤ u`; consequently no completeness assumption on the final
dyadic shell is present. -/
theorem exists_eventually_powerSieveEndpointSplit_numeric :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
        ∀ q ∈ powerSieveShiftedSmoothBadRoots n L
          (powerSieveGoodRootWeight n L),
        q ∈ powerSieveDyadicPrimeBlock Q →
        ∀ r ∈ powerSieveAuxPrimes n L Q,
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) +
              powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
            powerSieveProgressionBudget (powerSieveX n L) q r := by
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, L₀, hAβ, hCπ, hCV, hCBV,
      hS, hlogAβ, hw, hSL₀, hbudget⟩ :=
    exists_eventually_represented_add_goodRootWeight_le_budget_of_root_le
  refine ⟨L₀, by omega, ?_⟩
  intro L hL₀
  filter_upwards [hbudget L hL₀] with n hbudget
  intro Q hQ q hqBad hqBlock r hr
  have hqSmooth := (mem_powerSieveShiftedSmoothBadRoots.mp hqBad).2.1
  have hqDyadic := mem_powerSieveDyadicPrimeBlock.mp hqBlock
  exact hbudget Q q r hQ hqDyadic.1 hqDyadic.2.1 hqSmooth hr

/-- A completely unconditional represented-plus-weight progression budget.
All analytic constants and the sufficiently large exponent `L₀` are chosen
inside the theorem; the conclusion is uniform in each later dyadic block. -/
theorem exists_eventually_represented_add_goodRootWeight_le_budget :
    ∃ Aβ Cπ CV CBV : ℝ, ∃ S X₀ L₀ : ℕ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧ 0 ≤ CBV ∧
      101 ≤ S ∧ Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 ∧
      PrimeLevelWitness (1 / 4 : ℝ) 100 CBV X₀ ∧
      S + 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          2 * Q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) +
              powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
            powerSieveProgressionBudget (powerSieveX n L) q r := by
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hCBV, hS,
      hlogAβ, hw, hrepresented⟩ :=
    exists_eventually_representedLargeFactorPrimes_le_pointwiseEnvelope
  obtain ⟨L₀, hSL₀, henvelope⟩ :=
    exists_eventually_powerSievePointwiseEnvelope_le_quarter
      Aβ Cπ CV CBV S (zero_le_one.trans hAβ) hCπ.le hCV.le hCBV
  refine ⟨Aβ, Cπ, CV, CBV, S, X₀, L₀, hAβ, hCπ, hCV, hCBV,
    hS, hlogAβ, hw, hSL₀, ?_⟩
  intro L hL₀
  have hSL : S + 1 ≤ L := hSL₀.trans hL₀
  have hL : 1 ≤ L := by omega
  filter_upwards
    [hrepresented L hSL, henvelope L hL₀,
      eventually_represented_add_goodRootWeight_le_budget_of_card L hL]
    with n hrepresented henvelope hbudget Q q r hQ hqLower hqUpper hQupper hr
  apply hbudget Q q r hQ hqLower hqUpper hQupper hr
  exact (hrepresented Q q r hQ hqLower hqUpper hQupper hr).trans
    (henvelope Q q r hQ hqLower hqUpper hQupper hr)

/-- The normalized good-root weight is exactly the canonical raw threshold
after division by the auxiliary-counting loss `240000 * L^2`. -/
theorem powerSieveRawLower_eq_goodRootWeight_div
    (n L q : ℕ) :
    powerSieveRawLower n L q =
      powerSieveGoodRootWeight n L q / (240000 * (L : ℝ) ^ 2) := by
  unfold powerSieveRawLower powerSieveGoodRootWeight
  simp only [div_eq_mul_inv, mul_inv]
  ring

end

end Erdos48

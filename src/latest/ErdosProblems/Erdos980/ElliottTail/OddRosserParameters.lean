/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.OddRayNormRosser
import ErdosProblems.Erdos980.ElliottTail.OddAuxiliaryScaleCore
import ErdosProblems.Erdos980.ElliottTail.FixedRayCellCandidateData
import ErdosProblems.Erdos387.BinomialBetaCutoff

/-!
# Concrete numerical parameters for the odd norm Rosser sieve

This file selects the rational sieve-prime interval used for one fixed
number field, correction ideal, and ray modulus.  The lower endpoint is
larger than twice the effective norm-form dimension and larger than both
fixed moduli.  Consequently every selected prime is good for the correction
ideal, is coprime to the ray modulus, and has norm-zero density strictly
between zero and one.

Only numerical and local-density facts occur here.  Candidate realization,
exceptional-prime membership, and correction tags are deliberately absent.
-/

open Filter
open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddRosserParameters

open NumberField
open NumberField.mixedEmbedding
open LocalNormEuler
open LocalNormRootBound
open OddMediumParameters
open Erdos980.ElliottTail.OddAuxiliaryScale
open RayNormPrimeSieve
open FixedRayCellCandidateData
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaCutoff

/-- The rank of the Minkowski coordinate lattice. -/
def normSieveDegree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Nat.card (index K)

/-- We use dimension at least two so that the existing beta-sieve cutoff
theorems apply without a separate degree-one branch. -/
def normSieveDimension (K : Type*) [Field K] [NumberField K] : ℕ :=
  max 2 (normSieveDegree K)

/-- Fixed lower endpoint of the rational sieve interval.  Every selected
prime is larger than twice the effective dimension, the ray modulus, and
the norm of the correction ideal. -/
def normSieveLower
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) : ℕ :=
  max (2 * normSieveDimension K)
    (max f (Ideal.absNorm (J : Ideal (RingOfIntegers K))))

/-- Rational primes in the concrete interval `(normSieveLower, y]`. -/
def normSievePrimes
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ) : Finset ℕ :=
  Erdos851.sievePrimes (normSieveLower K J f) y

/-- The beta parameter used for the dimension-majorant Rosser sieve. -/
def normRosserBeta (K : Type*) [Field K] [NumberField K] : ℕ :=
  100 * normSieveDimension K

/-- The prime-local zero density of the fixed-ideal algebraic norm form. -/
def coordinateNormDensity
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) : ℝ :=
  ((coordinateAlgebraNormResidueSystem K J).rootCount K p : ℝ) /
    (p : ℝ) ^ normSieveDegree K

/-- The moving upper endpoint.  Taking a ceiling makes the elementary
comparison `x^eta ≤ y` exact, which is the direction required to recover
`1 / log x` from Mertens at the endpoint. -/
def normSieveUpper (eta : ℝ) (x : ℕ) : ℕ :=
  ⌈(x : ℝ) ^ eta⌉₊

/-- Nonnegativity of the fixed covolume-normalized generator-cell volume. -/
theorem generatorCellMainConstant_nonneg
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) :
    0 ≤ generatorCellMainConstant K J := by
  unfold generatorCellMainConstant
  positivity

/-- The unit-residue density is at most one, so after inserting the exact
height power the cell total mass is bounded by a fixed geometric coefficient
times the tensor density and x. -/
theorem rayCellTotalMass_le_tensor_mul_mainCoefficient_mul
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    {ell j f unitResidueCount x : ℕ} (hell : ell ≠ 0) (hf : f ≠ 0)
    {height : ℝ}
    (hunit : unitResidueCount ≤ f ^ Nat.card (index K))
    (hheight : height ^ Nat.card (index K) =
      ((x * Ideal.absNorm (J : Ideal (RingOfIntegers K)) : ℕ) : ℝ)) :
    rayCellTotalMass (K := K) J ell j f unitResidueCount height ≤
      ((ell : ℝ)⁻¹) ^ j *
        (generatorCellMainConstant K J *
          Ideal.absNorm (J : Ideal (RingOfIntegers K))) * x := by
  have hfR : (0 : ℝ) < f := by
    exact_mod_cast Nat.pos_of_ne_zero hf
  have hunitR : (unitResidueCount : ℝ) ≤
      (f : ℝ) ^ Nat.card (index K) := by exact_mod_cast hunit
  have hratio : (unitResidueCount : ℝ) /
      (f : ℝ) ^ Nat.card (index K) ≤ 1 :=
    (div_le_one (pow_pos hfR _)).mpr hunitR
  have hratio0 : 0 ≤ (unitResidueCount : ℝ) /
      (f : ℝ) ^ Nat.card (index K) := by positivity
  have hgen : 0 ≤ generatorCellMainConstant K J :=
    generatorCellMainConstant_nonneg K J
  have hheight0 : 0 ≤ height ^ Nat.card (index K) := by
    rw [hheight]
    positivity
  have hellR : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell
  unfold rayCellTotalMass
  rw [zpow_neg, zpow_natCast]
  calc
    ((ell : ℝ) ^ j)⁻¹ *
        ((unitResidueCount : ℝ) / (f : ℝ) ^ Nat.card (index K)) *
        (generatorCellMainConstant K J * height ^ Nat.card (index K)) ≤
      ((ell : ℝ) ^ j)⁻¹ * 1 *
        (generatorCellMainConstant K J * height ^ Nat.card (index K)) := by
          gcongr
    _ = ((ell : ℝ)⁻¹) ^ j *
        (generatorCellMainConstant K J *
          Ideal.absNorm (J : Ideal (RingOfIntegers K))) * x := by
      rw [inv_pow, hheight]
      push_cast
      ring

/-- The natural ceiling costs at most a factor two above its underlying
positive real power. -/
theorem normSieveUpper_cast_le_two_mul_rpow
    {eta : ℝ} (heta : 0 ≤ eta) {x : ℕ} (hx : 1 ≤ x) :
    (normSieveUpper eta x : ℝ) ≤ 2 * (x : ℝ) ^ eta := by
  have hceil :
      (normSieveUpper eta x : ℝ) < (x : ℝ) ^ eta + 1 := by
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have hone : (1 : ℝ) ≤ (x : ℝ) ^ eta :=
    Real.one_le_rpow (by exact_mod_cast hx) heta
  linarith

/-- Uniform level scale for the level-restricted Rosser sieve.  It includes
both the moving ray modulus and the full fixed Rosser level `y^S`. -/
theorem eventually_uniform_auxiliary_mul_normSieveLevel_le_rpow
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 ≤ eta) (S : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ∀ f : ℕ, f ≤ (t + 1) ^ oddTensorDepth t →
        ((f * normSieveUpper eta x ^ S : ℕ) : ℝ) ≤
          (2 : ℝ) ^ S * (x : ℝ) ^ (delta + eta * S) := by
  filter_upwards
    [eventually_uniform_auxiliaryModulus_le_rpow hdelta,
      eventually_ge_atTop 1]
    with x haux hx
  intro t ht f hf
  have hfR : (f : ℝ) ≤ (x : ℝ) ^ delta := by
    have hfCast : (f : ℝ) ≤
        (((t + 1) ^ oddTensorDepth t : ℕ) : ℝ) := by
      exact_mod_cast hf
    exact hfCast.trans (haux t ht)
  have hy := normSieveUpper_cast_le_two_mul_rpow heta hx
  have hyPow :
      ((normSieveUpper eta x : ℝ) ^ S) ≤
        (2 * (x : ℝ) ^ eta) ^ S :=
    pow_le_pow_left₀ (by positivity) hy S
  have hxpos : (0 : ℝ) < x := by positivity
  have hxpow : ((x : ℝ) ^ eta) ^ S =
      (x : ℝ) ^ (eta * S) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
  calc
    ((f * normSieveUpper eta x ^ S : ℕ) : ℝ) =
        (f : ℝ) * (normSieveUpper eta x : ℝ) ^ S := by push_cast; rfl
    _ ≤ (x : ℝ) ^ delta * (2 * (x : ℝ) ^ eta) ^ S :=
      mul_le_mul hfR hyPow (by positivity) (by positivity)
    _ = (2 : ℝ) ^ S * (x : ℝ) ^ (delta + eta * S) := by
      rw [mul_pow, hxpow, Real.rpow_add hxpos]
      ring

theorem rpow_le_normSieveUpper (eta : ℝ) (x : ℕ) :
    (x : ℝ) ^ eta ≤ (normSieveUpper eta x : ℝ) := by
  exact Nat.le_ceil _

theorem normSieveUpper_le_self
    {eta : ℝ} (heta : eta ≤ 1) {x : ℕ} (hx : 1 ≤ x) :
    normSieveUpper eta x ≤ x := by
  rw [normSieveUpper, Nat.ceil_le]
  calc
    (x : ℝ) ^ eta ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) heta
    _ = (x : ℝ) := Real.rpow_one _

theorem eta_mul_log_le_log_normSieveUpper
    {eta : ℝ} (heta : 0 < eta) {x : ℕ} (hx : 1 < x) :
    eta * Real.log (x : ℝ) ≤
      Real.log (normSieveUpper eta x : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  rw [← Real.log_rpow hxR eta]
  apply Real.log_le_log (Real.rpow_pos_of_pos hxR eta)
  exact rpow_le_normSieveUpper eta x

theorem eta_mul_log_le_log_normSieveUpper_add_one
    {eta : ℝ} (heta : 0 < eta) {x : ℕ} (hx : 1 < x) :
    eta * Real.log (x : ℝ) ≤
      Real.log ((normSieveUpper eta x + 1 : ℕ) : ℝ) := by
  calc
    eta * Real.log (x : ℝ) ≤
        Real.log (normSieveUpper eta x : ℝ) :=
      eta_mul_log_le_log_normSieveUpper heta hx
    _ ≤ Real.log ((normSieveUpper eta x + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log
      · have := Real.rpow_pos_of_pos
          (show (0 : ℝ) < x by exact_mod_cast (show 0 < x by omega)) eta
        exact this.trans_le (rpow_le_normSieveUpper eta x)
      · exact_mod_cast Nat.le_add_right (normSieveUpper eta x) 1

theorem oddTensorDepth_le_sixteen_mul_log
    {t : ℕ} (ht : 1 ≤ t) :
    (oddTensorDepth t : ℝ) ≤
      16 * Real.log ((t + 1 : ℕ) : ℝ) := by
  let n := t + 1
  have hn : 2 ≤ n := by simp [n]; omega
  have hclog : Nat.clog 2 n ≤ 2 * Nat.log 2 n := by
    have h1 : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
      Nat.clog_le_of_le_pow
        (le_of_lt (Nat.lt_pow_succ_log_self (by omega) n))
    have h2 : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    have hpowNat : 2 ^ Nat.log 2 n ≤ n :=
      Nat.pow_log_le_self 2 (by omega)
    have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
      exact_mod_cast hpowNat
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hlog2]
    linarith
  have hlog2half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hdiv : Real.log (n : ℝ) / Real.log 2 ≤
      2 * Real.log (n : ℝ) := by
    have hlogn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    rw [div_le_iff₀ hlog2]
    nlinarith
  have hclogR : (Nat.clog 2 n : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    calc
      (Nat.clog 2 n : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) := by exact_mod_cast hclog
      _ ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by gcongr
      _ ≤ 2 * (2 * Real.log (n : ℝ)) := by gcongr
      _ = 4 * Real.log (n : ℝ) := by ring
  dsimp [oddTensorDepth]
  push_cast
  dsimp [n] at hclogR
  norm_num at hclogR ⊢
  nlinarith

/-- The strengthened tensor density absorbs the full moving-lower
polylogarithm produced by the rational-prime Mertens quotient. -/
theorem eventually_tensorDensity_mul_lowerLogPow_le_inverseSquare
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    {ell : ℕ} (hell : 2 ≤ ell) :
    ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
      f ≤ (t + 1) ^ oddTensorDepth t →
      ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          Real.log (normSieveLower K J f : ℝ) ^ normSieveDimension K ≤
        (4 * 16 ^ normSieveDimension K : ℝ) /
          ((t + 1 : ℕ) : ℝ) ^ 2 := by
  let k := normSieveDimension K
  let c := max (2 * k) (Ideal.absNorm (J : Ideal (RingOfIntegers K)))
  have habs :=
    eventually_oddTensorDepth_geometric_mul_log_modulus_mul_logPow_le_inverseSquare
      hell (2 * k - 1)
  filter_upwards [habs, eventually_ge_atTop (max 1 c)] with t htensor ht
  intro f hf0 hf
  let n := t + 1
  let depth := oddTensorDepth t
  let aux := n ^ depth
  let z := normSieveLower K J f
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hdepth : 1 ≤ depth := by
    dsimp [depth, oddTensorDepth]
    have hcpos : 0 < Nat.clog 2 (t + 1) :=
      Nat.clog_pos (by norm_num) (by omega)
    omega
  have haux0 : aux ≠ 0 := by
    exact pow_ne_zero _ (by dsimp [n]; omega)
  have hnaux : n ≤ aux := by
    dsimp [aux]
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by dsimp [n]; omega : 0 < n) hdepth
  have hcaux : c ≤ aux := by
    calc
      c ≤ t := (le_max_right _ _).trans ht
      _ ≤ n := by dsimp [n]; omega
      _ ≤ aux := hnaux
  have hzaux : z ≤ aux := by
    dsimp [z, normSieveLower]
    apply max_le
    · exact (le_max_left _ _).trans hcaux
    · apply max_le
      · exact hf.trans_eq (by rfl)
      · exact (le_max_right _ _).trans hcaux
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogz : 0 ≤ Real.log (z : ℝ) := by
    apply Real.log_nonneg
    have : 2 * k ≤ z := by
      dsimp [z, normSieveLower, k]
      exact le_max_left _ _
    have hk : 2 ≤ k := by exact le_max_left _ _
    exact_mod_cast (show 1 ≤ z by omega)
  have hlogza : Real.log (z : ℝ) ≤ Real.log (aux : ℝ) := by
    apply Real.log_le_log
    · have : 2 * k ≤ z := by
        dsimp [z, normSieveLower, k]
        exact le_max_left _ _
      have hk : 2 ≤ k := by exact le_max_left _ _
      exact_mod_cast (show 0 < z by omega)
    · exact_mod_cast hzaux
  have hlogaux : Real.log (aux : ℝ) =
      (depth : ℝ) * Real.log (n : ℝ) := by
    dsimp [aux]
    norm_num
  have hdepthlog : (depth : ℝ) ≤ 16 * Real.log (n : ℝ) := by
    simpa [depth, n] using oddTensorDepth_le_sixteen_mul_log ht1
  have hlogzBound : Real.log (z : ℝ) ≤
      16 * Real.log (n : ℝ) ^ 2 := by
    calc
      Real.log (z : ℝ) ≤ (depth : ℝ) * Real.log (n : ℝ) := by
        rw [← hlogaux]
        exact hlogza
      _ ≤ (16 * Real.log (n : ℝ)) * Real.log (n : ℝ) := by gcongr
      _ = 16 * Real.log (n : ℝ) ^ 2 := by ring
  have hpow : Real.log (z : ℝ) ^ k ≤
      16 ^ k * Real.log (n : ℝ) ^ (2 * k) := by
    calc
      Real.log (z : ℝ) ^ k ≤
          (16 * Real.log (n : ℝ) ^ 2) ^ k :=
        pow_le_pow_left₀ hlogz hlogzBound k
      _ = 16 ^ k * Real.log (n : ℝ) ^ (2 * k) := by
        rw [mul_pow, pow_mul]
  have htensor' := htensor aux haux0 (by rfl)
  have htensor'' : ((ell : ℝ)⁻¹) ^ depth * (depth : ℝ) *
      Real.log (n : ℝ) ^ (2 * k) ≤ 4 / (n : ℝ) ^ 2 := by
    have htwo : 1 ≤ 2 * k := by
      have hk : 2 ≤ k := by exact le_max_left _ _
      omega
    have hpowexp : Real.log (n : ℝ) ^ (2 * k) =
        Real.log (n : ℝ) * Real.log (n : ℝ) ^ (2 * k - 1) := by
      calc
        Real.log (n : ℝ) ^ (2 * k) =
            Real.log (n : ℝ) ^ ((2 * k - 1) + 1) := by
              rw [Nat.sub_add_cancel htwo]
        _ = Real.log (n : ℝ) ^ (2 * k - 1) * Real.log (n : ℝ) :=
          pow_succ _ _
        _ = Real.log (n : ℝ) * Real.log (n : ℝ) ^ (2 * k - 1) :=
          mul_comm _ _
    calc
      ((ell : ℝ)⁻¹) ^ depth * (depth : ℝ) *
          Real.log (n : ℝ) ^ (2 * k) =
        ((ell : ℝ)⁻¹) ^ depth * ((depth : ℝ) * Real.log (n : ℝ)) *
          Real.log (n : ℝ) ^ (2 * k - 1) := by rw [hpowexp]; ring
      _ = ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (aux : ℝ) *
          Real.log ((t + 1 : ℕ) : ℝ) ^ (2 * k - 1) := by
        rw [hlogaux]
      _ ≤ 4 / ((t + 1 : ℕ) : ℝ) ^ 2 := htensor'
      _ = 4 / (n : ℝ) ^ 2 := by rfl
  have hgeom : 0 ≤ ((ell : ℝ)⁻¹) ^ depth := by positivity
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          Real.log (normSieveLower K J f : ℝ) ^ normSieveDimension K =
        ((ell : ℝ)⁻¹) ^ depth * Real.log (z : ℝ) ^ k := by rfl
    _ ≤ ((ell : ℝ)⁻¹) ^ depth *
          (16 ^ k * Real.log (n : ℝ) ^ (2 * k)) := by gcongr
    _ ≤ 16 ^ k * (4 / (n : ℝ) ^ 2) := by
      calc
        ((ell : ℝ)⁻¹) ^ depth *
              (16 ^ k * Real.log (n : ℝ) ^ (2 * k)) =
            16 ^ k * (((ell : ℝ)⁻¹) ^ depth *
              Real.log (n : ℝ) ^ (2 * k)) := by ring
        _ ≤ 16 ^ k * (((ell : ℝ)⁻¹) ^ depth * (depth : ℝ) *
              Real.log (n : ℝ) ^ (2 * k)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            ((ell : ℝ)⁻¹) ^ depth * Real.log (n : ℝ) ^ (2 * k) =
                ((ell : ℝ)⁻¹) ^ depth * 1 *
                  Real.log (n : ℝ) ^ (2 * k) := by ring
            _ ≤ ((ell : ℝ)⁻¹) ^ depth * (depth : ℝ) *
                  Real.log (n : ℝ) ^ (2 * k) := by
              gcongr
              exact_mod_cast hdepth
        _ ≤ 16 ^ k * (4 / (n : ℝ) ^ 2) := by gcongr
    _ = (4 * 16 ^ normSieveDimension K : ℝ) /
        ((t + 1 : ℕ) : ℝ) ^ 2 := by
      dsimp [k, n]
      ring

private theorem list_prod_mono_of_nonneg
    {ι : Type*} (l : List ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ l, 0 ≤ a i) (hab : ∀ i ∈ l, a i ≤ b i) :
    (l.map a).prod ≤ (l.map b).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      apply mul_le_mul (hab i (by simp))
        (ih (fun q hq ↦ ha q (by simp [hq]))
          (fun q hq ↦ hab q (by simp [hq])))
        (List.prod_nonneg fun _ h ↦ by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
          exact ha q (by simp [hq]))
        ((ha i (by simp)).trans (hab i (by simp)))

theorem normSieveDegree_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < normSieveDegree K := by
  letI := Fintype.ofFinite (index K)
  rw [normSieveDegree, Nat.card_eq_fintype_card,
    ← Module.finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank]
  exact Module.finrank_pos

theorem two_le_normSieveDimension
    (K : Type*) [Field K] [NumberField K] :
    2 ≤ normSieveDimension K :=
  le_max_left _ _

theorem normSieveDegree_le_dimension
    (K : Type*) [Field K] [NumberField K] :
    normSieveDegree K ≤ normSieveDimension K :=
  le_max_right _ _

theorem two_mul_dimension_le_lower
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) :
    2 * normSieveDimension K ≤ normSieveLower K J f :=
  le_max_left _ _

theorem rayModulus_le_lower
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) :
    f ≤ normSieveLower K J f :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem correctionNorm_le_lower
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ) :
    Ideal.absNorm (J : Ideal (RingOfIntegers K)) ≤
      normSieveLower K J f :=
  (le_max_right _ _).trans (le_max_right _ _)

@[simp] theorem mem_normSievePrimes
    {K : Type*} [Field K] [NumberField K]
    {J : (Ideal (RingOfIntegers K))⁰} {f y p : ℕ} :
    p ∈ normSievePrimes K J f y ↔
      normSieveLower K J f < p ∧ p ≤ y ∧ p.Prime := by
  exact Erdos851.mem_sievePrimes

theorem normSievePrimes_prime
    {K : Type*} [Field K] [NumberField K]
    {J : (Ideal (RingOfIntegers K))⁰} {f y : ℕ} :
    ∀ p ∈ normSievePrimes K J f y, p.Prime := by
  intro p hp
  exact (mem_normSievePrimes.mp hp).2.2

theorem normSievePrime_gt_twice_dimension
    {K : Type*} [Field K] [NumberField K]
    {J : (Ideal (RingOfIntegers K))⁰} {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    2 * normSieveDimension K < p :=
  (two_mul_dimension_le_lower K J f).trans_lt
    (mem_normSievePrimes.mp hp).1

theorem normSievePrime_coprime_rayModulus
    {K : Type*} [Field K] [NumberField K]
    {J : (Ideal (RingOfIntegers K))⁰} {f y p : ℕ}
    (hf : f ≠ 0) (hp : p ∈ normSievePrimes K J f y) :
    f.Coprime p := by
  have hpPrime := (mem_normSievePrimes.mp hp).2.2
  apply Nat.Coprime.symm
  apply hpPrime.coprime_iff_not_dvd.mpr
  intro hpf
  have hple : p ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf) hpf
  exact (Nat.not_lt_of_ge hple)
    ((rayModulus_le_lower K J f).trans_lt
      (mem_normSievePrimes.mp hp).1)

theorem normSievePrime_coprime_correctionNorm
    {K : Type*} [Field K] [NumberField K]
    {J : (Ideal (RingOfIntegers K))⁰} {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))) := by
  have hpPrime := (mem_normSievePrimes.mp hp).2.2
  rw [hpPrime.coprime_iff_not_dvd]
  intro hpJ
  have hJpos : 0 < Ideal.absNorm (J : Ideal (RingOfIntegers K)) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (nonZeroDivisors.coe_ne_zero J))
  have hple : p ≤ Ideal.absNorm (J : Ideal (RingOfIntegers K)) :=
    Nat.le_of_dvd hJpos hpJ
  exact (Nat.not_lt_of_ge hple)
    ((correctionNorm_le_lower K J f).trans_lt
      (mem_normSievePrimes.mp hp).1)

theorem rayModulus_coprime_normSieveProduct
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y : ℕ} (hf : f ≠ 0) :
    f.Coprime ((normSievePrimes K J f y).prod id) := by
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  exact normSievePrime_coprime_rayModulus hf hp

theorem normSievePrimes_good_for_correction
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ) :
    ∀ p ∈ normSievePrimes K J f y,
      p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))) := by
  intro p hp
  exact normSievePrime_coprime_correctionNorm hp

private theorem degree_mul_pow_lt_pow
    {D p : ℕ} (hD : 0 < D) (hDp : D < p) :
    D * p ^ (D - 1) < p ^ D := by
  have hpowpos : 0 < p ^ (D - 1) := pow_pos (hD.trans hDp) _
  have hmul := Nat.mul_lt_mul_of_pos_right hDp hpowpos
  calc
    D * p ^ (D - 1) < p * p ^ (D - 1) := hmul
    _ = p ^ D := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hD]

theorem coordinateRootCount_lt_full
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    (coordinateAlgebraNormResidueSystem K J).rootCount K p <
      p ^ normSieveDegree K := by
  have hpPrime := (mem_normSievePrimes.mp hp).2.2
  have hcop := normSievePrime_coprime_correctionNorm hp
  have hroot := coordinateAlgebraNormResidueSystem_rootCount_le
    K J p hpPrime hcop
  apply hroot.trans_lt
  apply degree_mul_pow_lt_pow (normSieveDegree_pos K)
  have hdimlt : normSieveDimension K < p := by
    have := normSievePrime_gt_twice_dimension hp
    omega
  exact (normSieveDegree_le_dimension K).trans_lt hdimlt

theorem coordinateRootCount_pos
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {p : ℕ} (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype (index K) := Fintype.ofFinite _
  have hindex : Nonempty (index K) := by
    rw [← Fintype.card_pos_iff]
    simpa [normSieveDegree, Nat.card_eq_fintype_card] using
      normSieveDegree_pos K
  letI : Nonempty (index K) := hindex
  letI : Fact p.Prime := ⟨hp⟩
  let e := fixedIdealCoordinateQuotientEquiv K J p hp hcop
  letI : Nontrivial (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
    e.symm.nontrivial
  let k : index K → ZMod p := e.symm 0
  rw [(coordinateAlgebraNormResidueSystem K J).rootCount_eq K p]
  apply Finset.card_pos.mpr
  refine ⟨k, ?_⟩
  rw [mem_normDivisibleResidues]
  exact (fixedIdeal_coordinateAlgebraNormMod_eq_zero_iff_nonunit
    K J p hp hcop k).mpr (by simp [e, k])

theorem coordinateNormDensity_nonneg
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) :
    0 ≤ coordinateNormDensity K J p := by
  unfold coordinateNormDensity
  positivity

theorem coordinateNormDensity_lt_one
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    coordinateNormDensity K J p < 1 := by
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast (mem_normSievePrimes.mp hp).2.2.pos
  rw [coordinateNormDensity, div_lt_one (pow_pos hpPos _)]
  exact_mod_cast coordinateRootCount_lt_full J hp

/-- The fixed-ideal norm-zero density is pointwise dominated on the sieve
interval by the dimension majorant `k/p`. -/
theorem coordinateNormDensity_le_dimension_div
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    coordinateNormDensity K J p ≤ (normSieveDimension K : ℝ) / p := by
  let D := normSieveDegree K
  have hpPrime := (mem_normSievePrimes.mp hp).2.2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hroot := coordinateAlgebraNormResidueSystem_rootCount_le K J p hpPrime
    (normSievePrime_coprime_correctionNorm hp)
  have hrootR :
      ((coordinateAlgebraNormResidueSystem K J).rootCount K p : ℝ) ≤
        (D : ℝ) * (p : ℝ) ^ (D - 1) := by
    exact_mod_cast hroot
  have hpow : (p : ℝ) ^ D = (p : ℝ) ^ (D - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (normSieveDegree_pos K)]
  have hfirst : coordinateNormDensity K J p ≤ (D : ℝ) / p := by
    rw [coordinateNormDensity, div_le_iff₀ (pow_pos hpR D)]
    calc
      ((coordinateAlgebraNormResidueSystem K J).rootCount K p : ℝ) ≤
          (D : ℝ) * (p : ℝ) ^ (D - 1) := hrootR
      _ = (D : ℝ) / p * (p : ℝ) ^ D := by
        rw [hpow]
        field_simp
  exact hfirst.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast normSieveDegree_le_dimension K) hpR.le)

theorem coordinateNormDensity_le_binomial
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    coordinateNormDensity K J p ≤
      Erdos387.binomialSieveNu (normSieveDimension K) p := by
  rw [Erdos387.binomialSieveNu_prime
    (mem_normSievePrimes.mp hp).2.2]
  exact coordinateNormDensity_le_dimension_div J hp

private theorem inverse_buchstab_coordinateNormDensity_le_binomial
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y : ℕ} {Q : List ℕ}
    (hQ : ∀ p ∈ Q, p ∈ normSievePrimes K J f y) :
    (buchstabProduct (coordinateNormDensity K J) Q)⁻¹ ≤
      (buchstabProduct
        (fun p ↦ Erdos387.binomialSieveNu (normSieveDimension K) p) Q)⁻¹ := by
  let b : ℕ → ℝ := fun p ↦
    Erdos387.binomialSieveNu (normSieveDimension K) p
  have hb_lt (p : ℕ) (hp : p ∈ Q) : b p < 1 := by
    have hpS := hQ p hp
    have hpPrime := (mem_normSievePrimes.mp hpS).2.2
    change Erdos387.binomialSieveNu (normSieveDimension K) p < 1
    rw [Erdos387.binomialSieveNu_prime hpPrime]
    rw [div_lt_one (by exact_mod_cast hpPrime.pos)]
    have htwice := normSievePrime_gt_twice_dimension hpS
    exact_mod_cast (show normSieveDimension K < p by omega)
  have hcoordPos : 0 < buchstabProduct (coordinateNormDensity K J) Q := by
    unfold buchstabProduct
    apply List.prod_pos
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact sub_pos.mpr (coordinateNormDensity_lt_one J (hQ p hp))
  have hbinPos : 0 < buchstabProduct b Q := by
    unfold buchstabProduct
    apply List.prod_pos
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact sub_pos.mpr (hb_lt p hp)
  apply (inv_le_inv₀ hcoordPos hbinPos).mpr
  unfold buchstabProduct
  apply list_prod_mono_of_nonneg
  · intro p hp
    exact sub_nonneg.mpr (hb_lt p hp).le
  · intro p hp
    linarith [coordinateNormDensity_le_binomial J (hQ p hp)]

private theorem coordinateRootCount_eq_natCard
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime) :
    (coordinateAlgebraNormResidueSystem K J).rootCount K p =
      Nat.card {k : index K → ZMod p //
        coordinateAlgebraNormMod K J p k = 0} := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [(coordinateAlgebraNormResidueSystem K J).rootCount_eq K p]
  exact (Nat.subtype_card _ (by
    intro x
    simp only [mem_normDivisibleResidues]
    rfl)).symm

/-- Exact complementary local density on every selected prime. -/
theorem one_sub_coordinateNormDensity_eq_unitRatio
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hp : p ∈ normSievePrimes K J f y) :
    1 - coordinateNormDensity K J p =
      (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  have hpPrime := (mem_normSievePrimes.mp hp).2.2
  rw [coordinateNormDensity, coordinateRootCount_eq_natCard K J p hpPrime]
  exact LocalNormEuler.one_sub_fixedIdeal_coordinateNormResidueDensity_eq_unitRatio
    K J p hpPrime (normSievePrime_coprime_correctionNorm hp)

/-- The exact finite Euler product on the concrete interval is the product
of the local unit proportions of the fixed number field. -/
theorem finiteEulerProduct_coordinateNormDensity_eq
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ) :
    finiteEulerProduct (coordinateNormDensity K J)
        (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) =
      ∏ p ∈ normSievePrimes K J f y,
        (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
          Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  classical
  rw [finiteEulerProduct]
  rw [← List.prod_toFinset
    (fun p ↦ 1 - coordinateNormDensity K J p)
    (Erdos851.ascendingSievePrimes_nodup _ _)]
  apply Finset.prod_congr
  · ext p
    simp [normSievePrimes]
  · intro p hp
    exact one_sub_coordinateNormDensity_eq_unitRatio J hp

theorem rationalPrime_unitRatio_pos
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    0 < (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  letI : Finite (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
    (Ideal.absNorm_ne_zero_iff (rationalModulusIdeal K p)).mp (by
      rw [rationalModulusIdeal, Ideal.absNorm_span_natCast]
      exact pow_ne_zero _ hp.ne_zero)
  exact div_pos (by exact_mod_cast
      (Nat.card_pos (α := (RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ)))
    (by exact_mod_cast
      (Nat.card_pos (α := RingOfIntegers K ⧸ rationalModulusIdeal K p)))

theorem rationalPrimeNormSieveProduct_pos
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    0 < rationalPrimeNormSieveProduct K w := by
  classical
  unfold rationalPrimeNormSieveProduct
  apply Finset.prod_pos
  intro p hp
  exact rationalPrime_unitRatio_pos K p (Nat.prime_of_mem_primesBelow hp)

/-- Exact removal of the finitely many rational primes at or below the
lower endpoint.  This identity makes the dependence on the moving ray
modulus completely visible. -/
theorem finiteEuler_mul_initialProduct_eq_fullProduct
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ)
    (hy : normSieveLower K J f ≤ y) :
    finiteEulerProduct (coordinateNormDensity K J)
        (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) *
      rationalPrimeNormSieveProduct K (normSieveLower K J f + 1) =
        rationalPrimeNormSieveProduct K (y + 1) := by
  classical
  rw [finiteEulerProduct_coordinateNormDensity_eq]
  unfold rationalPrimeNormSieveProduct
  let z := normSieveLower K J f
  let F : ℕ → ℝ := fun p ↦
    (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p)
  have hsub : Nat.primesBelow (z + 1) ⊆ Nat.primesBelow (y + 1) := by
    exact Nat.primesBelow_mono (Nat.add_le_add_right hy 1)
  have hdiff : Nat.primesBelow (y + 1) \ Nat.primesBelow (z + 1) =
      normSievePrimes K J f y := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_sdiff, Nat.mem_primesBelow,
        mem_normSievePrimes, hp, and_true]
      omega
    · simp [Nat.mem_primesBelow, mem_normSievePrimes, hp]
  simpa only [z, F, hdiff] using (Finset.prod_sdiff (f := F) hsub)

private def rationalPrimeUnitIntervalProduct
    (K : Type*) [Field K] [NumberField K] (z y : ℕ) : ℝ :=
  ∏ p ∈ Erdos851.sievePrimes z y,
    (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p)

private theorem rationalPrimeUnitIntervalProduct_mul_initial
    (K : Type*) [Field K] [NumberField K] {z y : ℕ} (hzy : z ≤ y) :
    rationalPrimeUnitIntervalProduct K z y *
      rationalPrimeNormSieveProduct K (z + 1) =
        rationalPrimeNormSieveProduct K (y + 1) := by
  classical
  unfold rationalPrimeUnitIntervalProduct rationalPrimeNormSieveProduct
  let F : ℕ → ℝ := fun p ↦
    (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p)
  have hsub : Nat.primesBelow (z + 1) ⊆ Nat.primesBelow (y + 1) :=
    Nat.primesBelow_mono (Nat.add_le_add_right hzy 1)
  have hdiff : Nat.primesBelow (y + 1) \ Nat.primesBelow (z + 1) =
      Erdos851.sievePrimes z y := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_sdiff, Nat.mem_primesBelow,
        Erdos851.mem_sievePrimes, hp, and_true]
      omega
    · simp [Nat.mem_primesBelow, Erdos851.mem_sievePrimes, hp]
  simpa only [F, hdiff] using (Finset.prod_sdiff (f := F) hsub)

private theorem rationalPrimeUnitIntervalProduct_inv_le_binomial
    (K : Type*) [Field K] [NumberField K] {z y : ℕ}
    (hz : 2 * normSieveDimension K ≤ z) :
    (rationalPrimeUnitIntervalProduct K z y)⁻¹ ≤
      inverseLocalEulerProduct
        (fun p ↦ Erdos387.binomialSieveNu (normSieveDimension K) p) z y := by
  classical
  unfold rationalPrimeUnitIntervalProduct inverseLocalEulerProduct
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact inv_nonneg.mpr (rationalPrime_unitRatio_pos K p
      (Erdos851.mem_sievePrimes.mp hp).2.2).le
  · intro p hp
    have hpData := Erdos851.mem_sievePrimes.mp hp
    have hpPrime := hpData.2.2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hklt : normSieveDimension K < p := by omega
    have hbinPos : 0 < 1 - (normSieveDimension K : ℝ) / p := by
      rw [sub_pos, div_lt_one hpR]
      exact_mod_cast hklt
    have hunitPos := rationalPrime_unitRatio_pos K p hpPrime
    change ((Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p))⁻¹ ≤
      (1 - Erdos387.binomialSieveNu (normSieveDimension K) p)⁻¹
    rw [Erdos387.binomialSieveNu_prime hpPrime]
    apply (inv_le_inv₀ hunitPos hbinPos).mpr
    calc
      1 - (normSieveDimension K : ℝ) / p ≤
          1 - (normSieveDegree K : ℝ) / p := by
        have hfrac : (normSieveDegree K : ℝ) / (p : ℝ) ≤
            (normSieveDimension K : ℝ) / p :=
          div_le_div_of_nonneg_right
            (by exact_mod_cast normSieveDegree_le_dimension K) hpR.le
        linarith
      _ ≤ (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
          Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
        rationalPrime_unitRatio_ge_one_sub_degree_div K p hpPrime

/-- The reciprocal finite loss below a moving lower endpoint is at most a
fixed degree-`k` power of its logarithm. -/
theorem exists_initialProduct_inverse_polylog_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 2 * normSieveDimension K ≤ w →
      (rationalPrimeNormSieveProduct K (w + 1))⁻¹ ≤
        C * Real.log (w : ℝ) ^ normSieveDimension K := by
  let k := normSieveDimension K
  let z := 2 * k
  obtain ⟨A, hA, hdim⟩ :=
    Erdos387.BinomialEulerProduct.exists_binomial_dimension_bound k
      ((show 1 ≤ 2 by omega).trans (two_le_normSieveDimension K))
  let B := (rationalPrimeNormSieveProduct K (z + 1))⁻¹
  let C := B * A / Real.log (z : ℝ) ^ k
  have hzgt : 1 < z := by
    dsimp [z, k]
    have := two_le_normSieveDimension K
    omega
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast hzgt)
  have hB : 0 ≤ B := inv_nonneg.mpr
    (rationalPrimeNormSieveProduct_pos K (z + 1)).le
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hB (by linarith))
    (pow_nonneg hlogz.le _)
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hfactor := rationalPrimeUnitIntervalProduct_mul_initial K
    (show z ≤ w by simpa [z, k] using hw)
  have hinvEq : (rationalPrimeNormSieveProduct K (w + 1))⁻¹ =
      B * (rationalPrimeUnitIntervalProduct K z w)⁻¹ := by
    rw [← hfactor, mul_inv_rev]
  rw [hinvEq]
  calc
    B * (rationalPrimeUnitIntervalProduct K z w)⁻¹ ≤
        B * inverseLocalEulerProduct
          (fun p ↦ Erdos387.binomialSieveNu k p) z w := by
      apply mul_le_mul_of_nonneg_left
        (rationalPrimeUnitIntervalProduct_inv_le_binomial K
          (by simp [z, k])) hB
    _ ≤ B * (A * (Real.log (w : ℝ) / Real.log (z : ℝ)) ^ k) := by
      gcongr
      exact hdim z w (by simp [z]) (by simpa [z, k] using hw)
    _ = C * Real.log (w : ℝ) ^ k := by
      dsimp [C]
      rw [div_pow]
      field_simp

/-- Fully explicit small-power endpoint Mertens bound.  The only loss from
the moving lower endpoint is the displayed fixed-degree polylogarithm. -/
theorem exists_normSieveUpper_finiteEuler_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∃ W : ℕ, 0 ≤ C ∧
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (f x : ℕ) (eta : ℝ),
        0 < eta → 1 < x →
        W ≤ normSieveUpper eta x + 1 →
        normSieveLower K J f ≤ normSieveUpper eta x →
        finiteEulerProduct (coordinateNormDensity K J)
            (Erdos851.ascendingSievePrimes (normSieveLower K J f)
              (normSieveUpper eta x)) ≤
          C * Real.log (normSieveLower K J f : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ)) := by
  obtain ⟨Cinit, hCinit, hinit⟩ :=
    exists_initialProduct_inverse_polylog_bound K
  have hEv := LocalNormEuler.eventually_rationalPrimeNormSieveProduct_le K
  rw [eventually_atTop] at hEv
  obtain ⟨W, hW⟩ := hEv
  let a : ℝ := 8 / NumberField.dedekindZeta_residue K
  let C := a * Cinit
  have ha : 0 ≤ a := (div_pos (by norm_num)
    (NumberField.dedekindZeta_residue_pos K)).le
  have hC : 0 ≤ C := mul_nonneg ha hCinit
  refine ⟨C, W, hC, ?_⟩
  intro J f x eta heta hx hWy hlow
  let y := normSieveUpper eta x
  let z := normSieveLower K J f
  have hM := hW (y + 1) (by simpa [y] using hWy)
  have hinitPos := rationalPrimeNormSieveProduct_pos K (z + 1)
  have hfinite : finiteEulerProduct (coordinateNormDensity K J)
      (Erdos851.ascendingSievePrimes z y) ≤
        (a / Real.log ((y + 1 : ℕ) : ℝ)) /
          rationalPrimeNormSieveProduct K (z + 1) := by
    calc
      finiteEulerProduct (coordinateNormDensity K J)
          (Erdos851.ascendingSievePrimes z y) =
        rationalPrimeNormSieveProduct K (y + 1) /
          rationalPrimeNormSieveProduct K (z + 1) := by
            apply (eq_div_iff hinitPos.ne').mpr
            simpa [y, z] using
              finiteEuler_mul_initialProduct_eq_fullProduct K J f y hlow
      _ ≤ (a / Real.log ((y + 1 : ℕ) : ℝ)) /
          rationalPrimeNormSieveProduct K (z + 1) := by
        apply div_le_div_of_nonneg_right _ hinitPos.le
        simpa [a] using hM
  have hinitial : (rationalPrimeNormSieveProduct K (z + 1))⁻¹ ≤
      Cinit * Real.log (z : ℝ) ^ normSieveDimension K :=
    hinit z (by simpa [z] using two_mul_dimension_le_lower K J f)
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hden : 0 < eta * Real.log (x : ℝ) := mul_pos heta hxlog
  have hlogy : eta * Real.log (x : ℝ) ≤ Real.log ((y + 1 : ℕ) : ℝ) := by
    simpa [y] using eta_mul_log_le_log_normSieveUpper_add_one heta hx
  have hlogypos : 0 < Real.log ((y + 1 : ℕ) : ℝ) := hden.trans_le hlogy
  have hcost : 0 ≤ Cinit * Real.log (z : ℝ) ^ normSieveDimension K := by
    have hzfour : 4 ≤ z := by
      dsimp [z]
      have hk := two_le_normSieveDimension K
      exact (show 4 ≤ 2 * normSieveDimension K by omega).trans
        (two_mul_dimension_le_lower K J f)
    exact mul_nonneg hCinit (pow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))) _)
  calc
    finiteEulerProduct (coordinateNormDensity K J)
        (Erdos851.ascendingSievePrimes z y) ≤
      (a / Real.log ((y + 1 : ℕ) : ℝ)) /
        rationalPrimeNormSieveProduct K (z + 1) := by
          simpa [a, y, z] using hfinite
    _ = (a / Real.log ((y + 1 : ℕ) : ℝ)) *
        (rationalPrimeNormSieveProduct K (z + 1))⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ (a / Real.log ((y + 1 : ℕ) : ℝ)) *
        (Cinit * Real.log (z : ℝ) ^ normSieveDimension K) := by
          exact mul_le_mul_of_nonneg_left hinitial
            (div_nonneg ha hlogypos.le)
    _ ≤ (a / (eta * Real.log (x : ℝ))) *
        (Cinit * Real.log (z : ℝ) ^ normSieveDimension K) := by
          apply mul_le_mul_of_nonneg_right _ hcost
          exact div_le_div_of_nonneg_left ha hden hlogy
    _ = C * Real.log (z : ℝ) ^ normSieveDimension K /
        (eta * Real.log (x : ℝ)) := by
          dsimp [C]
          field_simp

/-- Mertens with the finite low-prime loss isolated as an explicit positive
denominator.  In particular no dependence on the moving ray modulus is
silently absorbed into a constant. -/
theorem finiteEuler_le_of_rationalPrimeMertens
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ)
    (hy : normSieveLower K J f ≤ y)
    (hM : rationalPrimeNormSieveProduct K (y + 1) ≤
      (8 / NumberField.dedekindZeta_residue K) /
        Real.log ((y + 1 : ℕ) : ℝ)) :
    finiteEulerProduct (coordinateNormDensity K J)
        (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) ≤
      ((8 / NumberField.dedekindZeta_residue K) /
          Real.log ((y + 1 : ℕ) : ℝ)) /
        rationalPrimeNormSieveProduct K (normSieveLower K J f + 1) := by
  have hinit := rationalPrimeNormSieveProduct_pos K
    (normSieveLower K J f + 1)
  calc
    finiteEulerProduct (coordinateNormDensity K J)
        (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) =
      rationalPrimeNormSieveProduct K (y + 1) /
        rationalPrimeNormSieveProduct K (normSieveLower K J f + 1) := by
          apply (eq_div_iff hinit.ne').mpr
          exact finiteEuler_mul_initialProduct_eq_fullProduct K J f y hy
    _ ≤ ((8 / NumberField.dedekindZeta_residue K) /
          Real.log ((y + 1 : ℕ) : ℝ)) /
        rationalPrimeNormSieveProduct K (normSieveLower K J f + 1) :=
      div_le_div_of_nonneg_right hM hinit.le

theorem eventually_finiteEuler_coordinateNormDensity_le
    (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ y : ℕ in atTop,
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (f : ℕ),
        normSieveLower K J f ≤ y →
        finiteEulerProduct (coordinateNormDensity K J)
            (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) ≤
          ((8 / NumberField.dedekindZeta_residue K) /
              Real.log ((y + 1 : ℕ) : ℝ)) /
            rationalPrimeNormSieveProduct K
              (normSieveLower K J f + 1) := by
  have hEv := LocalNormEuler.eventually_rationalPrimeNormSieveProduct_le K
  rw [eventually_atTop] at hEv
  obtain ⟨w, hw⟩ := hEv
  rw [eventually_atTop]
  refine ⟨w, ?_⟩
  intro y hy J f hlow
  exact finiteEuler_le_of_rationalPrimeMertens K J f y hlow
    (hw (y + 1) (by omega))

/-- A fixed Rosser depth, depending only on the number-field degree,
controls the genuine norm density.  The cutoff estimate is inherited from
the binomial majorant through the pointwise local-root bound; no desired
prime-scale estimate appears among the hypotheses. -/
theorem exists_coordinateNorm_mainTerm_bounds
    (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, ∃ S₀ : ℕ,
      1 ≤ A ∧ normRosserBeta K + 1 ≤ S₀ ∧
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (f y S : ℕ),
        normSieveLower K J f ≤ y → S₀ ≤ S →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - normRosserBeta K)
        upperMainTerm (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
            (coordinateNormDensity K J)
            (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) ≤
          (1 + eta) * finiteEulerProduct (coordinateNormDensity K J)
            (Erdos851.ascendingSievePrimes (normSieveLower K J f) y) := by
  let k := normSieveDimension K
  obtain ⟨A, hA, hcutoff⟩ :=
    Erdos387.BinomialBetaCutoff.exists_binomial_hundred_mul_cutoff_bound
      k (two_le_normSieveDimension K)
  obtain ⟨n, hn⟩ := exists_nat_ge ((99 / 4 : ℝ) * Real.log A + 1)
  refine ⟨A, normRosserBeta K + n, hA, ?_, ?_⟩
  · have hlog0 : 0 ≤ Real.log A := Real.log_nonneg hA
    have hn1R : (1 : ℝ) ≤ n := by nlinarith
    have hn1 : 1 ≤ n := by exact_mod_cast hn1R
    omega
  · intro J f y S hzy hS
    have hbeta : 2 ≤ normRosserBeta K := by
      unfold normRosserBeta
      have hk := two_le_normSieveDimension K
      omega
    have hSbeta : normRosserBeta K + 1 ≤ S := by
      have hlog0 : 0 ≤ Real.log A := Real.log_nonneg hA
      have hn1R : (1 : ℝ) ≤ n := by nlinarith
      have hn1 : 1 ≤ n := by exact_mod_cast hn1R
      omega
    have hy : 1 < y := by
      have hfour : 4 ≤ normSieveLower K J f := by
        have hk := two_le_normSieveDimension K
        exact (show 4 ≤ 2 * normSieveDimension K by omega).trans
          (two_mul_dimension_le_lower K J f)
      omega
    have hdiff : n ≤ S - normRosserBeta K := by omega
    have hlog : Real.log A ≤ 4 * (S - normRosserBeta K : ℕ) / 99 := by
      have hnR : (n : ℝ) ≤ ((S - normRosserBeta K : ℕ) : ℝ) := by
        exact_mod_cast hdiff
      calc
        Real.log A ≤ 4 * (n : ℝ) / 99 := by nlinarith
        _ ≤ 4 * (S - normRosserBeta K : ℕ) / 99 := by gcongr
    have hmain :=
      Erdos387.GeneralBetaMainTerm.finiteMainTerms_bounds_of_generalBetaCutoffs
        (g := coordinateNormDensity K J) (beta := normRosserBeta K)
        (z := normSieveLower K J f) (y := y) (S := S) (A := A)
        hbeta hSbeta hy (coordinateNormDensity_nonneg K J)
        (by
          intro p hp
          apply coordinateNormDensity_lt_one (f := f) (y := y) J
          exact mem_descendingSievePrimes.mp hp)
        hA
        (by
          intro r _hr _hstart
          let Q := betaCutoffPrefix (normRosserBeta K)
            (normSieveLower K J f) y r
          have hprefix : Q <+:
              descendingSievePrimes (normSieveLower K J f) y :=
            betaCutoffPrefix_isPrefix _ _ _ _ (by omega)
          have hQ : ∀ p ∈ Q, p ∈ normSievePrimes K J f y := by
            intro p hp
            exact mem_descendingSievePrimes.mp (hprefix.subset hp)
          calc
            (buchstabProduct (coordinateNormDensity K J) Q)⁻¹ ≤
                (buchstabProduct
                  (fun p ↦ Erdos387.binomialSieveNu k p) Q)⁻¹ :=
              inverse_buchstab_coordinateNormDensity_le_binomial J hQ
            _ ≤ A * Real.rpow betaRatio (2 * r) := by
              apply hcutoff (normSieveLower K J f) y r
              · have := two_mul_dimension_le_lower K J f
                dsimp [k]
                omega
              · exact hzy)
        (by
          intro r hstart _hr
          have hcast : ((S - normRosserBeta K : ℕ) : ℝ) ≤ r := by
            exact_mod_cast hstart
          exact hlog.trans (by gcongr))
    simpa only [Erdos851.BetaSieveFundamental.descendingSievePrimes,
      Erdos851.ascendingSievePrimes, List.reverse_reverse] using hmain.2

/-- The endpoint Euler error used by the lattice remainder is bounded by
the standard dimension-`k` logarithmic factor. -/
theorem exists_normSieve_endpointEuler_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ),
        normSieveLower K J f ≤ y →
        ((Erdos851.ascendingSievePrimes (normSieveLower K J f) y).map
          (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod ≤
          A * (Real.log (y : ℝ) /
            Real.log (normSieveLower K J f : ℝ)) ^ normSieveDimension K := by
  obtain ⟨A, hA, hbound⟩ := exists_endpointEuler_dimension_bound
    (normSieveDimension K)
      ((show 1 ≤ 2 by omega).trans (two_le_normSieveDimension K))
  refine ⟨A, hA, ?_⟩
  intro J f y hy
  calc
    ((Erdos851.ascendingSievePrimes (normSieveLower K J f) y).map
        (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod ≤
      ((Erdos851.ascendingSievePrimes (normSieveLower K J f) y).map
        (fun p : ℕ ↦ 1 + (normSieveDimension K : ℝ) / p)).prod := by
        apply list_prod_mono_of_nonneg
        · intro p hp
          have hpPrime := Erdos851.ascendingSievePrimes_prime p hp
          exact add_nonneg zero_le_one (div_nonneg (by positivity)
            (by exact_mod_cast hpPrime.pos.le))
        · intro p hp
          have hpPrime := Erdos851.ascendingSievePrimes_prime p hp
          have hfrac : (normSieveDegree K : ℝ) / (p : ℝ) ≤
              (normSieveDimension K : ℝ) / (p : ℝ) :=
            div_le_div_of_nonneg_right
              (by exact_mod_cast normSieveDegree_le_dimension K)
              (by exact_mod_cast hpPrime.pos.le)
          linarith
    _ ≤ A * (Real.log (y : ℝ) /
        Real.log (normSieveLower K J f : ℝ)) ^ normSieveDimension K :=
      hbound _ _ (two_mul_dimension_le_lower K J f) hy

/-- Positivity of the concrete endpoint Euler factor. -/
theorem normSieve_endpointEuler_nonneg
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ) :
    0 ≤ ((ascendingSievePrimes (normSieveLower K J f) y).map
      (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have hpPrime := ascendingSievePrimes_prime p hp
  exact add_nonneg zero_le_one
    (div_nonneg (by positivity) (by exact_mod_cast hpPrime.pos.le))

/-- At the small-power endpoint the lattice remainder's Euler factor is at
most a fixed multiple of the required power of `log x`. -/
theorem exists_normSieve_endpointEuler_log_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (f x : ℕ) (eta : ℝ),
        0 < eta → eta ≤ 1 → 1 < x →
        normSieveLower K J f ≤ normSieveUpper eta x →
        ((ascendingSievePrimes (normSieveLower K J f)
          (normSieveUpper eta x)).map
          (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod ≤
            A * Real.log (x : ℝ) ^ normSieveDimension K := by
  obtain ⟨A, hA, hbound⟩ := exists_normSieve_endpointEuler_bound K
  refine ⟨A, hA, ?_⟩
  intro J f x eta heta heta1 hx hlow
  let y := normSieveUpper eta x
  let z := normSieveLower K J f
  have hz4 : 4 ≤ z := by
    have hk := two_le_normSieveDimension K
    exact (show 4 ≤ 2 * normSieveDimension K by omega).trans
      (two_mul_dimension_le_lower K J f)
  have hy4 : 4 ≤ y := hz4.trans hlow
  have hyx : y ≤ x := by
    dsimp [y]
    exact normSieveUpper_le_self heta1 (by omega)
  have hlogz1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hz4))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hratioNonneg : 0 ≤
      Real.log (y : ℝ) / Real.log (z : ℝ) :=
    div_nonneg hlogy (zero_le_one.trans hlogz1)
  have hratio :
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ Real.log (x : ℝ) := by
    calc
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ Real.log (y : ℝ) :=
        div_le_self hlogy hlogz1
      _ ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < y by omega))
          (by exact_mod_cast hyx)
  calc
    ((ascendingSievePrimes z y).map
        (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^
        normSieveDimension K := by
          simpa only [z, y] using hbound J f y hlow
    _ ≤ A * Real.log (x : ℝ) ^ normSieveDimension K := by
      gcongr

theorem normSievePrimes_rootCount_pos
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hpPrime : p.Prime) (hp : p ∣ (normSievePrimes K J f y).prod id) :
    0 < (coordinateAlgebraNormResidueSystem K J).rootCount K p := by
  have hpMem : p ∈ normSievePrimes K J f y := by
    have hp' : p ∣ Erdos387.sievePrimeProduct
        (normSieveLower K J f) (y + 1) := by
      rwa [Erdos851.erdos387_sievePrimeProduct_succ]
    have hm := Erdos387.prime_mem_sievePrimes_of_dvd_product hpPrime hp'
    rw [Erdos851.erdos387_sievePrimes_succ] at hm
    exact hm
  exact coordinateRootCount_pos J hpPrime
    (normSievePrime_coprime_correctionNorm hpMem)

theorem normSievePrimes_rootCount_lt
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y p : ℕ}
    (hpPrime : p.Prime) (hp : p ∣ (normSievePrimes K J f y).prod id) :
    (coordinateAlgebraNormResidueSystem K J).rootCount K p <
      p ^ normSieveDegree K := by
  have hpMem : p ∈ normSievePrimes K J f y := by
    have hp' : p ∣ Erdos387.sievePrimeProduct
        (normSieveLower K J f) (y + 1) := by
      rwa [Erdos851.erdos387_sievePrimeProduct_succ]
    have hm := Erdos387.prime_mem_sievePrimes_of_dvd_product hpPrime hp'
    rw [Erdos851.erdos387_sievePrimes_succ] at hm
    exact hm
  exact coordinateRootCount_lt_full J hpMem

/-- A single product bound supplies the moving-modulus height hypothesis of
`OddRayNormRosser`.  This is a transparent geometric constraint and contains
no prime-counting estimate. -/
theorem height_condition_of_product_le
    {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) {f y : ℕ} {height : ℝ}
    (hheight : (((f * (normSievePrimes K J f y).prod id : ℕ) : ℕ) : ℝ) ≤
      height) :
    ∀ (d : ℕ) [NeZero d], d ∣ (normSievePrimes K J f y).prod id →
      ((f * d : ℕ) : ℝ) ≤ height := by
  intro d _ hd
  have hprodPos : 0 < (normSievePrimes K J f y).prod id := by
    apply Finset.prod_pos
    intro p hp
    exact (normSievePrimes_prime p hp).pos
  have hdle : d ≤ (normSievePrimes K J f y).prod id :=
    Nat.le_of_dvd hprodPos hd
  exact (by exact_mod_cast Nat.mul_le_mul_left f hdle :
      ((f * d : ℕ) : ℝ) ≤
        ((f * (normSievePrimes K J f y).prod id : ℕ) : ℝ)).trans hheight

/-- The level-restricted Rosser bridge only requests geometric remainders
for `d ≤ level`; hence the correct height condition is `f * level ≤ height`,
not a bound involving the full primorial. -/
theorem height_condition_of_level_le
    {f level : ℕ} {height : ℝ}
    (hheight : ((f * level : ℕ) : ℝ) ≤ height) :
    ∀ (d : ℕ) [NeZero d], d ≤ level →
      ((f * d : ℕ) : ℝ) ≤ height := by
  intro d _ hd
  exact (by exact_mod_cast Nat.mul_le_mul_left f hd :
      ((f * d : ℕ) : ℝ) ≤ ((f * level : ℕ) : ℝ)).trans hheight

/-- If the total level exponent is strictly below the height exponent,
the complete level-restricted height condition holds eventually, uniformly
in every smoothness layer. -/
theorem eventually_uniform_normRosser_height_condition
    {degree : ℕ} (hdegree : 0 < degree)
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 ≤ eta)
    (S : ℕ) (heightCoefficient : ℝ) (hheightCoefficient : 0 < heightCoefficient)
    (hgap : delta + eta * S < (degree : ℝ)⁻¹) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ∀ f : ℕ, f ≤ (t + 1) ^ oddTensorDepth t →
        ((f * normSieveUpper eta x ^ S : ℕ) : ℝ) ≤
          heightCoefficient * (x : ℝ) ^ (degree : ℝ)⁻¹ := by
  let a : ℝ := delta + eta * S
  let b : ℝ := (degree : ℝ)⁻¹
  let L : ℝ := (2 : ℝ) ^ S
  have hba : 0 < b - a := sub_pos.mpr hgap
  have hpowTop : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ x : ℕ in atTop,
      L / heightCoefficient ≤ (x : ℝ) ^ (b - a) :=
    hpowTop.eventually (eventually_ge_atTop (L / heightCoefficient))
  filter_upwards
    [eventually_uniform_auxiliary_mul_normSieveLevel_le_rpow
      hdelta heta S, hlarge, eventually_ge_atTop 1]
    with x hlevel hlargeX hx
  intro t ht f hf
  have hxpos : (0 : ℝ) < x := by positivity
  have hL : L ≤ heightCoefficient * (x : ℝ) ^ (b - a) := by
    rw [div_le_iff₀ hheightCoefficient] at hlargeX
    nlinarith
  calc
    ((f * normSieveUpper eta x ^ S : ℕ) : ℝ) ≤
        L * (x : ℝ) ^ a := by
      simpa only [L, a] using hlevel t ht f hf
    _ ≤ (heightCoefficient * (x : ℝ) ^ (b - a)) *
        (x : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hxpos.le _)
    _ = heightCoefficient * (x : ℝ) ^ b := by
      calc
        heightCoefficient * (x : ℝ) ^ (b - a) * (x : ℝ) ^ a =
            heightCoefficient * ((x : ℝ) ^ (b - a) * (x : ℝ) ^ a) := by ring
        _ = heightCoefficient * (x : ℝ) ^ ((b - a) + a) := by
          exact congrArg (heightCoefficient * ·)
            (Real.rpow_add hxpos (b - a) a).symm
        _ = heightCoefficient * (x : ℝ) ^ b := by
          congr 2
          ring
    _ = heightCoefficient * (x : ℝ) ^ (degree : ℝ)⁻¹ := by rfl

/-- Algebraic conversion of a full-coordinate ray-cardinality bound, a
height-power bound, and the level scale into the exact Rosser boundary
power. -/
theorem normRosser_boundary_scale_le
    {degree f rayCard level : ℕ} (hdegree : 0 < degree) (hf : f ≠ 0)
    {height Cgeom heightCoefficient levelCoefficient x delta : ℝ}
    (hheight : 0 ≤ height) (hCgeom : 0 ≤ Cgeom)
    (hheightPow : height ^ (degree - 1) ≤
      heightCoefficient * x ^ (1 - (degree : ℝ)⁻¹))
    (hheightCoefficient : 0 ≤ heightCoefficient)
    (hcard : rayCard ≤ f ^ degree)
    (hlevel : ((f * level : ℕ) : ℝ) ≤
      levelCoefficient * x ^ delta)
    (hlevelCoefficient : 0 ≤ levelCoefficient)
    (hx : 0 < x) :
    (Cgeom * (rayCard : ℝ) *
        (height / f) ^ (degree - 1)) * level ≤
      (Cgeom * heightCoefficient * levelCoefficient) *
        x ^ (1 - (degree : ℝ)⁻¹ + delta) := by
  have hfR : (0 : ℝ) < f := by
    exact_mod_cast Nat.pos_of_ne_zero hf
  have hcardR : (rayCard : ℝ) ≤ (f : ℝ) ^ degree := by
    exact_mod_cast hcard
  have hratio : (rayCard : ℝ) / (f : ℝ) ^ degree ≤ 1 :=
    (div_le_one (pow_pos hfR _)).mpr hcardR
  have hratio0 : 0 ≤ (rayCard : ℝ) / (f : ℝ) ^ degree :=
    div_nonneg (by positivity) (by positivity)
  have hrewrite :
      (Cgeom * (rayCard : ℝ) *
          (height / f) ^ (degree - 1)) * level =
        Cgeom * ((rayCard : ℝ) / (f : ℝ) ^ degree) *
          height ^ (degree - 1) * ((f * level : ℕ) : ℝ) := by
    have hpow : (f : ℝ) ^ degree =
        (f : ℝ) ^ (degree - 1) * f := by
      rw [← pow_succ, Nat.sub_add_cancel hdegree]
    rw [Nat.cast_mul, div_pow, hpow]
    field_simp
  rw [hrewrite]
  calc
    Cgeom * ((rayCard : ℝ) / (f : ℝ) ^ degree) *
          height ^ (degree - 1) * ((f * level : ℕ) : ℝ) ≤
      Cgeom * 1 *
          (heightCoefficient * x ^ (1 - (degree : ℝ)⁻¹)) *
          (levelCoefficient * x ^ delta) := by
        gcongr
    _ = (Cgeom * heightCoefficient * levelCoefficient) *
        x ^ (1 - (degree : ℝ)⁻¹ + delta) := by
      rw [Real.rpow_add hx]
      ring

theorem normRosserBeta_pos
    (K : Type*) [Field K] [NumberField K] :
    1 ≤ normRosserBeta K := by
  unfold normRosserBeta
  have := two_le_normSieveDimension K
  omega

theorem normRosserLevel_pos
    {K : Type*} [Field K] [NumberField K]
    {y S : ℕ} (hy : 1 ≤ y) :
    1 ≤ y ^ S := by
  exact one_le_pow₀ hy



/-- After multiplying the fixed cell-main coefficient into the norm-form
Rosser main term, the strengthened tensor depth absorbs the complete
moving-lower polylogarithm.  The remaining hypotheses merely say that the
chosen ceiling endpoint has entered the Mertens range and dominates the
explicit sieve lower endpoint. -/
theorem exists_eventually_tensorWeighted_upperMainTerm_le_inverseSquare
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    (mainCoefficient : ℝ) (hmainCoefficient : 0 ≤ mainCoefficient)
    {ell : ℕ} (hell : 2 ≤ ell) {eta : ℝ} (heta : 0 < eta) :
    ∃ A : ℝ, ∃ S W : ℕ,
      0 ≤ A ∧ normRosserBeta K + 1 ≤ S ∧
      ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
        f ≤ (t + 1) ^ oddTensorDepth t →
        ∀ x : ℕ, 1 < x →
          W ≤ normSieveUpper eta x + 1 →
          normSieveLower K J f ≤ normSieveUpper eta x →
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
              upperMainTerm
                (rosserStoppingPredicate (normRosserBeta K)
                  (normSieveUpper eta x ^ S))
                (coordinateNormDensity K J)
                (ascendingSievePrimes (normSieveLower K J f)
                  (normSieveUpper eta x)) ≤
            A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Acut, S, hAcut, hS, hmain⟩ :=
    exists_coordinateNorm_mainTerm_bounds K
  obtain ⟨Ceuler, W, hCeuler, heuler⟩ :=
    exists_normSieveUpper_finiteEuler_bound K
  let cutoff : ℝ :=
    (4 * Acut / 3) * (1 / 4 : ℝ) ^ (S - normRosserBeta K)
  let tensorConstant : ℝ := (4 * 16 ^ normSieveDimension K : ℝ)
  let A : ℝ := mainCoefficient * ((1 + cutoff) * Ceuler / eta) *
    tensorConstant
  have hcutoff : 0 ≤ cutoff := by
    dsimp [cutoff]
    positivity
  have htensorConstant : 0 ≤ tensorConstant := by
    dsimp [tensorConstant]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have htensor :=
    eventually_tensorDensity_mul_lowerLogPow_le_inverseSquare K J hell
  refine ⟨A, S, W, hA, hS, ?_⟩
  filter_upwards [htensor] with t ht
  intro f hf0 hf x hx hW hlow
  let y := normSieveUpper eta x
  let z := normSieveLower K J f
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hupper := hmain J f y S hlow le_rfl
  have heuler' := heuler J f x eta heta hx hW hlow
  have hupper' :
      upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
        (1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ))) := by
    exact hupper.trans (mul_le_mul_of_nonneg_left heuler' (by positivity))
  have hmult : 0 ≤ ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
      mainCoefficient * (x : ℝ) := by positivity
  have hraw := mul_le_mul_of_nonneg_left hupper' hmult
  calc
    (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
      (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        ((1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ)))) := hraw
    _ = (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
            Real.log (z : ℝ) ^ normSieveDimension K) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      field_simp [hxlog.ne']
    _ ≤ (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          (tensorConstant / (((t + 1 : ℕ) : ℝ) ^ 2)) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      gcongr
      simpa only [tensorConstant, z] using ht f hf0 hf
    _ = A * ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [A]
      ring

/-- Non-circular parameter selection: the fixed Rosser depth is chosen
first, and only then are the endpoint and auxiliary exponents selected.
They satisfy the strict height budget while retaining the post-tensor
inverse-square main-term estimate. -/
theorem exists_smallEndpoint_tensorWeighted_upperMainTerm_le_inverseSquare
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰)
    (mainCoefficient : ℝ) (hmainCoefficient : 0 ≤ mainCoefficient)
    {ell : ℕ} (hell : 2 ≤ ell) :
    ∃ eta delta A : ℝ, ∃ S W : ℕ,
      0 < eta ∧ 0 < delta ∧ eta ≤ 1 ∧
      delta + eta * S < (normSieveDegree K : ℝ)⁻¹ ∧
      0 ≤ A ∧ normRosserBeta K + 1 ≤ S ∧
      ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
        f ≤ (t + 1) ^ oddTensorDepth t →
        ∀ x : ℕ, 1 < x →
          W ≤ normSieveUpper eta x + 1 →
          normSieveLower K J f ≤ normSieveUpper eta x →
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
              upperMainTerm
                (rosserStoppingPredicate (normRosserBeta K)
                  (normSieveUpper eta x ^ S))
                (coordinateNormDensity K J)
                (ascendingSievePrimes (normSieveLower K J f)
                  (normSieveUpper eta x)) ≤
            A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Acut, S, hAcut, hS, hmain⟩ :=
    exists_coordinateNorm_mainTerm_bounds K
  let d : ℝ := normSieveDegree K
  let delta : ℝ := 1 / (8 * d)
  let eta : ℝ := 1 / (8 * d * (S + 1))
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast normSieveDegree_pos K
  have hd1 : (1 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast (Nat.succ_le_iff.mpr (normSieveDegree_pos K))
  have hS1 : (0 : ℝ) < S + 1 := by positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    apply (div_le_one (by positivity)).2
    calc
      (1 : ℝ) ≤ 8 := by norm_num
      _ ≤ 8 * d := by nlinarith
      _ ≤ 8 * d * ((S : ℝ) + 1) := by
        nlinarith [mul_nonneg (show 0 ≤ 8 * d by positivity)
          (Nat.cast_nonneg S : (0 : ℝ) ≤ S)]
  have hetaS : eta * (S : ℝ) ≤ delta := by
    dsimp [eta, delta]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htwodelta : 2 * delta < d⁻¹ := by
    dsimp [delta]
    rw [show 2 * (1 / (8 * d)) = 2 / (8 * d) by ring, inv_eq_one_div,
      div_lt_div_iff₀ (by positivity) hd]
    nlinarith
  have hgap : delta + eta * S < (normSieveDegree K : ℝ)⁻¹ := by
    change delta + eta * (S : ℝ) < d⁻¹
    linarith
  obtain ⟨Ceuler, W, hCeuler, heuler⟩ :=
    exists_normSieveUpper_finiteEuler_bound K
  let cutoff : ℝ :=
    (4 * Acut / 3) * (1 / 4 : ℝ) ^ (S - normRosserBeta K)
  let tensorConstant : ℝ := (4 * 16 ^ normSieveDimension K : ℝ)
  let A : ℝ := mainCoefficient * ((1 + cutoff) * Ceuler / eta) *
    tensorConstant
  have hA : 0 ≤ A := by
    dsimp [A, cutoff, tensorConstant]
    positivity
  have htensor :=
    eventually_tensorDensity_mul_lowerLogPow_le_inverseSquare K J hell
  refine ⟨eta, delta, A, S, W, heta, hdelta, heta1, hgap, hA, hS, ?_⟩
  filter_upwards [htensor] with t ht
  intro f hf0 hf x hx hW hlow
  let y := normSieveUpper eta x
  let z := normSieveLower K J f
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hupper := hmain J f y S hlow le_rfl
  have heuler' := heuler J f x eta heta hx hW hlow
  have hupper' :
      upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
        (1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ))) := by
    exact hupper.trans (mul_le_mul_of_nonneg_left heuler' (by positivity))
  have hmult : 0 ≤ ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
      mainCoefficient * (x : ℝ) := by positivity
  have hraw := mul_le_mul_of_nonneg_left hupper' hmult
  calc
    (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
      (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        ((1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ)))) := hraw
    _ = (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
            Real.log (z : ℝ) ^ normSieveDimension K) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      field_simp [hxlog.ne']
    _ ≤ (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          (tensorConstant / (((t + 1 : ℕ) : ℝ) ^ 2)) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      gcongr
      simpa only [tensorConstant, z] using ht f hf0 hf
    _ = A * ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [A]
      ring

/-- Uniform field-only parameter selection for a finite correction cover.
The endpoint exponent, auxiliary exponent, Rosser depth, and Mertens
threshold are common to every correction ideal; only the harmless fixed
cell-main constant is allowed to vary. -/
theorem exists_uniform_smallEndpoint_tensorWeighted_upperMainTerm_le_inverseSquare
    (K : Type*) [Field K] [NumberField K]
    {ell : ℕ} (hell : 2 ≤ ell) :
    ∃ eta delta : ℝ, ∃ S W : ℕ,
      0 < eta ∧ 0 < delta ∧ eta ≤ 1 ∧
      delta + eta * S < (normSieveDegree K : ℝ)⁻¹ ∧
      normRosserBeta K + 1 ≤ S ∧
      ∀ (J : (Ideal (RingOfIntegers K))⁰) (mainCoefficient : ℝ),
        0 ≤ mainCoefficient →
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
            f ≤ (t + 1) ^ oddTensorDepth t →
            ∀ x : ℕ, 1 < x →
              W ≤ normSieveUpper eta x + 1 →
              normSieveLower K J f ≤ normSieveUpper eta x →
              (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
                    mainCoefficient * (x : ℝ)) *
                  upperMainTerm
                    (rosserStoppingPredicate (normRosserBeta K)
                      (normSieveUpper eta x ^ S))
                    (coordinateNormDensity K J)
                    (ascendingSievePrimes (normSieveLower K J f)
                      (normSieveUpper eta x)) ≤
                A * ((x : ℝ) / Real.log (x : ℝ)) /
                  (((t + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Acut, S, hAcut, hS, hmain⟩ :=
    exists_coordinateNorm_mainTerm_bounds K
  let d : ℝ := normSieveDegree K
  let delta : ℝ := 1 / (8 * d)
  let eta : ℝ := 1 / (8 * d * (S + 1))
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast normSieveDegree_pos K
  have hd1 : (1 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast (Nat.succ_le_iff.mpr (normSieveDegree_pos K))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    apply (div_le_one (by positivity)).2
    calc
      (1 : ℝ) ≤ 8 := by norm_num
      _ ≤ 8 * d := by nlinarith
      _ ≤ 8 * d * ((S : ℝ) + 1) := by
        nlinarith [mul_nonneg (show 0 ≤ 8 * d by positivity)
          (Nat.cast_nonneg S : (0 : ℝ) ≤ S)]
  have hetaS : eta * (S : ℝ) ≤ delta := by
    dsimp [eta, delta]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htwodelta : 2 * delta < d⁻¹ := by
    dsimp [delta]
    rw [show 2 * (1 / (8 * d)) = 2 / (8 * d) by ring, inv_eq_one_div,
      div_lt_div_iff₀ (by positivity) hd]
    nlinarith
  have hgap : delta + eta * S < (normSieveDegree K : ℝ)⁻¹ := by
    change delta + eta * (S : ℝ) < d⁻¹
    linarith
  obtain ⟨Ceuler, W, hCeuler, heuler⟩ :=
    exists_normSieveUpper_finiteEuler_bound K
  refine ⟨eta, delta, S, W, heta, hdelta, heta1, hgap, hS, ?_⟩
  intro J mainCoefficient hmainCoefficient
  let cutoff : ℝ :=
    (4 * Acut / 3) * (1 / 4 : ℝ) ^ (S - normRosserBeta K)
  let tensorConstant : ℝ := (4 * 16 ^ normSieveDimension K : ℝ)
  let A : ℝ := mainCoefficient * ((1 + cutoff) * Ceuler / eta) *
    tensorConstant
  have hA : 0 ≤ A := by
    dsimp [A, cutoff, tensorConstant]
    positivity
  refine ⟨A, hA, ?_⟩
  have htensor :=
    eventually_tensorDensity_mul_lowerLogPow_le_inverseSquare K J hell
  filter_upwards [htensor] with t ht
  intro f hf0 hf x hx hW hlow
  let y := normSieveUpper eta x
  let z := normSieveLower K J f
  have hxlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hupper := hmain J f y S hlow le_rfl
  have heuler' := heuler J f x eta heta hx hW hlow
  have hupper' :
      upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
        (1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ))) := by
    exact hupper.trans (mul_le_mul_of_nonneg_left heuler' (by positivity))
  have hmult : 0 ≤ ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
      mainCoefficient * (x : ℝ) := by positivity
  have hraw := mul_le_mul_of_nonneg_left hupper' hmult
  calc
    (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        upperMainTerm
          (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K J)
          (ascendingSievePrimes z y) ≤
      (((ell : ℝ)⁻¹) ^ oddTensorDepth t * mainCoefficient * (x : ℝ)) *
        ((1 + cutoff) *
          (Ceuler * Real.log (z : ℝ) ^ normSieveDimension K /
            (eta * Real.log (x : ℝ)))) := hraw
    _ = (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
            Real.log (z : ℝ) ^ normSieveDimension K) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      field_simp [hxlog.ne']
    _ ≤ (mainCoefficient * ((1 + cutoff) * Ceuler / eta)) *
          ((4 * 16 ^ normSieveDimension K : ℝ) /
            (((t + 1 : ℕ) : ℝ) ^ 2)) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      gcongr
      simpa only [z] using ht f hf0 hf
    _ = A * ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [A, tensorConstant]
      ring


end Erdos980.ElliottTail.OddRosserParameters

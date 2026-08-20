/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveGoodRoot
import ErdosProblems.Erdos48.PowerSieveLargeFactor
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# The pointwise progression budget for the integer-power sieve

This file packages the analytic input needed by `PowerSieveGoodRoot`.  The
weight below is deliberately smaller than the natural progression main term
by a polynomial in `L`; this leaves room for both the beta-sieve main term and
the Bombieri--Vinogradov remainders.
-/

namespace Erdos48

open Filter Asymptotics
open scoped Topology BigOperators Asymptotics

noncomputable section

open BoundedGaps.Maynard

/-- An unconditional quarter-level Bombieri--Vinogradov witness exists with
any prescribed positive logarithmic saving. -/
theorem exists_quarter_primeLevelWitness (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness (1 / 4 : ℝ) A C X₀ := by
  apply hasPrimeLevel_exists_witness
  · exact unconditional_bombieriVinogradov (1 / 4) (by norm_num) (by norm_num)
  · exact hA

/-- The positive weight eventually assigned to a good dyadic root. -/
def powerSieveGoodRootWeight (n L q : ℕ) : ℝ :=
  (powerSieveX n L : ℝ) /
    ((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
      (1000000 * (L : ℝ) ^ 2))

theorem powerSieveGoodRootWeight_nonneg (n L q : ℕ) :
    0 ≤ powerSieveGoodRootWeight n L q := by
  unfold powerSieveGoodRootWeight
  positivity

/-- The chosen weight uses at most one hundredth of the progression main
term.  Only the elementary inequality `phi(qr) ≤ qr` is needed here. -/
theorem powerSieveGoodRootWeight_mul_inv_le
    {n L q r : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hq : 0 < q) (hr : 0 < r) :
    powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
      (powerSieveX n L : ℝ) /
        (100 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ)) := by
  have hx : 2 ≤ powerSieveX n L := by
    unfold powerSieveX
    exact hn.trans (Nat.le_pow (by omega : 0 < 240 * L))
  have hlog : 0 < Real.log (powerSieveX n L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < powerSieveX n L by omega))
  have hphiNat : 0 < Nat.totient (q * r) :=
    Nat.totient_pos.mpr (Nat.mul_pos hq hr)
  have hphi : (0 : ℝ) < Nat.totient (q * r) := by exact_mod_cast hphiNat
  have hphiLe : (Nat.totient (q * r) : ℝ) ≤ (q : ℝ) * (r : ℝ) := by
    exact_mod_cast Nat.totient_le (q * r)
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcoef : (100 : ℝ) ≤ 1000000 * (L : ℝ) ^ 2 := by nlinarith
  have hden :
      100 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) ≤
        ((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
          (1000000 * (L : ℝ) ^ 2)) * (r : ℝ) := by
    calc
      100 * (Nat.totient (q * r) : ℝ) *
          Real.log (powerSieveX n L : ℝ) ≤
          100 * ((q : ℝ) * (r : ℝ)) *
            Real.log (powerSieveX n L : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphiLe (by norm_num)) hlog.le
      _ ≤ (1000000 * (L : ℝ) ^ 2) * ((q : ℝ) * (r : ℝ)) *
          Real.log (powerSieveX n L : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hlog.le
      _ = ((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
          (1000000 * (L : ℝ) ^ 2)) * (r : ℝ) := by ring
  unfold powerSieveGoodRootWeight
  have hrewrite :
      (powerSieveX n L : ℝ) /
          ((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
            (1000000 * (L : ℝ) ^ 2)) * (r : ℝ)⁻¹ =
        (powerSieveX n L : ℝ) /
          (((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
            (1000000 * (L : ℝ) ^ 2)) * (r : ℝ)) := by
    field_simp
  rw [hrewrite]
  rw [div_le_div_iff₀ (by positivity :
      0 < ((q : ℝ) * Real.log (powerSieveX n L : ℝ) *
        (1000000 * (L : ℝ) ^ 2)) * (r : ℝ))
    (by positivity : 0 < 100 * (Nat.totient (q * r) : ℝ) *
      Real.log (powerSieveX n L : ℝ))]
  exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- The PNT main term at the integer-power endpoint, with a fixed explicit
ten-percent margin. -/
theorem eventually_nine_tenths_mul_powerSieveX_le_theta
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      (9 / 10 : ℝ) * (powerSieveX n L : ℝ) ≤
        Chebyshev.theta (powerSieveX n L : ℝ) := by
  have hne : ∀ᶠ x : ℕ in atTop, (x : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact_mod_cast (show x ≠ 0 by omega)
  have hratio : Tendsto
      (fun x : ℕ => Chebyshev.theta (x : ℝ) / (x : ℝ))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hne).mp
      BoundedGaps.PrimeNumberTheorem.chebyshevTheta_natCast_isEquivalent
  have hpow : Tendsto (fun n : ℕ => powerSieveX n L) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max b 2, ?_⟩
    intro n hn
    have hbn : b ≤ n := (le_max_left b 2).trans hn
    have hnpow : n ≤ n ^ (240 * L) := Nat.le_pow (by omega)
    exact hbn.trans hnpow
  have hlower : ∀ᶠ n : ℕ in atTop,
      (9 / 10 : ℝ) <
        Chebyshev.theta (powerSieveX n L : ℝ) /
          (powerSieveX n L : ℝ) :=
    ((tendsto_order.1 (hratio.comp hpow)).1 _ (by norm_num))
  filter_upwards [hlower, eventually_ge_atTop 2] with n hlower hn
  have hxpos : (0 : ℝ) < powerSieveX n L := by
    exact_mod_cast (show 0 < powerSieveX n L by
      unfold powerSieveX
      positivity)
  exact (le_of_lt ((lt_div_iff₀ hxpos).mp hlower))

/-- Every fixed multiple of `log(n)^2` is eventually below any fixed
positive integral power of `n`. -/
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

/-- A fixed real constant is eventually below `n^2`. -/
private theorem eventually_const_le_nat_square (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, D ≤ (n : ℝ) ^ 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  exact ht.eventually_ge_atTop D

/-- The prime-power endpoint correction is uniformly negligible for every
modulus below the dyadic product cutoff. -/
theorem eventually_powerSieve_psi_sub_theta_le
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ n ^ (120 * L - 2) →
      Chebyshev.psi (powerSieveX n L : ℝ) -
          Chebyshev.theta (powerSieveX n L : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (100 * (Nat.totient d : ℝ)) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  filter_upwards [eventually_const_le_nat_square (100 * |C|),
    eventually_ge_atTop 2] with n hnLarge hn d hd hdUpper
  have hphiNat : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast hphiNat
  have hphiLe : (Nat.totient d : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.totient_le d
  have hdCast : (d : ℝ) ≤ (n : ℝ) ^ (120 * L - 2) := by
    exact_mod_cast hdUpper
  have hsqrt : Real.sqrt (powerSieveX n L : ℝ) =
      (n : ℝ) ^ (120 * L) := by
    have hx : (powerSieveX n L : ℝ) =
        ((n : ℝ) ^ (120 * L)) ^ 2 := by
      simp only [powerSieveX, Nat.cast_pow, ← pow_mul]
      congr 1
      omega
    rw [hx, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hgap : Chebyshev.psi (powerSieveX n L : ℝ) -
      Chebyshev.theta (powerSieveX n L : ℝ) ≤
        |C| * (n : ℝ) ^ (120 * L) := by
    calc
      Chebyshev.psi (powerSieveX n L : ℝ) -
          Chebyshev.theta (powerSieveX n L : ℝ) ≤
          C * Real.sqrt (powerSieveX n L : ℝ) := hC _
      _ ≤ |C| * Real.sqrt (powerSieveX n L : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
      _ = |C| * (n : ℝ) ^ (120 * L) := by rw [hsqrt]
  have hscale :
      100 * (Nat.totient d : ℝ) *
          (|C| * (n : ℝ) ^ (120 * L)) ≤
        (powerSieveX n L : ℝ) := by
    calc
      100 * (Nat.totient d : ℝ) *
          (|C| * (n : ℝ) ^ (120 * L)) ≤
          100 * (d : ℝ) *
            (|C| * (n : ℝ) ^ (120 * L)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphiLe (by norm_num)) (by positivity)
      _ ≤ 100 * ((n : ℝ) ^ (120 * L - 2)) *
            (|C| * (n : ℝ) ^ (120 * L)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdCast (by norm_num)) (by positivity)
      _ =
          (100 * |C|) * ((n : ℝ) ^ (120 * L - 2)) *
            ((n : ℝ) ^ (120 * L)) := by
        ring
      _ ≤ ((n : ℝ) ^ 2) * ((n : ℝ) ^ (120 * L - 2)) *
          ((n : ℝ) ^ (120 * L)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnLarge (by positivity)) (by positivity)
      _ = (powerSieveX n L : ℝ) := by
        simp only [powerSieveX, Nat.cast_pow, ← pow_add]
        congr 1
        omega
  rw [le_div_iff₀ (by positivity :
    0 < 100 * (Nat.totient d : ℝ))]
  calc
    (Chebyshev.psi (powerSieveX n L : ℝ) -
        Chebyshev.theta (powerSieveX n L : ℝ)) *
          (100 * (Nat.totient d : ℝ)) ≤
        (|C| * (n : ℝ) ^ (120 * L)) *
          (100 * (Nat.totient d : ℝ)) :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    _ = 100 * (Nat.totient d : ℝ) *
        (|C| * (n : ℝ) ^ (120 * L)) := by ring
    _ ≤ (powerSieveX n L : ℝ) := hscale

/-- The elementary logarithmic endpoint correction is uniformly negligible
for every modulus below the dyadic product cutoff. -/
theorem eventually_powerSieve_log_product_sq_le
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ n ^ (120 * L - 2) →
      Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
        (powerSieveX n L : ℝ) /
          (100 * (Nat.totient d : ℝ)) := by
  let D : ℝ := 100 * (((360 * L : ℕ) : ℝ) ^ 2)
  filter_upwards
    [eventually_const_mul_log_sq_le_nat_pow D (120 * L) (by omega),
      eventually_ge_atTop 2]
    with n hnLog hn d hd hdUpper
  have hnOne : 1 ≤ n := by omega
  have hphiNat : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast hphiNat
  have hphiLe : (Nat.totient d : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.totient_le d
  have hdCast : (d : ℝ) ≤ (n : ℝ) ^ (120 * L - 2) := by
    exact_mod_cast hdUpper
  have hdxUpper : d * powerSieveX n L ≤ n ^ (360 * L) := by
    calc
      d * powerSieveX n L ≤
          n ^ (120 * L - 2) * n ^ (240 * L) :=
        Nat.mul_le_mul hdUpper (by rfl)
      _ = n ^ ((120 * L - 2) + 240 * L) := by rw [← pow_add]
      _ ≤ n ^ (360 * L) := pow_le_pow_right' hnOne (by omega)
  have hdxNatPos : 0 < d * powerSieveX n L :=
    Nat.mul_pos hd (by
      unfold powerSieveX
      positivity)
  have hdxPos : (0 : ℝ) < (d * powerSieveX n L : ℕ) := by
    exact_mod_cast hdxNatPos
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnOne)
  have hlogProduct : 0 ≤
      Real.log ((d * powerSieveX n L : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast hdxNatPos)
  have hlogUpper :
      Real.log ((d * powerSieveX n L : ℕ) : ℝ) ≤
        ((360 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log ((d * powerSieveX n L : ℕ) : ℝ) ≤
          Real.log (((n : ℝ) ^ (360 * L))) := by
        apply Real.log_le_log hdxPos
        exact_mod_cast hdxUpper
      _ = ((360 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_pow]
  have hlogSq :
      Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
        (((360 * L : ℕ) : ℝ) ^ 2) * Real.log (n : ℝ) ^ 2 := by
    nlinarith
  have hscale :
      100 * (Nat.totient d : ℝ) *
          Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
        (powerSieveX n L : ℝ) := by
    calc
      100 * (Nat.totient d : ℝ) *
          Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
          100 * (d : ℝ) *
            ((((360 * L : ℕ) : ℝ) ^ 2) *
              Real.log (n : ℝ) ^ 2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hphiLe (by norm_num)) hlogSq
          (sq_nonneg _) (by positivity)
      _ ≤ (n : ℝ) ^ (120 * L - 2) *
          (D * Real.log (n : ℝ) ^ 2) := by
        dsimp only [D]
        have := mul_le_mul_of_nonneg_right hdCast (by positivity :
          0 ≤ 100 * (((360 * L : ℕ) : ℝ) ^ 2) *
            Real.log (n : ℝ) ^ 2)
        nlinarith
      _ ≤ (n : ℝ) ^ (120 * L - 2) * (n : ℝ) ^ (120 * L) :=
        mul_le_mul_of_nonneg_left hnLog (by positivity)
      _ ≤ (powerSieveX n L : ℝ) := by
        simp only [powerSieveX, Nat.cast_pow, ← pow_add]
        exact pow_le_pow_right₀ (by exact_mod_cast hnOne) (by omega)
  rw [le_div_iff₀ (by positivity :
    0 < 100 * (Nat.totient d : ℝ))]
  calc
    Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 *
        (100 * (Nat.totient d : ℝ)) =
      100 * (Nat.totient d : ℝ) *
        Real.log ((d * powerSieveX n L : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ (powerSieveX n L : ℝ) := hscale

/-- Every beta-sieve constant admits a fixed Rosser depth with the parameter
inequality required by the pointwise large-factor theorem. -/
theorem exists_admissible_powerSieveDepth (A : ℝ) :
    ∃ S : ℕ, 101 ≤ S ∧
      Real.log A ≤ 2 * (S - 100 : ℕ) / 99 := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_ge ((99 / 2 : ℝ) * Real.log A)
  refine ⟨m + 101, by omega, ?_⟩
  rw [show m + 101 - 100 = m + 1 by omega]
  norm_num [div_eq_mul_inv] at hm ⊢
  nlinarith

/-- The exact beta-sieve envelope, specialized to a log-saving exponent of
`100`, whose eventual comparison with the progression main term remains. -/
def powerSievePointwiseEnvelope
    (Aβ Cπ CV CBV : ℝ) (S n L q r : ℕ) : ℝ :=
  let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  ∑ b ∈ Finset.Icc 1 (powerSieveCofactorBound n L),
    ((Cπ * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
        Real.log ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) *
      ((1 + eta) *
        (CV * ((q * r * b : ℕ) : ℝ) /
            (Nat.totient (q * r * b) : ℝ) /
          Real.log (powerSieveSmallPrimeBound n L S : ℝ)))) +
      CBV * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
        Real.rpow
          (Real.log ((((powerSieveX n L + 1) /
            (q * r * b) : ℕ) : ℝ))) 100 +
      CBV * (powerSieveResidualCutoff n L : ℝ) /
        Real.rpow
          (Real.log (powerSieveResidualCutoff n L : ℝ)) 100)

/-- Closed, unconditional choice of beta-sieve constants, Rosser depth, and
quarter-level Bombieri--Vinogradov witness.  Uniformly in every later
`L ≥ S+1`, the represented exceptional set is bounded by the displayed
pointwise envelope throughout every admissible dyadic block. -/
theorem exists_eventually_representedLargeFactorPrimes_le_pointwiseEnvelope :
    ∃ Aβ Cπ CV CBV : ℝ, ∃ S X₀ : ℕ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧ 0 ≤ CBV ∧
      101 ≤ S ∧ Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 ∧
      PrimeLevelWitness (1 / 4 : ℝ) 100 CBV X₀ ∧
      ∀ L : ℕ, S + 1 ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          2 * Q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) ≤
            powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hpoint⟩ :=
    exists_powerSieve_representedLargeFactorPrimes_pointwise_upper_bound
  obtain ⟨S, hS, hlogAβ⟩ := exists_admissible_powerSieveDepth Aβ
  obtain ⟨CBV, X₀, hw⟩ :=
    exists_quarter_primeLevelWitness 100 (by norm_num)
  refine ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hw.1,
    hS, hlogAβ, hw, ?_⟩
  intro L hSL
  filter_upwards [eventually_ge_atTop (max X₀ 4)] with n hn
  intro Q q r hQ hqLower hqUpper hQupper hr
  have hnFour : 4 ≤ n := (le_max_right X₀ 4).trans hn
  have hX₀n : X₀ ≤ n := (le_max_left X₀ 4).trans hn
  have hX₀pow : X₀ ≤ n ^ L :=
    hX₀n.trans (Nat.le_pow (by omega : 0 < L))
  have hbound := hpoint (Bexp := (100 : ℝ)) (CBV := CBV)
    (X₀ := X₀) (n := n) (L := L) (S := S) (Q := Q)
    (q := q) (r := r) hnFour hS hSL hQ hqLower hqUpper hQupper hr
    hlogAβ hw hX₀pow
  simpa only [powerSievePointwiseEnvelope] using hbound

/-- Pure algebraic core of the progression budget.  The four hypotheses
reserve respectively the PNT main term, the elementary logarithmic endpoint
error, the prime-power endpoint error, and the pointwise beta-sieve term. -/
theorem represented_add_weight_le_powerSieveProgressionBudget_of_bounds
    {x q r : ℕ} {W represented : ℝ}
    (hx : 2 ≤ x) (hqr : 0 < q * r)
    (htheta : (9 / 10 : ℝ) * (x : ℝ) ≤ Chebyshev.theta (x : ℝ))
    (hlogError : Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 ≤
      (x : ℝ) / (100 * (Nat.totient (q * r) : ℝ)))
    (hprimePower : Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
      (x : ℝ) / (100 * (Nat.totient (q * r) : ℝ)))
    (hrepresented : represented ≤
      (x : ℝ) / (4 * (Nat.totient (q * r) : ℝ) * Real.log (x : ℝ)))
    (hweight : W * (r : ℝ)⁻¹ ≤
      (x : ℝ) / (100 * (Nat.totient (q * r) : ℝ) * Real.log (x : ℝ))) :
    represented + W * (r : ℝ)⁻¹ ≤
      powerSieveProgressionBudget x q r := by
  have hxReal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hxReal
  have hphiNat : 0 < Nat.totient (q * r) := Nat.totient_pos.mpr hqr
  have hphi : (0 : ℝ) < Nat.totient (q * r) := by exact_mod_cast hphiNat
  unfold powerSieveProgressionBudget
  rw [le_div_iff₀ hlogx]
  have hrepWeight :
      (represented + W * (r : ℝ)⁻¹) * Real.log (x : ℝ) ≤
        (13 / 50 : ℝ) * ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by
    have hrep : represented * Real.log (x : ℝ) ≤
        (1 / 4 : ℝ) * ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by
      calc
        represented * Real.log (x : ℝ) ≤
            ((x : ℝ) /
              (4 * (Nat.totient (q * r) : ℝ) * Real.log (x : ℝ))) *
                Real.log (x : ℝ) :=
          mul_le_mul_of_nonneg_right hrepresented hlogx.le
        _ = (1 / 4 : ℝ) *
            ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by field_simp
    have hw : (W * (r : ℝ)⁻¹) * Real.log (x : ℝ) ≤
        (1 / 100 : ℝ) * ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by
      calc
        (W * (r : ℝ)⁻¹) * Real.log (x : ℝ) ≤
            ((x : ℝ) /
              (100 * (Nat.totient (q * r) : ℝ) * Real.log (x : ℝ))) *
                Real.log (x : ℝ) :=
          mul_le_mul_of_nonneg_right hweight hlogx.le
        _ = (1 / 100 : ℝ) *
            ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by field_simp
    rw [add_mul]
    linarith
  have hbudgetNumerator :
      (13 / 50 : ℝ) * ((x : ℝ) / (Nat.totient (q * r) : ℝ)) ≤
        Chebyshev.theta (x : ℝ) / (Nat.totient (q * r) : ℝ) -
          (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
            ((Nat.totient (q * r) : ℝ))⁻¹ * (4 * ((x : ℝ) / 10)) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
    have hthetaDiv : (9 / 10 : ℝ) *
        ((x : ℝ) / (Nat.totient (q * r) : ℝ)) ≤
          Chebyshev.theta (x : ℝ) / (Nat.totient (q * r) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right htheta (inv_nonneg.mpr hphi.le)
      simpa only [div_eq_mul_inv, mul_assoc] using h
    have herrorScale : (x : ℝ) /
        (100 * (Nat.totient (q * r) : ℝ)) =
          (1 / 100 : ℝ) *
            ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by
      field_simp
    have hmiddle : ((Nat.totient (q * r) : ℝ))⁻¹ *
        (4 * ((x : ℝ) / 10)) =
          (2 / 5 : ℝ) * ((x : ℝ) / (Nat.totient (q * r) : ℝ)) := by
      field_simp
      ring
    rw [hmiddle]
    rw [herrorScale] at hlogError hprimePower
    let T : ℝ := (x : ℝ) / (Nat.totient (q * r) : ℝ)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    change (13 / 50 : ℝ) * T ≤
      Chebyshev.theta (x : ℝ) / (Nat.totient (q * r) : ℝ) -
        (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
          (2 / 5 : ℝ) * T +
            (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))
    change (9 / 10 : ℝ) * T ≤ _ at hthetaDiv
    change _ ≤ (1 / 100 : ℝ) * T at hlogError hprimePower
    linarith
  exact hrepWeight.trans hbudgetNumerator

/-- Eventual dyadic budget wrapper.  The only numerical inputs left explicit
are the pointwise represented-card estimate and the two endpoint errors; the
PNT main term and the concrete weight estimate are supplied unconditionally
and uniformly in `Q`, `q`, and `r`. -/
theorem eventually_represented_add_goodRootWeight_le_budget_of_bounds
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (4 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) →
      Real.log (((q * r) * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
        (powerSieveX n L : ℝ) /
          (100 * (Nat.totient (q * r) : ℝ)) →
      Chebyshev.psi (powerSieveX n L : ℝ) -
          Chebyshev.theta (powerSieveX n L : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (100 * (Nat.totient (q * r) : ℝ)) →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
          powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r := by
  filter_upwards [eventually_nine_tenths_mul_powerSieveX_le_theta L hL,
    eventually_ge_atTop 2] with n htheta hn Q q r hQ hqLower hqUpper hr
      hrepresented hlogError hprimePower
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  apply represented_add_weight_le_powerSieveProgressionBudget_of_bounds
    (x := powerSieveX n L) (q := q) (r := r)
    (W := powerSieveGoodRootWeight n L q)
    (represented := ((representedLargeFactorPrimes
      (powerSieveX n L) (powerSieveSmoothBound n L) q r
        (powerSieveCofactorBound n L)).card : ℝ))
  · unfold powerSieveX
    exact hn.trans (Nat.le_pow (by omega : 0 < 240 * L))
  · exact Nat.mul_pos hqPos hrPos
  · exact htheta
  · exact hlogError
  · exact hprimePower
  · exact hrepresented
  · exact powerSieveGoodRootWeight_mul_inv_le hn hL hqPos hrPos

/-- The same wrapper with the prime-power error discharged.  Thus the only
remaining endpoint input is the elementary logarithmic square, in addition
to the represented-card estimate itself. -/
theorem eventually_represented_add_goodRootWeight_le_budget_of_card_and_log
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      2 * Q ≤ powerSieveSmoothBound n L →
      r ∈ powerSieveAuxPrimes n L Q →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) ≤
        (powerSieveX n L : ℝ) /
          (4 * (Nat.totient (q * r) : ℝ) *
            Real.log (powerSieveX n L : ℝ)) →
      Real.log (((q * r) * powerSieveX n L : ℕ) : ℝ) ^ 2 ≤
        (powerSieveX n L : ℝ) /
          (100 * (Nat.totient (q * r) : ℝ)) →
      ((representedLargeFactorPrimes
        (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) +
          powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
        powerSieveProgressionBudget (powerSieveX n L) q r := by
  filter_upwards
    [eventually_represented_add_goodRootWeight_le_budget_of_bounds L hL,
      eventually_powerSieve_psi_sub_theta_le L hL,
      eventually_ge_atTop 4]
    with n hbudget hprimePower hn Q q r hQ hqLower hqUpper hQupper hr
      hrepresented hlogError
  have hqrUpper : q * r ≤ n ^ (120 * L - 2) :=
    powerSieve_root_mul_aux_le hn hL hQupper hqUpper hr
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  exact hbudget Q q r hQ hqLower hqUpper hr hrepresented hlogError
    (hprimePower (q * r) (Nat.mul_pos hqPos hrPos) hqrUpper)

/-- Fully unconditional endpoint wrapper.  At this point the sole remaining
numeric hypothesis is the sharp represented-large-factor cardinality bound
which the beta-sieve estimate must provide. -/
theorem eventually_represented_add_goodRootWeight_le_budget_of_card
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
      1 ≤ Q → Q < q → q ≤ 2 * Q →
      2 * Q ≤ powerSieveSmoothBound n L →
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
    [eventually_represented_add_goodRootWeight_le_budget_of_card_and_log L hL,
      eventually_powerSieve_log_product_sq_le L hL,
      eventually_ge_atTop 4]
    with n hbudget hlogError hn Q q r hQ hqLower hqUpper hQupper hr
      hrepresented
  have hqrUpper : q * r ≤ n ^ (120 * L - 2) :=
    powerSieve_root_mul_aux_le hn hL hQupper hqUpper hr
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  exact hbudget Q q r hQ hqLower hqUpper hQupper hr hrepresented
    (hlogError (q * r) (Nat.mul_pos hqPos hrPos) hqrUpper)

/-- Consolidated interface for the dyadic bad-root argument.  All analytic
inputs have been selected and proved except one transparent inequality: the
displayed beta-sieve envelope must occupy at most one quarter of the
progression main term. -/
theorem exists_eventually_represented_add_goodRootWeight_le_budget_of_envelope :
    ∃ Aβ Cπ CV CBV : ℝ, ∃ S X₀ : ℕ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧ 0 ≤ CBV ∧
      101 ≤ S ∧ Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 ∧
      PrimeLevelWitness (1 / 4 : ℝ) 100 CBV X₀ ∧
      ∀ L : ℕ, S + 1 ≤ L →
        ∀ᶠ n : ℕ in atTop, ∀ Q q r : ℕ,
          1 ≤ Q → Q < q → q ≤ 2 * Q →
          2 * Q ≤ powerSieveSmoothBound n L →
          r ∈ powerSieveAuxPrimes n L Q →
          powerSievePointwiseEnvelope Aβ Cπ CV CBV S n L q r ≤
            (powerSieveX n L : ℝ) /
              (4 * (Nat.totient (q * r) : ℝ) *
                Real.log (powerSieveX n L : ℝ)) →
          ((representedLargeFactorPrimes
            (powerSieveX n L) (powerSieveSmoothBound n L) q r
              (powerSieveCofactorBound n L)).card : ℝ) +
              powerSieveGoodRootWeight n L q * (r : ℝ)⁻¹ ≤
            powerSieveProgressionBudget (powerSieveX n L) q r := by
  obtain ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hCBV, hS,
    hlogAβ, hw, hrepresented⟩ :=
      exists_eventually_representedLargeFactorPrimes_le_pointwiseEnvelope
  refine ⟨Aβ, Cπ, CV, CBV, S, X₀, hAβ, hCπ, hCV, hCBV, hS,
    hlogAβ, hw, ?_⟩
  intro L hSL
  have hL : 1 ≤ L := by omega
  filter_upwards [hrepresented L hSL,
    eventually_represented_add_goodRootWeight_le_budget_of_card L hL]
    with n hcard hbudget Q q r hQ hqLower hqUpper hQupper hr henvelope
  apply hbudget Q q r hQ hqLower hqUpper hQupper hr
  exact (hcard Q q r hQ hqLower hqUpper hQupper hr).trans henvelope

end

end Erdos48

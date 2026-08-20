/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos48.External.Erdos4.Base
import ErdosProblems.Erdos387.PrimeReciprocalBound

/-!
# A dyadic Rankin bound for the smooth residual exception

The elementary Euler-product majorant in `Erdos469` bounds the prime sum by
the corresponding sum over *all* integers.  That is adequate for a
polylogarithmic smoothness frontier, but loses too much when the frontier is
of Rankin size.  Here we retain the primality condition and decompose the
prime sum into binary logarithmic shells.  Chebyshev's bound then supplies a
harmonic factor in the shell index.

The estimates in this file are deliberately quantitative.  They will be
specialized with a small fixed coefficient in the definition of the
small-prime frontier.  This permits the unshifted smooth-number estimate to
replace the substantially deeper shifted Maier--Pomerance sieve estimate,
without changing the order of the final prime gap.
-/

open Filter Real Asymptotics
open scoped BigOperators Asymptotics

namespace Erdos4
namespace SmoothRankin

noncomputable section

open Erdos387

/-- The prime Rankin sum at natural frontier `y`. -/
noncomputable def primeRankinSum (delta : Real) (y : Nat) : Real :=
  ∑ p ∈ Nat.primesLE y, (p : Real) ^ (delta - 1)

/-- A Rankin weight is a positive power times a reciprocal. -/
theorem rankinWeight_eq_rpow_mul_inv {p : Nat} (hp : 0 < p)
    (delta : Real) :
    (p : Real) ^ (delta - 1) = (p : Real) ^ delta * (p : Real)⁻¹ := by
  rw [Real.rpow_sub_one (by exact_mod_cast hp.ne')]
  ring

/-- On the shell with binary logarithm `j`, the positive-power part of the
Rankin weight is bounded at the upper endpoint of the shell. -/
theorem rankinWeight_le_shellEndpoint {delta : Real} (hdelta : 0 ≤ delta)
    {y j p : Nat}
    (hp : p ∈ Erdos387.PrimeReciprocal.primeLogShell y j) :
    (p : Real) ^ (delta - 1) ≤
      ((2 : Real) ^ delta) ^ (j + 1) * (p : Real)⁻¹ := by
  have hpData := Finset.mem_filter.mp
    (show p ∈ (Nat.primesLE y).filter (fun q => Nat.log 2 q = j) by
      simpa [Erdos387.PrimeReciprocal.primeLogShell] using hp)
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hpData.1
  have hpPos : 0 < p := hpPrime.pos
  have hpUpperNat : p ≤ 2 ^ (j + 1) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) p
      |>.trans_le (by rw [hpData.2])).le
  have hpUpper : (p : Real) ≤ ((2 ^ (j + 1) : Nat) : Real) := by
    exact_mod_cast hpUpperNat
  rw [rankinWeight_eq_rpow_mul_inv hpPos]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by positivity))
  calc
    (p : Real) ^ delta ≤ (((2 ^ (j + 1) : Nat) : Real)) ^ delta :=
      Real.rpow_le_rpow (by positivity) hpUpper hdelta
    _ = ((2 : Real) ^ delta) ^ (j + 1) := by
      rw [show (((2 ^ (j + 1) : Nat) : Real)) = (2 : Real) ^ (j + 1) by
        norm_cast]
      exact (Real.rpow_pow_comm (by norm_num : (0 : Real) ≤ 2) delta
        (j + 1)).symm

/-- Chebyshev's prime-counting estimate bounds the Rankin mass of one
binary logarithmic shell. -/
theorem sum_rankinWeight_primeLogShell_le
    {C delta : Real} (hC : 0 < C) (hdelta : 0 ≤ delta)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    {y j : Nat} (hj : 1 ≤ j) :
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell y j,
        (p : Real) ^ (delta - 1)) ≤
      (2 * C / Real.log 2) *
        (((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹) := by
  calc
    (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell y j,
        (p : Real) ^ (delta - 1)) ≤
        ∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell y j,
          ((2 : Real) ^ delta) ^ (j + 1) * (p : Real)⁻¹ := by
      exact Finset.sum_le_sum fun p hp =>
        rankinWeight_le_shellEndpoint hdelta hp
    _ = ((2 : Real) ^ delta) ^ (j + 1) *
        (∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell y j,
          (1 : Real) / p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [one_div]
    _ ≤ ((2 : Real) ^ delta) ^ (j + 1) *
        ((2 * C / Real.log 2) * (j : Real)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · exact
          (Erdos387.PrimeReciprocal.sum_primeLogShell_le_primeCounting_div_pow
            y j).trans
            (Erdos387.PrimeReciprocal.primeCounting_pow_div_pow_le_harmonicSummand
              hC hcheb hj)
      · positivity
    _ = (2 * C / Real.log 2) *
        (((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹) := by
      ring

/-- The complete prime Rankin sum is controlled by a weighted harmonic sum
over its binary logarithmic shells. -/
theorem primeRankinSum_le_weightedHarmonic
    {C delta : Real} (hC : 0 < C) (hdelta : 0 ≤ delta)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    (y : Nat) :
    primeRankinSum delta y ≤
      (2 * C / Real.log 2) *
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 y),
          ((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹ := by
  classical
  rw [primeRankinSum, ← Erdos387.PrimeReciprocal.biUnion_primeLogShell y,
    Finset.sum_biUnion
      (Erdos387.PrimeReciprocal.pairwiseDisjoint_primeLogShell
        y (Nat.log 2 y))]
  calc
    (∑ j ∈ Finset.Icc 1 (Nat.log 2 y),
        ∑ p ∈ Erdos387.PrimeReciprocal.primeLogShell y j,
          (p : Real) ^ (delta - 1)) ≤
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 y),
          (2 * C / Real.log 2) *
            (((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_rankinWeight_primeLogShell_le hC hdelta hcheb
        (Finset.mem_Icc.mp hj).1
    _ = (2 * C / Real.log 2) *
        ∑ j ∈ Finset.Icc 1 (Nat.log 2 y),
          ((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹ := by
      rw [Finset.mul_sum]

/-! ## The weighted harmonic sum -/

/-- Split a geometrically weighted harmonic sum at an arbitrary integral
frontier.  The initial segment costs one ordinary harmonic number; on the
tail, the reciprocal denominator is frozen at the splitting point and the
remaining powers form a geometric series. -/
theorem weightedHarmonic_le_split
    {a : Real} (ha : 1 < a) (R J : Nat) :
    (∑ j ∈ Finset.Icc 1 J, a ^ (j + 1) * (j : Real)⁻¹) ≤
      a ^ (R + 1) * (harmonic R : Real) +
        (R + 1 : Real)⁻¹ * (a ^ (J + 2) / (a - 1)) := by
  classical
  let S := Finset.Icc 1 J
  let f : Nat → Real := fun j => a ^ (j + 1) * (j : Real)⁻¹
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha.le
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun j => j ≤ R) f
  change (∑ j ∈ S, f j) ≤ _
  rw [← hsplit]
  apply add_le_add
  · calc
      (∑ j ∈ S with j ≤ R, f j) ≤
          ∑ j ∈ S with j ≤ R,
            a ^ (R + 1) * (j : Real)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjR : j ≤ R := (Finset.mem_filter.mp hj).2
        dsimp only [f]
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_right₀ ha.le (by omega)
        · positivity
      _ ≤ ∑ j ∈ Finset.Icc 1 R,
          a ^ (R + 1) * (j : Real)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          have hjData := Finset.mem_filter.mp hj
          have hjS := Finset.mem_Icc.mp hjData.1
          exact Finset.mem_Icc.mpr ⟨hjS.1, hjData.2⟩
        · intro j _hj _hnot
          positivity
      _ = a ^ (R + 1) * (harmonic R : Real) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Finset.mul_sum]
  · calc
      (∑ j ∈ S with ¬j ≤ R, f j) ≤
          ∑ j ∈ S with ¬j ≤ R,
            (R + 1 : Real)⁻¹ * a ^ (j + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjR : R + 1 ≤ j := by
          have := (Finset.mem_filter.mp hj).2
          omega
        have hRpos : (0 : Real) < R + 1 := by positivity
        have hjpos : (0 : Real) < j := by
          exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ R) hjR)
        have hinv : (j : Real)⁻¹ ≤ (R + 1 : Real)⁻¹ := by
          exact (inv_le_inv₀ hjpos hRpos).2 (by exact_mod_cast hjR)
        dsimp only [f]
        calc
          a ^ (j + 1) * (j : Real)⁻¹ ≤
              a ^ (j + 1) * (R + 1 : Real)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (pow_nonneg ha0 _)
          _ = (R + 1 : Real)⁻¹ * a ^ (j + 1) := by ring
      _ ≤ ∑ j ∈ Finset.range (J + 1),
          (R + 1 : Real)⁻¹ * a ^ (j + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          have hjS := Finset.mem_Icc.mp
            (Finset.mem_filter.mp hj).1
          rw [Finset.mem_range]
          omega
        · intro j _hj _hnot
          positivity
      _ = (R + 1 : Real)⁻¹ *
          (a * ((a ^ (J + 1) - 1) / (a - 1))) := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          (∑ j ∈ Finset.range (J + 1), a ^ (j + 1)) =
              a * ∑ j ∈ Finset.range (J + 1), a ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [pow_succ']
          _ = a * ((a ^ (J + 1) - 1) / (a - 1)) := by
            rw [geom_sum_eq ha.ne' (J + 1)]
      _ ≤ (R + 1 : Real)⁻¹ * (a ^ (J + 2) / (a - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            a * ((a ^ (J + 1) - 1) / (a - 1)) ≤
                a * (a ^ (J + 1) / (a - 1)) := by
              apply mul_le_mul_of_nonneg_left
              · apply div_le_div_of_nonneg_right
                · linarith
                · exact (sub_pos.mpr ha).le
              · exact ha0
            _ = a ^ (J + 2) / (a - 1) := by
              rw [pow_succ']
              ring
        · positivity

/-- The denominator of the geometric tail has the expected first-order
lower bound. -/
theorem delta_mul_log_two_le_rpow_sub_one {delta : Real}
    (_hdelta : 0 ≤ delta) :
    delta * Real.log 2 ≤ (2 : Real) ^ delta - 1 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2)]
  have h := Real.add_one_le_exp (Real.log 2 * delta)
  nlinarith

/-- When the splitting point is within one multiplicative unit of
`1 / delta`, the abstract split has a particularly simple bound. -/
theorem weightedHarmonic_le_four_mul_harmonic_add
    {delta : Real} (hdelta : 0 < delta) (R J : Nat)
    (hRlower : 1 ≤ delta * (R + 1 : Real))
    (hRupper : delta * (R + 1 : Real) ≤ 2) :
    (∑ j ∈ Finset.Icc 1 J,
        ((2 : Real) ^ delta) ^ (j + 1) * (j : Real)⁻¹) ≤
      4 * (harmonic R : Real) +
        ((2 : Real) ^ delta) ^ (J + 2) / Real.log 2 := by
  let a : Real := (2 : Real) ^ delta
  have ha : 1 < a := by
    dsimp only [a]
    exact Real.one_lt_rpow (by norm_num) hdelta
  have hsplit := weightedHarmonic_le_split ha R J
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hfactor : delta * Real.log 2 ≤ a - 1 := by
    simpa only [a] using delta_mul_log_two_le_rpow_sub_one hdelta.le
  have hRpos : (0 : Real) < R + 1 := by positivity
  have hden : Real.log 2 ≤ (R + 1 : Real) * (a - 1) := by
    calc
      Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ (delta * (R + 1 : Real)) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right hRlower hlog2.le
      _ = (R + 1 : Real) * (delta * Real.log 2) := by ring
      _ ≤ (R + 1 : Real) * (a - 1) :=
        mul_le_mul_of_nonneg_left hfactor hRpos.le
  have haR : a ^ (R + 1) ≤ 4 := by
    calc
      a ^ (R + 1) = (2 : Real) ^ (delta * (R + 1 : Real)) := by
        dsimp only [a]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
        norm_num [Nat.cast_add, Nat.cast_one]
      _ ≤ (2 : Real) ^ (2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hRupper
      _ = 4 := by norm_num
  have hharmonic : 0 ≤ (harmonic R : Real) := by
    rw [harmonic_eq_sum_Icc]
    norm_cast
    positivity
  have hfirst : a ^ (R + 1) * (harmonic R : Real) ≤
      4 * (harmonic R : Real) :=
    mul_le_mul_of_nonneg_right haR hharmonic
  have htail :
      (R + 1 : Real)⁻¹ * (a ^ (J + 2) / (a - 1)) ≤
        a ^ (J + 2) / Real.log 2 := by
    have hapos : 0 < a - 1 := sub_pos.mpr ha
    calc
      (R + 1 : Real)⁻¹ * (a ^ (J + 2) / (a - 1)) =
          a ^ (J + 2) / ((R + 1 : Real) * (a - 1)) := by
        field_simp [hRpos.ne', hapos.ne']
      _ ≤ a ^ (J + 2) / Real.log 2 := by
        exact div_le_div_of_nonneg_left
          (pow_nonneg (le_trans (by norm_num) ha.le) _) hlog2 hden
  exact hsplit.trans (add_le_add hfirst htail)

/-! ## Return to the finite Euler product -/

/-- Keeping the prime support in the exponent gives a substantially sharper
Euler-product bound than replacing the primes by all positive integers. -/
theorem smoothRankinEulerProduct_le_exp_primeRankinSum
    {y : Nat} {delta : Real} (_hdelta_nonneg : 0 ≤ delta)
    (hdelta_le_half : delta ≤ 1 / 2) :
    Erdos469.smoothRankinEulerProduct delta y ≤
      Real.exp (Erdos469.rankinEulerConstant * primeRankinSum delta y) := by
  calc
    Erdos469.smoothRankinEulerProduct delta y ≤
        ∏ p ∈ (y + 1).primesBelow,
          Real.exp (Erdos469.rankinEulerConstant *
            (p : Real) ^ (delta - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr
          (Erdos469.prime_rankinWeight_le_half_reference hdelta_le_half
            (Nat.prime_of_mem_primesBelow hp) |>.trans
              (Real.rpow_lt_one_of_one_lt_of_neg
                (by norm_num) (by norm_num)).le))
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primesBelow hp
        exact Erdos469.inv_one_sub_le_exp_rankinEulerConstant_mul
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Erdos469.prime_rankinWeight_le_half_reference
            hdelta_le_half hpPrime)
    _ = Real.exp
        (∑ p ∈ (y + 1).primesBelow,
          Erdos469.rankinEulerConstant *
            (p : Real) ^ (delta - 1)) := by
      rw [Real.exp_sum]
    _ = Real.exp
        (Erdos469.rankinEulerConstant * primeRankinSum delta y) := by
      congr 1
      rw [← Finset.mul_sum]
      rfl

/-- Explicit prime-supported Rankin-sum bound after choosing a splitting
point comparable with `1 / delta`. -/
theorem primeRankinSum_le_four_mul_harmonic_add
    {C delta : Real} (hC : 0 < C) (hdelta : 0 < delta)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    (y R : Nat)
    (hRlower : 1 ≤ delta * (R + 1 : Real))
    (hRupper : delta * (R + 1 : Real) ≤ 2) :
    primeRankinSum delta y ≤
      (2 * C / Real.log 2) *
        (4 * (harmonic R : Real) +
          ((2 : Real) ^ delta) ^ (Nat.log 2 y + 2) / Real.log 2) := by
  exact (primeRankinSum_le_weightedHarmonic hC hdelta.le hcheb y).trans
    (mul_le_mul_of_nonneg_left
      (weightedHarmonic_le_four_mul_harmonic_add
        hdelta R (Nat.log 2 y) hRlower hRupper)
      (by positivity))

/-- The sharp finite Euler-product estimate in the form consumed by
Rankin's smooth-number inequality. -/
theorem smoothRankinEulerProduct_le_exp_dyadic
    {C delta : Real} (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta_le_half : delta ≤ 1 / 2)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    (y R : Nat)
    (hRlower : 1 ≤ delta * (R + 1 : Real))
    (hRupper : delta * (R + 1 : Real) ≤ 2) :
    Erdos469.smoothRankinEulerProduct delta y ≤
      Real.exp (Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (4 * (harmonic R : Real) +
            ((2 : Real) ^ delta) ^ (Nat.log 2 y + 2) /
              Real.log 2))) := by
  exact (smoothRankinEulerProduct_le_exp_primeRankinSum
    hdelta.le hdelta_le_half).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left
          (primeRankinSum_le_four_mul_harmonic_add
            hC hdelta hcheb y R hRlower hRupper)
          Erdos469.rankinEulerConstant_pos.le))

/-- Canonical integral splitting point for the weighted harmonic sum. -/
noncomputable def rankinSplitPoint (delta : Real) : Nat :=
  ⌈delta⁻¹⌉₊

theorem rankinSplitPoint_lower {delta : Real} (hdelta : 0 < delta) :
    1 ≤ delta * (rankinSplitPoint delta + 1 : Real) := by
  have hceil : delta⁻¹ ≤ (rankinSplitPoint delta : Real) := by
    exact Nat.le_ceil delta⁻¹
  have hceil' : delta⁻¹ ≤ (rankinSplitPoint delta + 1 : Real) := by
    exact hceil.trans (by norm_num)
  calc
    1 = delta * delta⁻¹ := by field_simp
    _ ≤ delta * (rankinSplitPoint delta + 1 : Real) :=
      mul_le_mul_of_nonneg_left hceil' hdelta.le

theorem rankinSplitPoint_upper {delta : Real} (hdelta : 0 < delta)
    (hdelta_half : delta ≤ 1 / 2) :
    delta * (rankinSplitPoint delta + 1 : Real) ≤ 2 := by
  have hinv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hceil : (rankinSplitPoint delta : Real) < delta⁻¹ + 1 := by
    exact Nat.ceil_lt_add_one hinv_nonneg
  have hcast : (rankinSplitPoint delta + 1 : Real) < delta⁻¹ + 2 := by
    linarith
  have hmul : delta * (rankinSplitPoint delta + 1 : Real) <
      delta * (delta⁻¹ + 2) :=
    mul_lt_mul_of_pos_left hcast hdelta
  have hid : delta * (delta⁻¹ + 2) = 1 + 2 * delta := by
    field_simp
  rw [hid] at hmul
  linarith

/-- The dyadic Euler-product estimate with its splitting point chosen
canonically. -/
theorem smoothRankinEulerProduct_le_exp_dyadic_canonical
    {C delta : Real} (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta_le_half : delta ≤ 1 / 2)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    (y : Nat) :
    Erdos469.smoothRankinEulerProduct delta y ≤
      Real.exp (Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (4 * (harmonic (rankinSplitPoint delta) : Real) +
            ((2 : Real) ^ delta) ^ (Nat.log 2 y + 2) /
              Real.log 2))) := by
  exact smoothRankinEulerProduct_le_exp_dyadic
    hC hdelta hdelta_le_half hcheb y (rankinSplitPoint delta)
    (rankinSplitPoint_lower hdelta)
    (rankinSplitPoint_upper hdelta hdelta_le_half)

/-- Fully explicit smooth-residual estimate with the sharp prime-supported
Euler exponent.  Unlike the earlier all-integer majorant, this remains useful
when `y` is of Rankin size. -/
theorem card_smoothResidualException_rankin_dyadic_le
    {C delta : Real} (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta_le_half : delta ≤ 1 / 2)
    (hcheb : ∀ t : Nat, 2 ≤ t →
      (Nat.primeCounting t : Real) ≤ C * t / Real.log t)
    {U y : Nat} (hU : 0 < U) :
    ((smoothResidualException U y).card : Real) ≤
      (U : Real) ^ (1 - delta) *
        Real.exp (Erdos469.rankinEulerConstant *
          ((2 * C / Real.log 2) *
            (4 * (harmonic (rankinSplitPoint delta) : Real) +
              ((2 : Real) ^ delta) ^ (Nat.log 2 y + 2) /
                Real.log 2))) := by
  exact (card_smoothResidualException_rankin_le hU hdelta
    (hdelta_le_half.trans_lt (by norm_num))).trans
      (mul_le_mul_of_nonneg_left
        (smoothRankinEulerProduct_le_exp_dyadic_canonical
          hC hdelta hdelta_le_half hcheb y)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end
end SmoothRankin
end Erdos4

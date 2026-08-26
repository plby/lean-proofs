/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos784.Erdos784Analytic
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Prime estimates for Erdős Problem 67

This file gives names local to the Erdős discrepancy development for the
prime-reciprocal estimates that occur in the analytic reduction.  There are
three inputs:

* the elementary Chebyshev--Abel upper estimate from `Erdos784`;
* the prime number theorem, used for a lower bound on a dyadic prime block;
* the bounded-error reciprocal-prime Mertens theorem proved for `Erdos697`.

The last part records a finite, uniform version of the exponentially weighted
tail estimate on the first multiplicative block.  This is deliberately stated
for finite sums, which is the form used by later truncation arguments.
-/

open Filter Finset Real
open scoped BigOperators Topology
open Asymptotics

namespace Erdos67b.PrimeEstimates

noncomputable section

/-- The primes in the half-open natural interval `(X,Y]`. -/
def primesInInterval (X Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X Y).filter Nat.Prime

@[simp] theorem mem_primesInInterval {X Y p : ℕ} :
    p ∈ primesInInterval X Y ↔ X < p ∧ p ≤ Y ∧ p.Prime := by
  simp [primesInInterval, and_assoc]

/-- The reciprocal mass of the primes in `(X,Y]`. -/
def reciprocalPrimeInterval (X Y : ℕ) : ℝ :=
  ∑ p ∈ primesInInterval X Y, (p : ℝ)⁻¹

/-- The reciprocal mass of all primes at most `X`. -/
abbrev primeReciprocals (X : ℕ) : ℝ :=
  Erdos784.Analytic.primeReciprocals X

theorem primeReciprocals_nonneg (X : ℕ) : 0 ≤ primeReciprocals X :=
  Erdos784.Analytic.primeReciprocals_nonneg X

/-- Splitting a prime prefix at `X` gives exactly the interval `(X,Y]`. -/
theorem reciprocalPrimeInterval_eq_sub {X Y : ℕ} (hXY : X ≤ Y) :
    reciprocalPrimeInterval X Y = primeReciprocals Y - primeReciprocals X := by
  classical
  have hsplit : Nat.primesLE Y = Nat.primesLE X ∪ primesInInterval X Y := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, mem_primesInInterval]
    constructor
    · intro hp
      by_cases hpX : p ≤ X
      · exact Or.inl ⟨hpX, hp.2⟩
      · exact Or.inr ⟨by omega, hp.1, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hXY, hp.2⟩
      · exact ⟨hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (Nat.primesLE X) (primesInInterval X Y) := by
    apply Finset.disjoint_left.mpr
    intro p hpX hpI
    have hpXle := (Nat.mem_primesLE.mp hpX).1
    have hpXlt := (mem_primesInInterval.mp hpI).1
    omega
  unfold reciprocalPrimeInterval primeReciprocals Erdos784.Analytic.primeReciprocals
  rw [hsplit, Finset.sum_union hdisj]
  ring

theorem reciprocalPrimeInterval_nonneg (X Y : ℕ) :
    0 ≤ reciprocalPrimeInterval X Y := by
  unfold reciprocalPrimeInterval
  exact Finset.sum_nonneg fun p _ => inv_nonneg.mpr (by positivity)

/-- Throwing away the primes at most `X` can only decrease a prime prefix. -/
theorem reciprocalPrimeInterval_le_primeReciprocals {X Y : ℕ} (hXY : X ≤ Y) :
    reciprocalPrimeInterval X Y ≤ primeReciprocals Y := by
  rw [reciprocalPrimeInterval_eq_sub hXY]
  exact sub_le_self _ (primeReciprocals_nonneg X)

/-- The `Erdos784` coefficient-explicit upper bound, re-exported in the
notation of this file. -/
theorem eventually_primeReciprocals_le_139 :
    ∀ᶠ X : ℕ in atTop,
      primeReciprocals X ≤
        (139 / 100 : ℝ) * Real.log (Real.log (X : ℝ)) := by
  simpa [Erdos784.Analytic.logLogNat] using
    Erdos784.Analytic.eventually_primeReciprocals_le_139

/-- A Chebyshev--Abel upper bound for every prime interval beyond one fixed
threshold. -/
theorem exists_reciprocalPrimeInterval_upper {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ X Y : ℕ, T ≤ (X : ℝ) → X ≤ Y →
      reciprocalPrimeInterval X Y ≤
        (Real.log 4 + δ) / Real.log (Y : ℝ) +
          (Real.log 4 + δ) *
            (Real.log (Real.log (Y : ℝ)) -
              Real.log (Real.log (X : ℝ))) := by
  obtain ⟨T, hT, hbound⟩ :=
    Erdos784.Analytic.primeReciprocals_sub_le_loglog hδ
  refine ⟨T, hT, ?_⟩
  intro X Y hTX hXY
  rw [reciprocalPrimeInterval_eq_sub hXY]
  exact hbound X Y hTX hXY

/-! ## A dyadic lower bound from the prime number theorem -/

/-- Primes in `(X,2X]`. -/
abbrev dyadicPrimes (X : ℕ) : Finset ℕ :=
  primesInInterval X (2 * X)

/-- Reciprocal prime mass in `(X,2X]`. -/
abbrev dyadicPrimeMass (X : ℕ) : ℝ :=
  reciprocalPrimeInterval X (2 * X)

/-- A fixed-relative-error form of the PNT. -/
theorem eventually_primeCounting_tenth_bounds :
    ∀ᶠ X : ℕ in atTop,
      (9 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
          (Nat.primeCounting X : ℝ) ∧
      (Nat.primeCounting X : ℝ) ≤
          (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmainPos : ∀ᶠ X : ℕ in atTop,
      0 ≤ (X : ℝ) / Real.log (X : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    positivity
  filter_upwards [herr, hmainPos] with X hX hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hX
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting X : ℝ) - (X : ℝ) / Real.log (X : ℝ)),
    neg_abs_le
      ((Nat.primeCounting X : ℝ) - (X : ℝ) / Real.log (X : ℝ))]

theorem eventually_log_two_mul_le_eleven_tenths :
    ∀ᶠ X : ℕ in atTop,
      Real.log (2 * X : ℝ) ≤
        (11 / 10 : ℝ) * Real.log (X : ℝ) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ X : ℕ in atTop,
      10 * Real.log 2 ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (10 * Real.log 2))
  filter_upwards [hevent, eventually_ge_atTop 1] with X hX hXone
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [show (2 * X : ℝ) = 2 * (X : ℝ) by norm_num,
    Real.log_mul (by norm_num) hXpos.ne']
  linarith

/-- PNT gives enough primes in `(X,2X]` for a reciprocal-mass lower bound. -/
theorem eventually_dyadicPrimes_card_lower :
    ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        (dyadicPrimes X).card := by
  have hpnt := eventually_primeCounting_tenth_bounds
  have htwoTop : Tendsto (fun X : ℕ ↦ 2 * X) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards with X
    simpa only [id_eq] using (show X ≤ 2 * X by omega)
  have hpntTwo := htwoTop.eventually eventually_primeCounting_tenth_bounds
  have hlog := eventually_log_two_mul_le_eleven_tenths
  have hlogPos : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  filter_upwards [hpnt, hpntTwo, hlog, hlogPos, eventually_ge_atTop 3]
      with X hX hXTwo hlog hlogPos hXthree
  norm_num [Nat.cast_mul] at hXTwo
  have hlogTwoPos : 0 < Real.log (2 * X : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hsubset : Nat.primesLE X ⊆ Nat.primesLE (2 * X) :=
    Nat.primesLE_mono (by omega)
  have hcard : (dyadicPrimes X).card =
      Nat.primeCounting (2 * X) - Nat.primeCounting X := by
    have hset : dyadicPrimes X = Nat.primesLE (2 * X) \ Nat.primesLE X := by
      ext p
      simp only [mem_primesInInterval, Finset.mem_sdiff, Nat.mem_primesLE]
      aesop
    rw [hset, Finset.card_sdiff_of_subset hsubset,
      Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
  have hpiMono : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) := by
    simpa [← Nat.primesLE_card_eq_primeCounting] using
      Finset.card_le_card hsubset
  have hcardR : ((dyadicPrimes X).card : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) -
        (Nat.primeCounting X : ℝ) := by
    rw [hcard, Nat.cast_sub hpiMono]
  rw [hcardR]
  have hratio :
      (X : ℝ) / Real.log (X : ℝ) ≤
        (11 / 10 : ℝ) *
          ((X : ℝ) / Real.log (2 * X : ℝ)) := by
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    have hmul :
        (X : ℝ) * Real.log (2 * X : ℝ) ≤
          ((11 / 10 : ℝ) * (X : ℝ)) * Real.log (X : ℝ) := by
      nlinarith [mul_nonneg hXnonneg (sub_nonneg.mpr hlog)]
    calc
      (X : ℝ) / Real.log (X : ℝ) ≤
          ((11 / 10 : ℝ) * (X : ℝ)) /
            Real.log (2 * X : ℝ) :=
        (div_le_div_iff₀ hlogPos hlogTwoPos).2 hmul
      _ = (11 / 10 : ℝ) *
          ((X : ℝ) / Real.log (2 * X : ℝ)) := by ring
  have hmainNonneg : 0 ≤ (X : ℝ) / Real.log (X : ℝ) := by positivity
  calc
    (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))
        ≤ (59 / 110 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hmainNonneg
    _ ≤ (9 / 10 : ℝ) *
            ((2 * X : ℝ) / Real.log (2 * X : ℝ)) -
          (11 / 10 : ℝ) *
            ((X : ℝ) / Real.log (X : ℝ)) := by
      have hscaled := mul_le_mul_of_nonneg_left hratio
        (show (0 : ℝ) ≤ 18 / 11 by norm_num)
      calc
        (59 / 110 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) =
            (18 / 11 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) -
              (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by ring
        _ ≤ (18 / 10 : ℝ) *
              ((X : ℝ) / Real.log (2 * X : ℝ)) -
              (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
                exact sub_le_sub_right (by nlinarith) _
        _ = (9 / 10 : ℝ) *
              ((2 * X : ℝ) / Real.log (2 * X : ℝ)) -
              (11 / 10 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
                norm_num [Nat.cast_mul]
                ring
    _ ≤ (Nat.primeCounting (2 * X) : ℝ) -
          (Nat.primeCounting X : ℝ) := sub_le_sub hXTwo.1 hX.2

/-- The dyadic reciprocal mass is eventually at least
`1 / (4 log X)`. -/
theorem eventually_dyadicPrimeMass_lower :
    ∀ᶠ X : ℕ in atTop,
      (1 / 4 : ℝ) / Real.log (X : ℝ) ≤ dyadicPrimeMass X := by
  filter_upwards [eventually_dyadicPrimes_card_lower,
      eventually_ge_atTop 3] with X hcard hXthree
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlower :
      ((dyadicPrimes X).card : ℝ) * (1 / (2 * X : ℝ)) ≤
        dyadicPrimeMass X := by
    unfold dyadicPrimeMass reciprocalPrimeInterval
    calc
      ((dyadicPrimes X).card : ℝ) * (1 / (2 * X : ℝ)) =
          ∑ p ∈ dyadicPrimes X, 1 / (2 * X : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ dyadicPrimes X, (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPos : (0 : ℝ) < p := by
          exact_mod_cast (mem_primesInInterval.mp hp).2.2.pos
        simpa only [one_div] using one_div_le_one_div_of_le hpPos
          (by exact_mod_cast (mem_primesInInterval.mp hp).2.1)
  calc
    (1 / 4 : ℝ) / Real.log (X : ℝ) =
        ((1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) *
          (1 / (2 * X : ℝ)) := by field_simp; ring
    _ ≤ ((dyadicPrimes X).card : ℝ) * (1 / (2 * X : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ dyadicPrimeMass X := hlower

/-! ## Bounded-error Mertens estimates and a finite weighted tail -/

/-- One nonnegative absolute constant in the reciprocal-prime Mertens
theorem. -/
def mertensBound : ℝ :=
  Classical.choose
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem mertensBound_nonneg : 0 ≤ mertensBound :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).1

theorem primeReciprocals_eq_primeHarmonic (X : ℕ) :
    primeReciprocals X = Erdos697.PrimeHarmonic.sum X := by
  unfold primeReciprocals Erdos784.Analytic.primeReciprocals
    Erdos697.PrimeHarmonic.sum
  simp only [one_div]

theorem abs_primeReciprocals_sub_log_log_le {X : ℕ} (hX : 2 ≤ X) :
    |primeReciprocals X - Real.log (Real.log (X : ℝ))| ≤ mertensBound := by
  rw [primeReciprocals_eq_primeHarmonic]
  exact (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).2 X hX

/-- Uniform reciprocal-prime interval bound. -/
theorem reciprocalPrimeInterval_le_log_log_sub_add
    {X Y : ℕ} (hX : 2 ≤ X) (hXY : X ≤ Y) :
    reciprocalPrimeInterval X Y ≤
      Real.log (Real.log (Y : ℝ)) -
        Real.log (Real.log (X : ℝ)) + 2 * mertensBound := by
  rw [reciprocalPrimeInterval_eq_sub hXY]
  have hY : 2 ≤ Y := hX.trans hXY
  have hUpper := abs_primeReciprocals_sub_log_log_le hY
  have hLower := abs_primeReciprocals_sub_log_log_le hX
  rw [abs_le] at hUpper hLower
  linarith

/-- The finite exponentially weighted prime tail
`sum_{X < p ≤ Y} p^(-1-1/log X)`. -/
def expWeightedPrimeTail (X Y : ℕ) : ℝ :=
  ∑ p ∈ primesInInterval X Y,
    (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹)

/-- The exponential weight only decreases each reciprocal-prime term. -/
theorem expWeightedPrimeTail_le_reciprocalPrimeInterval
    {X Y : ℕ} (hX : 2 ≤ X) :
    expWeightedPrimeTail X Y ≤ reciprocalPrimeInterval X Y := by
  unfold expWeightedPrimeTail reciprocalPrimeInterval
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := (mem_primesInInterval.mp hp).2.2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hweight :
      (p : ℝ) ^ (-(Real.log (X : ℝ))⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpOne
      (neg_nonpos.mpr (inv_nonneg.mpr hlog.le))
  rw [show -(1 : ℝ) - (Real.log (X : ℝ))⁻¹ =
      (-1 : ℝ) + (-(Real.log (X : ℝ))⁻¹) by ring,
    Real.rpow_add hpPos, Real.rpow_neg_one]
  simpa only [one_div, mul_one] using
    mul_le_mul_of_nonneg_left hweight (inv_nonneg.mpr hpPos.le)

/-- On the first square block `(X,X^2]`, the exponentially weighted prime
tail is bounded by an absolute constant, uniformly in both finite cutoffs. -/
theorem expWeightedPrimeTail_le_log_two_add
    {X Y : ℕ} (hX : 2 ≤ X) (hXY : X ≤ Y) (hY : Y ≤ X ^ 2) :
    expWeightedPrimeTail X Y ≤ Real.log 2 + 2 * mertensBound := by
  have hmass := reciprocalPrimeInterval_le_log_log_sub_add hX hXY
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hXsqpos : (0 : ℝ) < (X ^ 2 : ℕ) := by positivity
  have hlogYle : Real.log (Y : ℝ) ≤ Real.log ((X ^ 2 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hYpos)
      (by simpa only [Set.mem_Ioi] using hXsqpos)
      (by exact_mod_cast hY)
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogXsqpos : 0 < Real.log ((X ^ 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X ^ 2 by omega))
  have hloglogYle :
      Real.log (Real.log (Y : ℝ)) ≤
        Real.log (Real.log ((X ^ 2 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hlogYpos)
      (by simpa only [Set.mem_Ioi] using hlogXsqpos)
      hlogYle
  have hsquare :
      Real.log (Real.log ((X ^ 2 : ℕ) : ℝ)) -
          Real.log (Real.log (X : ℝ)) = Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    rw [Real.log_mul (by norm_num) hlogX.ne']
    ring
  calc
    expWeightedPrimeTail X Y ≤ reciprocalPrimeInterval X Y :=
      expWeightedPrimeTail_le_reciprocalPrimeInterval hX
    _ ≤ Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (X : ℝ)) + 2 * mertensBound := hmass
    _ ≤ Real.log (Real.log ((X ^ 2 : ℕ) : ℝ)) -
          Real.log (Real.log (X : ℝ)) + 2 * mertensBound := by linarith
    _ = Real.log 2 + 2 * mertensBound := by rw [hsquare]

end

end Erdos67b.PrimeEstimates

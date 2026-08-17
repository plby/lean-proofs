/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.ActiveLcm
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos297.PrimeIntervals

/-!
# Numerical supply estimates for the repaired auxiliary-prime argument

This file keeps the slowly growing cutoffs used by the repaired `p'`
pigeonhole argument separate from the finite combinatorics in
`AuxiliarySupply`.  In particular, it may be imported by that file without
creating an import cycle.
-/

namespace Erdos297.SupplyNumerics

open Filter Finset Real
open scoped ArithmeticFunction.Omega BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos297.ActiveLcm Erdos297.GoodFactorization Erdos297.PrimeIntervals
open Erdos285.PrimePowers

/-- Upper bound for the number of denominators in a bad minor-arc fiber. -/
def minorBadThreshold (N : ℕ) : ℕ :=
  ⌊100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
      (KSafe N : ℝ) ^ 2⌋₊

/-- The ceiling version used as the exact minor-arc threshold. -/
def minorThreshold (N : ℕ) : ℕ :=
  ⌈100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
      (KSafe N : ℝ) ^ 2⌉₊

/-- Prime cutoff used in the repaired averaging over `p'`. -/
def smallPrimeCutoff (N : ℕ) : ℕ :=
  ⌈(10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
      logLogScale N ^ 4 / logScale N⌉₊

/-- Permitted size of the exceptional `A_{qp'}` fiber. -/
def fiberBudget (N : ℕ) : ℕ :=
  ⌊logScale N / (1000 * logLogScale N ^ 2)⌋₊

/-- The acyclic copy of `AuxiliarySupply.smallPrimeCandidates`. -/
def smallPrimeCandidates (X q : ℕ) : Finset ℕ :=
  (Icc 2 X).filter fun p ↦ p.Prime ∧ p.Coprime q

@[simp] lemma mem_smallPrimeCandidates {X q p : ℕ} :
    p ∈ smallPrimeCandidates X q ↔
      2 ≤ p ∧ p ≤ X ∧ p.Prime ∧ p.Coprime q := by
  simp [smallPrimeCandidates, and_assoc]

/-- Excluding the single prime below a prime power costs at most one prime. -/
lemma primeCounting_le_smallPrimeCandidates_card_add_one
    {X q : ℕ} (hq : IsPrimePow q) :
    Nat.primeCounting X ≤ (smallPrimeCandidates X q).card + 1 := by
  obtain ⟨a, k, ha, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have hq0 : a ^ k ≠ 0 := pow_ne_zero _ ha.ne_zero
  have hpf : (a ^ k).primeFactors = {a} :=
    Nat.primeFactors_prime_pow hk.ne' ha
  have hsub : Nat.primesLE X \ (a ^ k).primeFactors ⊆
      smallPrimeCandidates X (a ^ k) := by
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpX, hpnot⟩
    have hpdata := Nat.mem_primesLE.mp hpX
    have hpnotdvd : ¬p ∣ a ^ k := by
      intro hpdvd
      exact hpnot (Nat.mem_primeFactors.mpr ⟨hpdata.2, hpdvd, hq0⟩)
    exact mem_smallPrimeCandidates.mpr
      ⟨hpdata.2.two_le, hpdata.1, hpdata.2,
        hpdata.2.coprime_iff_not_dvd.mpr hpnotdvd⟩
  have hcover : Nat.primesLE X ⊆
      (Nat.primesLE X \ (a ^ k).primeFactors) ∪ (a ^ k).primeFactors := by
    intro p hp
    by_cases hpq : p ∈ (a ^ k).primeFactors
    · exact Finset.mem_union_right _ hpq
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, hpq⟩)
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    (Nat.primesLE X).card ≤
        (Nat.primesLE X \ (a ^ k).primeFactors).card +
          (a ^ k).primeFactors.card :=
      (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    _ ≤ (smallPrimeCandidates X (a ^ k)).card +
          (a ^ k).primeFactors.card := by
      gcongr
    _ = (smallPrimeCandidates X (a ^ k)).card + 1 := by simp [hpf]

lemma eventually_floor_logScale_le_minorBadThreshold :
    ∀ᶠ N : ℕ in atTop, ⌊logScale N⌋₊ ≤ minorBadThreshold N := by
  filter_upwards [eventually_pos_scales, eventually_nat_KSafe_lower,
      eventually_nat_safe_scale_chain] with N hpos hKlower hchain
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  have hKN : (KSafe N : ℝ) ≤ (N : ℝ) := by
    calc
      (KSafe N : ℝ) ≤ (M N : ℝ) := hchain.2.1
      _ ≤ (N : ℝ) / 10 := hchain.2.2
      _ ≤ (N : ℝ) := by linarith
  have hKsq : (KSafe N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
    pow_le_pow_left₀ hK.le hKN 2
  have hcoeff : (1 : ℝ) ≤ 100 * logLogScale N ^ 2 := by
    nlinarith [sq_nonneg (logLogScale N - 1)]
  have hnum : logScale N * (KSafe N : ℝ) ^ 2 ≤
      100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 := by
    calc
      logScale N * (KSafe N : ℝ) ^ 2 ≤
          logScale N * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hKsq hL.le
      _ ≤ (logScale N * (N : ℝ) ^ 2) *
          (100 * logLogScale N ^ 2) :=
        le_mul_of_one_le_right (mul_nonneg hL.le (sq_nonneg _)) hcoeff
      _ = 100 * (N : ℝ) ^ 2 * logScale N *
          logLogScale N ^ 2 := by ring
  have hreal : logScale N ≤
      100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
        (KSafe N : ℝ) ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hK)).2 hnum
  exact Nat.floor_mono hreal

lemma minorBadThreshold_tendsto_atTop :
    Tendsto minorBadThreshold atTop atTop := by
  exact tendsto_atTop_mono' atTop
    eventually_floor_logScale_le_minorBadThreshold
    (tendsto_nat_floor_atTop.comp tendsto_logScale)

lemma eventually_floor_logLogScale_le_smallPrimeCutoff :
    ∀ᶠ N : ℕ in atTop, ⌊logLogScale N⌋₊ ≤ smallPrimeCutoff N := by
  filter_upwards [eventually_floor_logScale_le_minorBadThreshold,
      eventually_pos_scales, tendsto_logScale.eventually_ge_atTop 2]
      with N hT hpos hLtwo
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hThalf : logScale N / 2 ≤ (minorBadThreshold N : ℝ) := by
    exact (half_le_floor hLtwo).trans (by exact_mod_cast hT)
  let y : ℝ := (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
      logLogScale N ^ 4 / logScale N
  have hy : logLogScale N ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hL]
    have hLLpow : logLogScale N ≤ logLogScale N ^ 4 := by
      simpa using pow_le_pow_right₀ hLLone.le (by norm_num : 1 ≤ 4)
    calc
      logLogScale N * logScale N ≤
          logLogScale N * (2 * (minorBadThreshold N : ℝ)) := by
        gcongr
        linarith
      _ ≤ (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
          logLogScale N ^ 4 := by
        have hTnonneg : 0 ≤ (minorBadThreshold N : ℝ) := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hLLpow hTnonneg
        norm_num at hmul ⊢
        nlinarith
  have hfloor : (⌊logLogScale N⌋₊ : ℝ) ≤ logLogScale N :=
    Nat.floor_le hLL.le
  have hceil : y ≤ (smallPrimeCutoff N : ℝ) := by
    exact Nat.le_ceil y
  exact_mod_cast hfloor.trans (hy.trans hceil)

lemma smallPrimeCutoff_tendsto_atTop :
    Tendsto smallPrimeCutoff atTop atTop := by
  exact tendsto_atTop_mono' atTop
    eventually_floor_logLogScale_le_smallPrimeCutoff
    (tendsto_nat_floor_atTop.comp tendsto_logLogScale)

lemma eventually_minorBadThreshold_cast_upper :
    ∀ᶠ N : ℕ in atTop,
      (minorBadThreshold N : ℝ) ≤
        100 * logScale N ^ 21 * logLogScale N ^ 2 := by
  filter_upwards [eventually_pos_scales, eventually_nat_KSafe_lower]
      with N hpos hKlower
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  have hNle : (N : ℝ) ≤ (KSafe N : ℝ) * logScale N ^ 10 := by
    exact (div_le_iff₀ (pow_pos hL 10)).mp hKlower
  have hsq : (N : ℝ) ^ 2 ≤
      ((KSafe N : ℝ) * logScale N ^ 10) ^ 2 :=
    pow_le_pow_left₀ hN.le hNle 2
  have hnum : 100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 ≤
      (100 * logScale N ^ 21 * logLogScale N ^ 2) *
        (KSafe N : ℝ) ^ 2 := by
    calc
      100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 ≤
          100 * (((KSafe N : ℝ) * logScale N ^ 10) ^ 2) *
            logScale N * logLogScale N ^ 2 := by gcongr
      _ = (100 * logScale N ^ 21 * logLogScale N ^ 2) *
          (KSafe N : ℝ) ^ 2 := by ring
  have hreal :
      100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
          (KSafe N : ℝ) ^ 2 ≤
        100 * logScale N ^ 21 * logLogScale N ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hK)).2 hnum
  exact (Nat.floor_le (by positivity)).trans hreal

lemma eventually_smallPrimeCutoff_cast_le_logScale_pow_28 :
    ∀ᶠ N : ℕ in atTop,
      (smallPrimeCutoff N : ℝ) ≤ logScale N ^ 28 := by
  filter_upwards [eventually_minorBadThreshold_cast_upper,
      eventually_logLogScale_le_logScale, eventually_pos_scales,
      tendsto_logScale.eventually
        (eventually_ge_atTop (Real.sqrt (2 * (10 : ℝ) ^ 8)))]
      with N hT hLLle hpos hLlarge
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hlargeSq : 2 * (10 : ℝ) ^ 8 ≤ logScale N ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (2 * (10 : ℝ) ^ 8) := Real.sqrt_nonneg _
    have hsquare := mul_self_le_mul_self hsqrt0 hLlarge
    have hsqrteq : Real.sqrt (2 * (10 : ℝ) ^ 8) ^ 2 =
        2 * (10 : ℝ) ^ 8 := Real.sq_sqrt (by norm_num)
    nlinarith [hsqrteq]
  let y : ℝ := (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
      logLogScale N ^ 4 / logScale N
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy : y ≤ (10 : ℝ) ^ 8 * logScale N ^ 20 *
      logLogScale N ^ 6 := by
    dsimp [y]
    rw [div_le_iff₀ hL]
    calc
      (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
          logLogScale N ^ 4 ≤
          (10 : ℝ) ^ 6 *
            (100 * logScale N ^ 21 * logLogScale N ^ 2) *
              logLogScale N ^ 4 := by gcongr
      _ = ((10 : ℝ) ^ 8 * logScale N ^ 20 *
          logLogScale N ^ 6) * logScale N := by ring
  have hLLpow : logLogScale N ^ 6 ≤ logScale N ^ 6 :=
    pow_le_pow_left₀ hLL.le hLLle 6
  have hy' : y ≤ (10 : ℝ) ^ 8 * logScale N ^ 26 := by
    calc
      y ≤ (10 : ℝ) ^ 8 * logScale N ^ 20 *
          logLogScale N ^ 6 := hy
      _ ≤ (10 : ℝ) ^ 8 * logScale N ^ 20 *
          logScale N ^ 6 := by gcongr
      _ = (10 : ℝ) ^ 8 * logScale N ^ 26 := by ring
  have hceil : (smallPrimeCutoff N : ℝ) ≤ y + 1 :=
    (Nat.ceil_lt_add_one hy0).le
  calc
    (smallPrimeCutoff N : ℝ) ≤ y + 1 := hceil
    _ ≤ (10 : ℝ) ^ 8 * logScale N ^ 26 + 1 := by linarith
    _ ≤ 2 * (10 : ℝ) ^ 8 * logScale N ^ 26 := by
      have hpow : (1 : ℝ) ≤ logScale N ^ 26 := by
        simpa using pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1)
          hLone.le 26
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (10 : ℝ) ^ 8 by positivity)
        (zero_le_one.trans hpow)]
    _ ≤ logScale N ^ 2 * logScale N ^ 26 := by gcongr
    _ = logScale N ^ 28 := by ring

lemma eventually_log_smallPrimeCutoff_le_twentyEight_mul_logLogScale :
    ∀ᶠ N : ℕ in atTop,
      Real.log (smallPrimeCutoff N : ℝ) ≤
        28 * logLogScale N := by
  filter_upwards [eventually_smallPrimeCutoff_cast_le_logScale_pow_28,
      eventually_pos_scales,
      smallPrimeCutoff_tendsto_atTop.eventually (eventually_gt_atTop 0)]
      with N hX hpos hXpos
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hXposR : 0 < (smallPrimeCutoff N : ℝ) := by exact_mod_cast hXpos
  calc
    Real.log (smallPrimeCutoff N : ℝ) ≤
        Real.log (logScale N ^ 28) :=
      Real.strictMonoOn_log.monotoneOn hXposR (pow_pos hL 28) hX
    _ = 28 * logLogScale N := by
      rw [Real.log_pow]
      rfl

/-- PNT lower bound after removing the one prime below `q`. -/
lemma eventually_smallPrimeCandidates_card_lower :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, IsPrimePow q →
      (smallPrimeCutoff N : ℝ) /
          (3 * Real.log (smallPrimeCutoff N : ℝ)) ≤
        ((smallPrimeCandidates (smallPrimeCutoff N) q).card : ℝ) := by
  have hcast : Tendsto (fun N : ℕ ↦ (smallPrimeCutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp smallPrimeCutoff_tendsto_atTop
  have hratio : Tendsto
      (fun N : ℕ ↦ (smallPrimeCutoff N : ℝ) /
        Real.log (smallPrimeCutoff N : ℝ)) atTop atTop :=
    x_log_x_atTop.comp hcast
  have hpnt := smallPrimeCutoff_tendsto_atTop.eventually
    eventually_half_mul_div_log_le_primeCounting
  filter_upwards [hpnt, hratio.eventually_ge_atTop 6,
      smallPrimeCutoff_tendsto_atTop.eventually (eventually_gt_atTop 1)]
      with N hpntN hratioN hXone
  intro q hq
  let X := smallPrimeCutoff N
  let C := (smallPrimeCandidates X q).card
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hXone)
  have hpiC : Nat.primeCounting X ≤ C + 1 :=
    primeCounting_le_smallPrimeCandidates_card_add_one hq
  have hpiCR : (Nat.primeCounting X : ℝ) ≤ (C : ℝ) + 1 := by
    exact_mod_cast hpiC
  have hpntR : (X : ℝ) / (2 * Real.log (X : ℝ)) ≤
      (Nat.primeCounting X : ℝ) := by simpa [X] using hpntN
  have hratioR : (6 : ℝ) ≤ (X : ℝ) / Real.log (X : ℝ) := by
    simpa [X] using hratioN
  have hhalf : (X : ℝ) / (2 * Real.log (X : ℝ)) =
      ((X : ℝ) / Real.log (X : ℝ)) / 2 := by ring
  have hthird : (X : ℝ) / (3 * Real.log (X : ℝ)) =
      ((X : ℝ) / Real.log (X : ℝ)) / 3 := by ring
  change (X : ℝ) / (3 * Real.log (X : ℝ)) ≤ (C : ℝ)
  rw [hthird]
  rw [hhalf] at hpntR
  nlinarith

lemma eventually_minorThreshold_sub_one_le_minorBadThreshold :
    ∀ᶠ N : ℕ in atTop,
      minorThreshold N - 1 ≤ minorBadThreshold N := by
  filter_upwards [eventually_pos_scales,
      eventually_nat_KSafe_lower] with N hpos hKlower
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  let y : ℝ := 100 * (N : ℝ) ^ 2 * logScale N *
      logLogScale N ^ 2 / (KSafe N : ℝ) ^ 2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hround : ⌈y⌉₊ ≤ ⌊y⌋₊ + 1 := Nat.ceil_le_floor_add_one y
  change ⌈y⌉₊ - 1 ≤ ⌊y⌋₊
  omega

/-- The repaired `p'` supply, in a slightly stronger form than needed:
the left side uses `T`, not `T - 1`. -/
theorem eventually_smallPrimeCandidates_budget :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, IsPrimePow q →
      factorBound N * minorBadThreshold N <
        (smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
  filter_upwards [eventually_smallPrimeCandidates_card_lower,
      eventually_log_smallPrimeCutoff_le_twentyEight_mul_logLogScale,
      eventually_pos_scales,
      minorBadThreshold_tendsto_atTop.eventually (eventually_gt_atTop 0),
      smallPrimeCutoff_tendsto_atTop.eventually (eventually_gt_atTop 1)]
      with N hcand hlogX hpos hTpos hXone
  intro q hq
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  let L := logScale N
  let LL := logLogScale N
  let T := minorBadThreshold N
  let X := smallPrimeCutoff N
  let C := (smallPrimeCandidates X q).card
  let B := fiberBudget N
  have hL : 0 < L := by dsimp [L]; exact zero_lt_one.trans hLone
  have hLL : 0 < LL := by dsimp [LL]; exact zero_lt_one.trans hLLone
  have hT : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have hX : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hXone)
  have hfactor : (factorBound N : ℝ) ≤ 10 * LL := by
    dsimp [factorBound, LL, logLogScale, logScale]
    exact Nat.floor_le (by positivity)
  have hcutoff : (10 : ℝ) ^ 6 * (T : ℝ) * LL ^ 4 / L ≤ (X : ℝ) := by
    dsimp [X, smallPrimeCutoff, T, L, LL]
    exact Nat.le_ceil _
  have hbudgetR : L / (1000 * LL ^ 2) < ((B + 1 : ℕ) : ℝ) := by
    dsimp [B, fiberBudget, L, LL]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one
        (logScale N / (1000 * logLogScale N ^ 2) : ℝ))
  have hcand' : (X : ℝ) / (84 * LL) ≤ (C : ℝ) := by
    have hc := hcand q hq
    dsimp [X, C] at hc ⊢
    have hlog := hlogX
    have hden1 : 0 < 84 * logLogScale N := by positivity
    have hden2 : 0 < 3 * Real.log (smallPrimeCutoff N : ℝ) := by positivity
    calc
      (smallPrimeCutoff N : ℝ) / (84 * logLogScale N) ≤
          (smallPrimeCutoff N : ℝ) /
            (3 * Real.log (smallPrimeCutoff N : ℝ)) := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden2
        nlinarith
      _ ≤ ((smallPrimeCandidates (smallPrimeCutoff N) q).card : ℝ) := hc
  have hcpos : 0 < (C : ℝ) :=
    (div_pos hX (mul_pos (by norm_num) hLL)).trans_le hcand'
  have hmain : 10 * (T : ℝ) * LL <
      (C : ℝ) * ((B + 1 : ℕ) : ℝ) := by
    calc
      10 * (T : ℝ) * LL < (250 / 21 : ℝ) * (T : ℝ) * LL := by
        nlinarith [mul_pos hT hLL]
      _ = (((10 : ℝ) ^ 6 * (T : ℝ) * LL ^ 4 / L) /
            (84 * LL)) * (L / (1000 * LL ^ 2)) := by
        field_simp
        ring
      _ ≤ ((X : ℝ) / (84 * LL)) *
            (L / (1000 * LL ^ 2)) := by
        gcongr
      _ ≤ (C : ℝ) * (L / (1000 * LL ^ 2)) := by
        gcongr
      _ < (C : ℝ) * ((B + 1 : ℕ) : ℝ) := by
        exact mul_lt_mul_of_pos_left hbudgetR hcpos
  have hleft : ((factorBound N * T : ℕ) : ℝ) ≤
      10 * (T : ℝ) * LL := by
    push_cast
    calc
      (factorBound N : ℝ) * (T : ℝ) ≤
          (10 * LL) * (T : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg T)
      _ = 10 * (T : ℝ) * LL := by ring
  exact_mod_cast hleft.trans_lt hmain

/-- Requested floor-threshold form. -/
theorem eventually_smallPrimeCandidates_budget_sub_one :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
      q ∈ activePrimePowers (goodDenominators N (M N) (S N)) →
      factorBound N * (minorBadThreshold N - 1) <
        (smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
  filter_upwards [eventually_smallPrimeCandidates_budget] with N hN
  intro q hq
  have hqpp := activePrimePower_isPrimePow hq
  exact (Nat.mul_le_mul_left (factorBound N)
    (Nat.sub_le _ _)).trans_lt (hN q hqpp)

/-- Exact ceiling-threshold form consumed by the minor-arc code. -/
theorem eventually_minorThreshold_smallPrimeCandidates_budget :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
      q ∈ activePrimePowers (goodDenominators N (M N) (S N)) →
      factorBound N * (minorThreshold N - 1) <
        (smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
  filter_upwards [eventually_smallPrimeCandidates_budget,
      eventually_minorThreshold_sub_one_le_minorBadThreshold] with N hN hround
  intro q hq
  have hqpp := activePrimePower_isPrimePow hq
  exact (Nat.mul_le_mul_left (factorBound N) hround).trans_lt (hN q hqpp)

/-- The common logarithmic band has ample room after paying both the bad
fiber incidence cost and the at-most-three-prime extension cost. -/
theorem eventually_auxiliaryPrimes_band_budget :
    ∀ᶠ N : ℕ in atTop,
      10 * (factorBound N * fiberBudget N + (exponentBound N + 3)) ≤
        (auxiliaryPrimes N).card := by
  filter_upwards [eventually_five_log_div_loglog_le_card_auxiliaryPrimes,
      eventually_logLog_pow_five_le_logScale 1000 (by norm_num),
      eventually_pos_scales] with N haux hscale hpos
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  let L := logScale N
  let LL := logLogScale N
  let F := factorBound N
  let E := exponentBound N
  let B := fiberBudget N
  have hL : 0 < L := by dsimp [L]; exact zero_lt_one.trans hLone
  have hLL : 0 < LL := by dsimp [LL]; exact zero_lt_one.trans hLLone
  have hF : (F : ℝ) ≤ 10 * LL := by
    dsimp [F, factorBound, LL, logLogScale, logScale]
    exact Nat.floor_le (by positivity)
  have hE : (E : ℝ) ≤ 5 * LL := by
    dsimp [E, exponentBound, LL, logLogScale, logScale]
    exact Nat.floor_le (by positivity)
  have hB : (B : ℝ) ≤ L / (1000 * LL ^ 2) := by
    dsimp [B, fiberBudget, L, LL]
    exact Nat.floor_le (by positivity)
  have hFB : ((F * B : ℕ) : ℝ) ≤ L / (100 * LL) := by
    push_cast
    calc
      (F : ℝ) * B ≤ (10 * LL) * (L / (1000 * LL ^ 2)) := by
        gcongr
      _ = L / (100 * LL) := by field_simp; ring
  have hLLpow : LL ^ 2 ≤ LL ^ 5 := by
    simpa using pow_le_pow_right₀ hLLone.le (by norm_num : 2 ≤ 5)
  have hscale' : 1000 * LL ^ 2 ≤ L := by
    calc
      1000 * LL ^ 2 ≤ 1000 * LL ^ 5 := by gcongr
      _ ≤ L := by simpa [L, LL] using hscale
  have htail : 80 * LL ≤ L / (10 * LL) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hLL)]
    nlinarith
  have hleft :
      ((10 * (F * B + (E + 3)) : ℕ) : ℝ) ≤ 5 * L / LL := by
    push_cast
    have hEthree : (E : ℝ) + 3 ≤ 8 * LL := by nlinarith
    have hFBR : (F : ℝ) * (B : ℝ) ≤ L / (100 * LL) := by
      simpa using hFB
    calc
      10 * ((F : ℝ) * B + ((E : ℝ) + 3)) ≤
          10 * (L / (100 * LL) + 8 * LL) := by nlinarith
      _ = L / (10 * LL) + 80 * LL := by ring
      _ ≤ L / (10 * LL) + L / (10 * LL) := by gcongr
      _ ≤ 5 * L / LL := by
        field_simp [hLL.ne']
        nlinarith
  have haux' : 5 * L / LL ≤ ((auxiliaryPrimes N).card : ℝ) := by
    simpa [L, LL, logScale, logLogScale] using haux
  exact_mod_cast hleft.trans haux'

lemma tendsto_S_atTop : Tendsto S atTop atTop := by
  have hpow : Tendsto almostOnePower atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (9999 : ℝ) / 10000)).comp
      tendsto_natCast_atTop_atTop
  have hnat : Tendsto (fun N : ℕ ↦ (S N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop eventually_almostOnePower_le_natS hpow
  exact (tendsto_natCast_atTop_iff (R := ℝ)).mp hnat

lemma eventually_two_mul_S_le_KSafe :
    ∀ᶠ N : ℕ in atTop, 2 * S N ≤ KSafe N := by
  filter_upwards [eventually_pos_scales, eventually_logLogScale_le_logScale,
      eventually_KSafeReal_ge_two,
      tendsto_logScale.eventually
        (eventually_ge_atTop (Real.sqrt (4 * (10 : ℝ) ^ 7)))]
      with N hpos hLLle hKtwo hLlarge
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hLsq : 4 * (10 : ℝ) ^ 7 ≤ logScale N ^ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (4 * (10 : ℝ) ^ 7) := Real.sqrt_nonneg _
    have hsquare := mul_self_le_mul_self hsqrt0 hLlarge
    have hsqrteq : Real.sqrt (4 * (10 : ℝ) ^ 7) ^ 2 =
        4 * (10 : ℝ) ^ 7 := Real.sq_sqrt (by norm_num)
    nlinarith [hsqrteq]
  have hmain : 4 * (10 : ℝ) ^ 7 * logLogScale N ≤ logScale N ^ 3 := by
    calc
      4 * (10 : ℝ) ^ 7 * logLogScale N ≤
          4 * (10 : ℝ) ^ 7 * logScale N := by gcongr
      _ ≤ logScale N ^ 2 * logScale N := by gcongr
      _ = logScale N ^ 3 := by ring
  have hfour : 4 * SReal N ≤ KSafeReal N := by
    dsimp [SReal, KSafeReal, KReal]
    rw [div_div]
    field_simp
    nlinarith
  have hSfloor : (S N : ℝ) ≤ SReal N := by
    exact Nat.floor_le (by dsimp [SReal]; positivity)
  have hKhalf : KSafeReal N / 2 ≤ (KSafe N : ℝ) := half_le_floor hKtwo
  have hcast : (2 * S N : ℕ) ≤ KSafe N := by
    exact_mod_cast (calc
      (2 : ℝ) * (S N : ℝ) ≤ 2 * SReal N := by gcongr
      _ ≤ KSafeReal N / 2 := by linarith
      _ ≤ (KSafe N : ℝ) := hKhalf)
  simpa using hcast

/-- The repaired cubic scale inequality absorbs the complete `p'` cutoff. -/
theorem eventually_S_mul_smallPrimeCutoff_le_KSafe :
    ∀ᶠ N : ℕ in atTop,
      S N * smallPrimeCutoff N ≤ KSafe N := by
  filter_upwards [eventually_nat_S_mul_safe_repaired_den_le_KSafe_cube
      (4 * (10 : ℝ) ^ 8) (by positivity), eventually_two_mul_S_le_KSafe,
      eventually_pos_scales, eventually_nat_KSafe_lower]
      with N hcubic hSK hpos hKlower
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  let R : ℝ := 100 * (N : ℝ) ^ 2 * logScale N *
      logLogScale N ^ 2 / (KSafe N : ℝ) ^ 2
  let Y : ℝ := (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
      logLogScale N ^ 4 / logScale N
  let U : ℝ := (10 : ℝ) ^ 8 * (N : ℝ) ^ 2 *
      logLogScale N ^ 6 / (KSafe N : ℝ) ^ 2
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hT : (minorBadThreshold N : ℝ) ≤ R := by
    exact Nat.floor_le hR0
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hYU : Y ≤ U := by
    dsimp [Y, U, R] at *
    rw [div_le_iff₀ hL]
    calc
      (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
          logLogScale N ^ 4 ≤ (10 : ℝ) ^ 6 * R *
          logLogScale N ^ 4 := by gcongr
      _ = ((10 : ℝ) ^ 8 * (N : ℝ) ^ 2 *
          logLogScale N ^ 6 / (KSafe N : ℝ) ^ 2) *
            logScale N := by
        dsimp [R]
        field_simp
        ring
  have hXU : (smallPrimeCutoff N : ℝ) ≤ U + 1 := by
    exact (Nat.ceil_lt_add_one hY0).le.trans (by linarith)
  have hSU : (S N : ℝ) * U ≤ (KSafe N : ℝ) / 4 := by
    dsimp [U]
    field_simp [hK.ne']
    nlinarith [hcubic]
  have hSle : (S N : ℝ) ≤ (KSafe N : ℝ) / 2 := by
    have hSKR : (2 : ℝ) * (S N : ℝ) ≤ (KSafe N : ℝ) := by
      exact_mod_cast hSK
    nlinarith
  have hreal : (S N : ℝ) * (smallPrimeCutoff N : ℝ) ≤
      (KSafe N : ℝ) := by
    calc
      (S N : ℝ) * (smallPrimeCutoff N : ℝ) ≤
          (S N : ℝ) * (U + 1) := by gcongr
      _ = (S N : ℝ) * U + (S N : ℝ) := by ring
      _ ≤ (KSafe N : ℝ) / 4 + (KSafe N : ℝ) / 2 := by gcongr
      _ ≤ (KSafe N : ℝ) := by linarith
  exact_mod_cast hreal

lemma eventually_log_pow_twentyEight_le_almostOnePower :
    ∀ᶠ N : ℕ in atTop,
      logScale N ^ 28 ≤ almostOnePower N := by
  have hlittle :
      (fun x : ℝ ↦ Real.log x ^ (28 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ ((9999 : ℝ) / 10000)) :=
    isLittleO_log_rpow_rpow_atTop 28 (by norm_num)
  have hcomp := (hlittle.comp_tendsto tendsto_natCast_atTop_atTop).bound one_pos
  filter_upwards [hcomp, eventually_pos_scales] with N hN hpos
  rcases hpos with ⟨hNpos, hLone, hLLone, hLLL⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using zero_le_one.trans hLone.le
  simp only [Function.comp_apply, one_mul] at hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlognonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  simpa [logScale, almostOnePower, Real.rpow_natCast] using hN

/-- Every candidate prime is eventually below the smoothness cutoff. -/
theorem eventually_smallPrimeCutoff_le_S :
    ∀ᶠ N : ℕ in atTop, smallPrimeCutoff N ≤ S N := by
  filter_upwards [eventually_smallPrimeCutoff_cast_le_logScale_pow_28,
      eventually_log_pow_twentyEight_le_almostOnePower,
      eventually_almostOnePower_le_natS] with N hX hlog hS
  exact_mod_cast hX.trans (hlog.trans hS)

theorem eventually_two_hundred_le_S :
    ∀ᶠ N : ℕ in atTop, 200 ≤ S N :=
  tendsto_S_atTop.eventually_ge_atTop 200

/-- The quadratic room needed by the two-prime extension branch. -/
theorem eventually_hundred_mul_KSafe_le_S_sq :
    ∀ᶠ N : ℕ in atTop, 100 * KSafe N ≤ (S N) ^ 2 := by
  filter_upwards [eventually_nat_KSafe_upper, eventually_real_scales_ge_two,
      eventually_log_pow_ten_le_almostOnePower,
      eventually_almostOnePower_le_natS, eventually_nat_safe_scale_chain,
      eventually_pos_scales] with N hKupper hSreal hlog hpowS hchain hpos
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hSfloor : SReal N / 2 ≤ (S N : ℝ) := half_le_floor hSreal.1
  have hSN : (S N : ℝ) ≤ (N : ℝ) := by
    calc
      (S N : ℝ) ≤ (KSafe N : ℝ) := hchain.1
      _ ≤ (M N : ℝ) := hchain.2.1
      _ ≤ (N : ℝ) / 10 := hchain.2.2
      _ ≤ (N : ℝ) := by linarith
  have hLseven : logScale N ^ 7 ≤ logScale N ^ 10 := by
    simpa using pow_le_pow_right₀ hLone.le (by norm_num : 7 ≤ 10)
  have hlogN : logScale N ^ 10 ≤ (N : ℝ) :=
    hlog.trans (hpowS.trans hSN)
  have hpoly : 4 * logScale N ^ 7 ≤ (10 : ℝ) ^ 5 * (N : ℝ) := by
    calc
      4 * logScale N ^ 7 ≤ 4 * logScale N ^ 10 := by gcongr
      _ ≤ 4 * (N : ℝ) := by gcongr
      _ ≤ (10 : ℝ) ^ 5 * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hN.le
  have hSlower : (N : ℝ) ^ 2 /
      (4 * logScale N ^ 8) ≤ (S N : ℝ) ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (by dsimp [SReal]; positivity : 0 ≤ SReal N / 2)
      hSfloor 2
    calc
      (N : ℝ) ^ 2 / (4 * logScale N ^ 8) = (SReal N / 2) ^ 2 := by
        dsimp [SReal]
        field_simp [hL.ne']
        ring
      _ ≤ (S N : ℝ) ^ 2 := hsquare
  have htarget : 100 * (KSafe N : ℝ) ≤
      (N : ℝ) ^ 2 / (4 * logScale N ^ 8) := by
    calc
      100 * (KSafe N : ℝ) ≤
          100 * ((N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)) := by gcongr
      _ ≤ (N : ℝ) ^ 2 / (4 * logScale N ^ 8) := by
        field_simp [hL.ne']
        nlinarith [hpoly, mul_pos hN hL,
          mul_nonneg hN.le (pow_nonneg hL.le 7)]
  exact_mod_cast htarget.trans hSlower

end

end Erdos297.SupplyNumerics

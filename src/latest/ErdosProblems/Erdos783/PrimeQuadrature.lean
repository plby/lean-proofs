/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.SmoothBuchstab
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ErdosProblems.Erdos783.External.PrimeNumberTheoremAnd.IEANTN.Mertens

namespace Erdos783

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-! ## Finite Stieltjes summation -/

/-- Cumulative sum of a sequence on the integer interval `(lo, hi]`. -/
def finiteIocCumulative
    (coefficient : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc lo hi, coefficient k

/-- Discrete variation on the ordered sample points of `(lo, hi]`. -/
def finiteIocVariation
    (statistic : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc lo (hi - 1),
    |statistic (k + 1) - statistic k|

theorem finiteIocVariation_nonneg
    (statistic : ℕ → ℝ) (lo hi : ℕ) :
    0 ≤ finiteIocVariation statistic lo hi := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Finite Stieltjes summation by parts. -/
theorem finiteIoc_sum_by_parts
    (coefficient statistic : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo < hi) :
    (∑ k ∈ Finset.Ioc lo hi,
        statistic k * coefficient k) =
      statistic hi * finiteIocCumulative coefficient lo hi -
        ∑ k ∈ Finset.Ioc lo (hi - 1),
          (statistic (k + 1) - statistic k) *
            finiteIocCumulative coefficient lo k := by
  let supportedCoefficient : ℕ → ℝ :=
    fun k ↦ if lo < k then coefficient k else 0
  have hcumulative (t : ℕ) :
      (∑ k ∈ Finset.range (t + 1), supportedCoefficient k) =
        finiteIocCumulative coefficient lo t := by
    rw [finiteIocCumulative]
    have hfilter :
        (Finset.range (t + 1)).filter (fun k ↦ lo < k) =
          Finset.Ioc lo t := by
      ext k
      simp
      omega
    rw [← hfilter]
    simp only [supportedCoefficient, Finset.sum_filter]
  have hraw := Finset.sum_Ioc_by_parts
    statistic supportedCoefficient hlohi
  simp only [smul_eq_mul] at hraw
  have hleft :
      (∑ k ∈ Finset.Ioc lo hi,
          statistic k * supportedCoefficient k) =
        ∑ k ∈ Finset.Ioc lo hi,
          statistic k * coefficient k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklo : lo < k := (Finset.mem_Ioc.mp hk).1
    simp [supportedCoefficient, hklo]
  rw [hleft, hcumulative hi, hcumulative lo] at hraw
  have hloCumulative :
      finiteIocCumulative coefficient lo lo = 0 := by
    simp [finiteIocCumulative]
  rw [hloCumulative, mul_zero, sub_zero] at hraw
  simpa only [hcumulative] using hraw

/-- Uniform control of cumulative discrepancies gives a bounded-variation
estimate for the weighted sum. -/
theorem abs_finiteIoc_weightedSum_le
    (coefficient statistic : ℕ → ℝ)
    {lo hi : ℕ} {error : ℝ}
    (herror : 0 ≤ error)
    (hcumulative :
      ∀ t, lo ≤ t → t ≤ hi →
        |finiteIocCumulative coefficient lo t| ≤ error) :
    |∑ k ∈ Finset.Ioc lo hi,
        statistic k * coefficient k| ≤
      error *
        (|statistic hi| + finiteIocVariation statistic lo hi) := by
  by_cases hlohi : lo < hi
  · rw [finiteIoc_sum_by_parts coefficient statistic hlohi]
    calc
      |statistic hi * finiteIocCumulative coefficient lo hi -
          ∑ k ∈ Finset.Ioc lo (hi - 1),
            (statistic (k + 1) - statistic k) *
              finiteIocCumulative coefficient lo k| ≤
        |statistic hi * finiteIocCumulative coefficient lo hi| +
          |∑ k ∈ Finset.Ioc lo (hi - 1),
            (statistic (k + 1) - statistic k) *
              finiteIocCumulative coefficient lo k| := abs_sub _ _
      _ ≤ |statistic hi| * error +
            ∑ k ∈ Finset.Ioc lo (hi - 1),
              |(statistic (k + 1) - statistic k) *
                finiteIocCumulative coefficient lo k| := by
        apply add_le_add
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hcumulative hi (Nat.le_of_lt hlohi) le_rfl)
            (abs_nonneg _)
        · exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ |statistic hi| * error +
            ∑ k ∈ Finset.Ioc lo (hi - 1),
              |statistic (k + 1) - statistic k| * error := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left
        · apply hcumulative k
          · exact (Finset.mem_Ioc.mp hk).1.le
          · exact (Finset.mem_Ioc.mp hk).2.trans (Nat.sub_le hi 1)
        · exact abs_nonneg _
      _ = error *
            (|statistic hi| +
              finiteIocVariation statistic lo hi) := by
        rw [finiteIocVariation, ← Finset.sum_mul]
        ring
  · have hinterval : Finset.Ioc lo hi = ∅ :=
      Finset.Ioc_eq_empty hlohi
    rw [hinterval, Finset.sum_empty, abs_zero]
    exact mul_nonneg herror
      (add_nonneg (abs_nonneg _)
        (finiteIocVariation_nonneg statistic lo hi))

theorem finiteIocVariation_eq_sub_of_monotone
    (statistic : ℕ → ℝ) (hmono : Monotone statistic)
    {lo hi : ℕ} (hlohi : lo + 1 ≤ hi) :
    finiteIocVariation statistic lo hi =
      statistic hi - statistic (lo + 1) := by
  rw [finiteIocVariation]
  have hinterval :
      Finset.Ioc lo (hi - 1) = Finset.Ico (lo + 1) hi := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hinterval]
  calc
    (∑ k ∈ Finset.Ico (lo + 1) hi,
        |statistic (k + 1) - statistic k|) =
        ∑ k ∈ Finset.Ico (lo + 1) hi,
          (statistic (k + 1) - statistic k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (hmono (Nat.le_succ k))
    _ = statistic hi - statistic (lo + 1) :=
      Finset.sum_Ico_sub statistic hlohi

theorem finiteIocVariation_le_one_of_monotone_unit
    (statistic : ℕ → ℝ) (hmono : Monotone statistic)
    (hzero : ∀ k, 0 ≤ statistic k)
    (hone : ∀ k, statistic k ≤ 1)
    (lo hi : ℕ) :
    finiteIocVariation statistic lo hi ≤ 1 := by
  by_cases hlohi : lo + 1 ≤ hi
  · rw [finiteIocVariation_eq_sub_of_monotone
      statistic hmono hlohi]
    linarith [hzero (lo + 1), hone hi]
  · have hempty : Finset.Ioc lo (hi - 1) = ∅ := by
      exact Finset.Ioc_eq_empty (by omega)
    rw [finiteIocVariation, hempty, Finset.sum_empty]
    norm_num

/-- Primes in the logarithmic cell `(y^a, y^b]`, with real powers rounded
down exactly as in Mertens' cumulative prime sum. -/
def primeExponentCell (y : ℕ) (a b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊(y : ℝ) ^ a⌋₊ ⌊(y : ℝ) ^ b⌋₊).filter Nat.Prime

/-- Reciprocal prime mass in one logarithmic cell. -/
def primeExponentCellMass (y : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ primeExponentCell y a b, (p : ℝ)⁻¹

def primeReciprocalCumulativeReal (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (p : ℝ)⁻¹

theorem primeReciprocalCumulativeReal_eq_mertens (x : ℝ) :
    primeReciprocalCumulativeReal x =
      Real.log (Real.log x) + Mertens.M + Mertens.E₂p x := by
  simpa [primeReciprocalCumulativeReal, one_div] using
    Mertens.sum_prime_div_eq x

lemma floor_rpow_mono {y : ℕ} {a b : ℝ} (hy : 1 ≤ y) (hab : a ≤ b) :
    ⌊(y : ℝ) ^ a⌋₊ ≤ ⌊(y : ℝ) ^ b⌋₊ := by
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy) hab

theorem primeExponentCellMass_eq_cumulative_sub
    {y : ℕ} {a b : ℝ} (hy : 1 ≤ y) (hab : a ≤ b) :
    primeExponentCellMass y a b =
      primeReciprocalCumulativeReal ((y : ℝ) ^ b) -
        primeReciprocalCumulativeReal ((y : ℝ) ^ a) := by
  let A := ⌊(y : ℝ) ^ a⌋₊
  let B := ⌊(y : ℝ) ^ b⌋₊
  have hAB : A ≤ B := floor_rpow_mono hy hab
  let lower := (Finset.Ioc 0 A).filter Nat.Prime
  let upper := (Finset.Ioc 0 B).filter Nat.Prime
  have hsub : lower ⊆ upper := by
    intro p hp
    simp only [lower, upper, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hAB⟩, hp.2⟩
  have hdiff : upper \ lower = (Finset.Ioc A B).filter Nat.Prime := by
    ext p
    simp only [upper, lower, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp0, hpB⟩, hpPrime⟩, hpLower⟩
      refine ⟨⟨?_, hpB⟩, hpPrime⟩
      by_contra hpA
      exact hpLower ⟨⟨hp0, Nat.le_of_not_gt hpA⟩, hpPrime⟩
    · rintro ⟨⟨hpA, hpB⟩, hpPrime⟩
      refine ⟨⟨⟨by omega, hpB⟩, hpPrime⟩, ?_⟩
      rintro ⟨⟨_hp0, hpA'⟩, _hpPrime⟩
      omega
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => (p : ℝ)⁻¹)
  rw [hdiff] at hsum
  change primeExponentCellMass y a b =
    primeReciprocalCumulativeReal ((y : ℝ) ^ b) -
      primeReciprocalCumulativeReal ((y : ℝ) ^ a)
  dsimp only [primeExponentCellMass, primeExponentCell,
    primeReciprocalCumulativeReal, A, B]
  linarith

lemma log_log_rpow {y : ℕ} {a : ℝ} (hy : 2 ≤ y) (ha : 0 < a) :
    Real.log (Real.log ((y : ℝ) ^ a)) =
      Real.log a + Real.log (Real.log (y : ℝ)) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  rw [Real.log_rpow hyPos]
  rw [Real.log_mul ha.ne' hlogY.ne']

/-- Exact Mertens evaluation of a logarithmic cell.  All dependence on the
base `y` is confined to the two Mertens error terms. -/
theorem primeExponentCellMass_eq_log_sub_add_errors
    {y : ℕ} {a b : ℝ} (hy : 2 ≤ y) (ha : 0 < a) (hab : a ≤ b) :
    primeExponentCellMass y a b =
      Real.log b - Real.log a +
        (Mertens.E₂p ((y : ℝ) ^ b) -
          Mertens.E₂p ((y : ℝ) ^ a)) := by
  have hb : 0 < b := ha.trans_le hab
  rw [primeExponentCellMass_eq_cumulative_sub (by omega) hab,
    primeReciprocalCumulativeReal_eq_mertens,
    primeReciprocalCumulativeReal_eq_mertens,
    log_log_rpow hy hb, log_log_rpow hy ha]
  ring

theorem tendsto_mertensError_real :
    Tendsto Mertens.E₂p atTop (nhds 0) := by
  exact (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'

/-- The Mertens cell estimate is uniform over all cells whose exponents are
at least one: once the base is large, both endpoints are beyond the same
error threshold. -/
theorem eventually_primeExponentCellMass_close :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ a b : ℝ,
        1 ≤ a → a ≤ b →
        |primeExponentCellMass y a b -
          (Real.log b - Real.log a)| < ε := by
  intro ε hε
  have herror :
      ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| < ε / 2 :=
    by
      have h := tendsto_mertensError_real.eventually
        (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
      simpa [Real.dist_eq] using h
  rw [eventually_atTop] at herror
  obtain ⟨X, hX⟩ := herror
  obtain ⟨Y, hY⟩ := exists_nat_ge (max X 2)
  rw [eventually_atTop]
  refine ⟨Y, ?_⟩
  intro y hy a b ha hab
  have hy2 : 2 ≤ y := by
    exact_mod_cast (show (2 : ℝ) ≤ y by
      exact (le_max_right X 2).trans hY |>.trans (by exact_mod_cast hy))
  have hyX : X ≤ (y : ℝ) := by
    exact (le_max_left X 2).trans hY |>.trans (by exact_mod_cast hy)
  have hya : (y : ℝ) ≤ (y : ℝ) ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ y by omega)) ha
  have hyb : (y : ℝ) ≤ (y : ℝ) ^ b := by
    exact hya.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ y by omega)) hab)
  have hEa := hX _ (hyX.trans hya)
  have hEb := hX _ (hyX.trans hyb)
  rw [primeExponentCellMass_eq_log_sub_add_errors hy2
    (zero_lt_one.trans_le ha) hab]
  have htriangle :
      |Mertens.E₂p ((y : ℝ) ^ b) -
          Mertens.E₂p ((y : ℝ) ^ a)| < ε := by
    calc
      |Mertens.E₂p ((y : ℝ) ^ b) -
          Mertens.E₂p ((y : ℝ) ^ a)| ≤
          |Mertens.E₂p ((y : ℝ) ^ b)| +
            |Mertens.E₂p ((y : ℝ) ^ a)| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add hEb hEa
      _ = ε := by ring
  simpa only [add_sub_cancel_left] using htriangle

/-! ## Prime reciprocal Stieltjes discrepancy -/

/-- The exact logarithmic measure of the physical cell `(k-1,k]`. -/
def logLogCellWeight (k : ℕ) : ℝ :=
  Real.log (Real.log (k : ℝ)) -
    Real.log (Real.log ((k - 1 : ℕ) : ℝ))

theorem logLogCellWeight_eq_integral
    {k : ℕ} (hk : 3 ≤ k) :
    logLogCellWeight k =
      ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
        t⁻¹ / Real.log t := by
  have hkm1 : (1 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 1 < k - 1 by omega)
  have hk1 : (1 : ℝ) < k := by
    exact_mod_cast (show 1 < k by omega)
  symm
  simpa only [logLogCellWeight] using
    (integral_inv_div_log hkm1 hk1)

/-- An interval integral over integer endpoints is the sum of its unit-cell
integrals.  Integrability is requested only on the intervals actually used. -/
theorem intervalIntegral_eq_sum_Ioc_unit
    (f : ℝ → ℝ) {lo hi : ℕ} (hlohi : lo ≤ hi)
    (hprefix :
      ∀ n : ℕ, lo ≤ n → n ≤ hi →
        IntervalIntegrable f volume (lo : ℝ) n)
    (hcell :
      ∀ n : ℕ, lo ≤ n → n < hi →
        IntervalIntegrable f volume (n : ℝ) (n + 1 : ℕ)) :
    (∫ t : ℝ in (lo : ℝ)..hi, f t) =
      ∑ k ∈ Finset.Ioc lo hi,
        ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k, f t := by
  have hclaim :
      ∀ n : ℕ, lo ≤ n → n ≤ hi →
        (∫ t : ℝ in (lo : ℝ)..n, f t) =
          ∑ k ∈ Finset.Ioc lo n,
            ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k, f t := by
    intro n hln hnhi
    induction n, hln using Nat.le_induction with
    | base => simp
    | succ n hln ih =>
        have hnhi : n ≤ hi := by omega
        have hnlt : n < hi := by omega
        rw [Finset.sum_Ioc_succ_top hln, ← ih hnhi]
        have hadd :=
          intervalIntegral.integral_add_adjacent_intervals
            (hprefix n hln hnhi)
            (hcell n hln hnlt)
        simpa only [Nat.cast_add, Nat.cast_one,
          Nat.add_sub_cancel] using hadd.symm
  exact hclaim hi hlohi le_rfl

theorem sum_Ioc_logLogCellWeight
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    (∑ k ∈ Finset.Ioc lo hi, logLogCellWeight k) =
      Real.log (Real.log (hi : ℝ)) -
        Real.log (Real.log (lo : ℝ)) := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp [logLogCellWeight]
  | succ hi hlohi ih =>
      rw [Finset.sum_Ioc_succ_top hlohi, ih]
      simp only [logLogCellWeight]
      rw [Nat.add_sub_cancel]
      ring

theorem sum_Ioc_sub_pred
    (f : ℕ → ℝ) {lo hi : ℕ} (hlohi : lo ≤ hi) :
    (∑ k ∈ Finset.Ioc lo hi,
        (f k - f (k - 1))) =
      f hi - f lo := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ioc_succ_top hlohi, ih,
        Nat.add_sub_cancel]
      ring

/-- Signed coefficient whose cumulative mass is the discrepancy between
reciprocal primes and the continuous measure `dt/(t log t)`. -/
def primeLogLogDiscrepancyCoefficient (k : ℕ) : ℝ :=
  (if k.Prime then (k : ℝ)⁻¹ else 0) - logLogCellWeight k

theorem finiteIocCumulative_primeLogLogDiscrepancyCoefficient
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    finiteIocCumulative
        primeLogLogDiscrepancyCoefficient lo hi =
      (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime,
          (p : ℝ)⁻¹) -
        (Real.log (Real.log (hi : ℝ)) -
          Real.log (Real.log (lo : ℝ))) := by
  unfold finiteIocCumulative
  simp only [primeLogLogDiscrepancyCoefficient,
    Finset.sum_sub_distrib, sum_Ioc_logLogCellWeight hlohi]
  congr 1
  rw [Finset.sum_filter]

theorem primeIntervalMass_eq_cumulative_sub
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (p : ℝ)⁻¹) =
      primeReciprocalCumulativeReal (hi : ℝ) -
        primeReciprocalCumulativeReal (lo : ℝ) := by
  let lower := (Finset.Ioc 0 lo).filter Nat.Prime
  let upper := (Finset.Ioc 0 hi).filter Nat.Prime
  have hsub : lower ⊆ upper := by
    intro p hp
    simp only [lower, upper, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hlohi⟩, hp.2⟩
  have hdiff : upper \ lower = (Finset.Ioc lo hi).filter Nat.Prime := by
    ext p
    simp only [upper, lower, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp0, hpHi⟩, hpPrime⟩, hpLower⟩
      refine ⟨⟨?_, hpHi⟩, hpPrime⟩
      by_contra hpLo
      exact hpLower ⟨⟨hp0, Nat.le_of_not_gt hpLo⟩, hpPrime⟩
    · rintro ⟨⟨hpLo, hpHi⟩, hpPrime⟩
      refine ⟨⟨⟨by omega, hpHi⟩, hpPrime⟩, ?_⟩
      rintro ⟨⟨_hp0, hpLo'⟩, _hpPrime⟩
      omega
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => (p : ℝ)⁻¹)
  rw [hdiff] at hsum
  simp only [primeReciprocalCumulativeReal, Nat.floor_natCast]
  linarith

/-- At natural endpoints the cumulative discrepancy is exactly the
difference of two Mertens errors. -/
theorem finiteIocCumulative_primeLogLogDiscrepancyCoefficient_eq_errors
    {lo hi : ℕ} (hlo : 2 ≤ lo) (hlohi : lo ≤ hi) :
    finiteIocCumulative primeLogLogDiscrepancyCoefficient lo hi =
      Mertens.E₂p (hi : ℝ) - Mertens.E₂p (lo : ℝ) := by
  rw [finiteIocCumulative_primeLogLogDiscrepancyCoefficient hlohi,
    primeIntervalMass_eq_cumulative_sub hlohi,
    primeReciprocalCumulativeReal_eq_mertens,
    primeReciprocalCumulativeReal_eq_mertens]
  ring

/-- The cumulative prime-reciprocal discrepancy is uniformly small on
every tail `(y,t]`, with no upper restriction on `t`. -/
theorem eventually_uniform_primeLogLogCumulative :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ t : ℕ, y ≤ t →
        |finiteIocCumulative
          primeLogLogDiscrepancyCoefficient y t| < ε := by
  intro ε hε
  have herror :
      ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| < ε / 2 := by
    have h := tendsto_mertensError_real.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    simpa [Real.dist_eq] using h
  rw [eventually_atTop] at herror
  obtain ⟨X, hX⟩ := herror
  obtain ⟨Y, hY⟩ := exists_nat_ge (max X 2)
  rw [eventually_atTop]
  refine ⟨Y, ?_⟩
  intro y hy t hyt
  have hyX : X ≤ (y : ℝ) :=
    (le_max_left X 2).trans hY |>.trans (by exact_mod_cast hy)
  have hy2 : 2 ≤ y := by
    exact_mod_cast ((le_max_right X 2).trans hY |>.trans
      (by exact_mod_cast hy) : (2 : ℝ) ≤ y)
  have htX : X ≤ (t : ℝ) := hyX.trans (by exact_mod_cast hyt)
  rw [finiteIocCumulative_primeLogLogDiscrepancyCoefficient_eq_errors
    hy2 hyt]
  calc
    |Mertens.E₂p (t : ℝ) - Mertens.E₂p (y : ℝ)| ≤
        |Mertens.E₂p (t : ℝ)| + |Mertens.E₂p (y : ℝ)| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hX _ htX) (hX _ hyX)
    _ = ε := by ring

/-- Uniform prime quadrature for every monotone statistic taking values in
`[0,1]`.  The statistic and the upper endpoint may both vary with the base. -/
theorem eventually_monotonePrimeLogLogQuadrature :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
        ∀ statistic : ℕ → ℝ,
          Monotone statistic →
          (∀ k, 0 ≤ statistic k) →
          (∀ k, statistic k ≤ 1) →
          |(∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
                statistic p / p) -
              ∑ k ∈ Finset.Ioc y x,
                statistic k * logLogCellWeight k| < ε := by
  intro ε hε
  have hcumEvent :=
    eventually_uniform_primeLogLogCumulative (ε / 3) (by positivity)
  filter_upwards [hcumEvent] with y hcum
  intro x hyx statistic hmono hzero hone
  have hcum' : ∀ t, y ≤ t → t ≤ x →
      |finiteIocCumulative
        primeLogLogDiscrepancyCoefficient y t| ≤ ε / 3 := by
    intro t hyt _htx
    exact (hcum t hyt).le
  have hweighted := abs_finiteIoc_weightedSum_le
    primeLogLogDiscrepancyCoefficient statistic
    (show 0 ≤ ε / 3 by positivity) hcum'
  have hvariation : finiteIocVariation statistic y x ≤ 1 :=
    finiteIocVariation_le_one_of_monotone_unit
      statistic hmono hzero hone y x
  have hfactor :
      |statistic x| + finiteIocVariation statistic y x ≤ 2 := by
    rw [abs_of_nonneg (hzero x)]
    linarith [hone x]
  have hsmall :
      (ε / 3) *
          (|statistic x| + finiteIocVariation statistic y x) < ε := by
    calc
      (ε / 3) *
          (|statistic x| + finiteIocVariation statistic y x) ≤
          (ε / 3) * 2 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ < ε := by linarith
  have hrewrite :
      (∑ k ∈ Finset.Ioc y x,
          statistic k * primeLogLogDiscrepancyCoefficient k) =
        (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
            statistic p / p) -
          ∑ k ∈ Finset.Ioc y x,
            statistic k * logLogCellWeight k := by
    rw [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hkPrime : k.Prime
    · simp [primeLogLogDiscrepancyCoefficient, hkPrime,
        div_eq_mul_inv]
      ring
    · simp [primeLogLogDiscrepancyCoefficient, hkPrime]
  rw [hrewrite] at hweighted
  exact hweighted.trans_lt hsmall

end

end Erdos783

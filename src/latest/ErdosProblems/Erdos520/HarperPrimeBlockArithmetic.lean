import ErdosProblems.Erdos520.HarperOscillatoryPrime
import ErdosProblems.Erdos520.HarperBlockSchedule
import ErdosProblems.Erdos520.ThinEuler

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators Interval

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Arithmetic estimates for Harper's scheduled prime blocks

This module converts the vendored strong prime number theorem into the two
number-theoretic inputs used by the fixed-`q` Harper walk.  A first Abel
summation controls the logarithmically weighted reciprocal-prime sum; the
exact square schedule then gives a uniform two-sided reciprocal mass bound.
The oscillatory estimate from `HarperOscillatoryPrime` is also transferred
from natural-number intervals to the scheduled prime-coordinate subtype.
-/

/-- Logarithmically weighted reciprocal-prime mass on `(A,B]`. -/
noncomputable def weightedPrimeReciprocalBlock (A B : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
    Real.log (p : ℝ) / p

theorem freshPrimes_eq_Ioc_filter_prime (A B : ℕ) :
    freshPrimes A B = (Finset.Ioc A B).filter Nat.Prime := by
  ext p
  simp only [mem_freshPrimes, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem log_mul_freshReciprocalSum_le_weightedPrimeReciprocalBlock
    {A B : ℕ} (hA : 1 ≤ A) :
    Real.log (A : ℝ) * freshReciprocalSum A B ≤
      weightedPrimeReciprocalBlock A B := by
  rw [freshReciprocalSum, freshPrimes_eq_Ioc_filter_prime]
  unfold weightedPrimeReciprocalBlock
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpIoc := Finset.mem_Ioc.mp hp'.1
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
  have hlog : Real.log (A : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hApos (by exact_mod_cast hpIoc.1.le)
  calc
    Real.log (A : ℝ) * (p : ℝ)⁻¹ ≤
        Real.log (p : ℝ) * (p : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hpPos.le)
    _ = Real.log (p : ℝ) / p := by ring

theorem weightedPrimeReciprocalBlock_le_log_mul_freshReciprocalSum
    {A B : ℕ} :
    weightedPrimeReciprocalBlock A B ≤
      Real.log (B : ℝ) * freshReciprocalSum A B := by
  rw [freshReciprocalSum, freshPrimes_eq_Ioc_filter_prime]
  unfold weightedPrimeReciprocalBlock
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpIoc := Finset.mem_Ioc.mp hp'.1
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
  have hlog : Real.log (p : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log hpPos (by exact_mod_cast hpIoc.2)
  calc
    Real.log (p : ℝ) / p = Real.log (p : ℝ) * (p : ℝ)⁻¹ := by ring
    _ ≤ Real.log (B : ℝ) * (p : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hpPos.le)

/-- Exact Abel-summation identity with the Chebyshev-theta error exposed. -/
theorem weightedPrimeReciprocalBlock_eq_abel
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    weightedPrimeReciprocalBlock A B =
      Real.log ((B : ℝ) / A) +
        (B : ℝ)⁻¹ * thetaError B -
        (A : ℝ)⁻¹ * thetaError A +
        ∫ x in (A : ℝ)..B, thetaError x / x ^ 2 := by
  have h := weightedPrimeOscillation_abel_identity hA hAB 0
  have hsum : weightedPrimeReciprocalBlock A B =
      ∑ n ∈ Finset.Ioc A B, oscKernel 0 n * primeLogCoeff n := by
    unfold weightedPrimeReciprocalBlock
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, oscKernel, primeLogCoeff, div_eq_mul_inv, mul_comm]
    · simp [hp, primeLogCoeff]
  rw [hsum, h]
  have hApos : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hBpos : (0 : ℝ) < B := hApos.trans_le (by exact_mod_cast hAB)
  simp only [oscKernel, oscKernelDeriv, zero_mul, Real.cos_zero,
    Real.sin_zero, zero_add, one_div]
  rw [integral_inv_of_pos hApos hBpos]
  have hfun : (fun x : ℝ => -1 / x ^ 2 * thetaError x) =
      fun x : ℝ => -(thetaError x / x ^ 2) := by
    funext x
    ring
  rw [hfun, intervalIntegral.integral_neg]
  ring

/-- A relative theta error `delta` gives the expected logarithmic block mass,
with explicit endpoint and integral losses. -/
theorem abs_weightedPrimeReciprocalBlock_sub_log_le_of_thetaError
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {delta : ℝ}
    (herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x) :
    |weightedPrimeReciprocalBlock A B - Real.log ((B : ℝ) / A)| ≤
      2 * delta + delta * Real.log ((B : ℝ) / A) := by
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hBpos : (0 : ℝ) < B :=
    hApos.trans_le (by exact_mod_cast hAB)
  have hABreal : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hA_mem : (A : ℝ) ∈ Set.Icc (A : ℝ) B := ⟨le_rfl, hABreal⟩
  have hB_mem : (B : ℝ) ∈ Set.Icc (A : ℝ) B := ⟨hABreal, le_rfl⟩
  have hboundA : |(A : ℝ)⁻¹ * thetaError A| ≤ delta := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hApos)]
    calc
      (A : ℝ)⁻¹ * |thetaError A| ≤ (A : ℝ)⁻¹ * (delta * A) := by
        exact mul_le_mul_of_nonneg_left (herror A hA_mem)
          (inv_nonneg.mpr hApos.le)
      _ = delta := by field_simp
  have hboundB : |(B : ℝ)⁻¹ * thetaError B| ≤ delta := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
    calc
      (B : ℝ)⁻¹ * |thetaError B| ≤ (B : ℝ)⁻¹ * (delta * B) := by
        exact mul_le_mul_of_nonneg_left (herror B hB_mem)
          (inv_nonneg.mpr hBpos.le)
      _ = delta := by field_simp
  have hgInt : IntervalIntegrable
      (fun x : ℝ => delta / x) volume (A : ℝ) B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (lt_min hApos hBpos) hx.1)
    exact continuousAt_const.div continuousAt_id hx0
  have hpoint : ∀ x ∈ Set.Ioc (A : ℝ) B,
      |thetaError x / x ^ 2| ≤ delta / x := by
    intro x hx
    have hxpos : 0 < x := hApos.trans hx.1
    have hxIcc : x ∈ Set.Icc (A : ℝ) B := ⟨hx.1.le, hx.2⟩
    rw [abs_div, abs_pow, abs_of_pos hxpos]
    calc
      |thetaError x| / x ^ 2 ≤ (delta * x) / x ^ 2 :=
        div_le_div_of_nonneg_right (herror x hxIcc) (sq_nonneg x)
      _ = delta / x := by field_simp
  have hinterr :
      |∫ x in (A : ℝ)..B, thetaError x / x ^ 2| ≤
        delta * Real.log ((B : ℝ) / A) := by
    have hnorm :
        ‖∫ x in (A : ℝ)..B, thetaError x / x ^ 2‖ ≤
          ∫ x in (A : ℝ)..B, delta / x :=
      intervalIntegral.norm_integral_le_of_norm_le
        (μ := volume) hABreal
        (Filter.Eventually.of_forall fun x => by
          intro hx
          simpa only [Real.norm_eq_abs] using! hpoint x hx)
        hgInt
    simp only [div_eq_mul_inv] at hnorm
    rw [intervalIntegral.integral_const_mul,
      integral_inv_of_pos hApos hBpos] at hnorm
    simpa [mul_assoc] using! hnorm
  rw [weightedPrimeReciprocalBlock_eq_abel hA hAB]
  have htri :
      |(Real.log ((B : ℝ) / A) + (B : ℝ)⁻¹ * thetaError B -
          (A : ℝ)⁻¹ * thetaError A +
          ∫ x in (A : ℝ)..B, thetaError x / x ^ 2) -
          Real.log ((B : ℝ) / A)| ≤
        |(B : ℝ)⁻¹ * thetaError B| + |(A : ℝ)⁻¹ * thetaError A| +
          |∫ x in (A : ℝ)..B, thetaError x / x ^ 2| := by
    calc
      |(Real.log ((B : ℝ) / A) + (B : ℝ)⁻¹ * thetaError B -
          (A : ℝ)⁻¹ * thetaError A +
          ∫ x in (A : ℝ)..B, thetaError x / x ^ 2) -
          Real.log ((B : ℝ) / A)| =
        |(B : ℝ)⁻¹ * thetaError B - (A : ℝ)⁻¹ * thetaError A +
          ∫ x in (A : ℝ)..B, thetaError x / x ^ 2| := by ring_nf
      _ ≤ |(B : ℝ)⁻¹ * thetaError B - (A : ℝ)⁻¹ * thetaError A| +
          |∫ x in (A : ℝ)..B, thetaError x / x ^ 2| := abs_add_le _ _
      _ ≤ (|(B : ℝ)⁻¹ * thetaError B| + |(A : ℝ)⁻¹ * thetaError A|) +
          |∫ x in (A : ℝ)..B, thetaError x / x ^ 2| := by
        gcongr
        exact abs_sub _ _
      _ = _ := by ring
  exact htri.trans (by linarith)

theorem tendsto_mediumThetaSquareDelta_zero
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun x : ℝ =>
        C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) +
          4 * Real.log x / Real.sqrt x)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hneg : Tendsto
      (fun x : ℝ => -c * Real.log x ^ ((1 : ℝ) / 10))
      atTop atBot := by
    have hpos := Tendsto.const_mul_atTop hc hpow
    have heq : (fun x : ℝ => -c * Real.log x ^ ((1 : ℝ) / 10)) =
        fun x : ℝ => -(c * Real.log x ^ ((1 : ℝ) / 10)) := by
      funext x
      ring
    rw [heq, tendsto_neg_atBot_iff]
    exact hpos
  have hexp : Tendsto
      (fun x : ℝ => C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
    simpa using! (tendsto_const_nhds.mul
      (Real.tendsto_exp_atBot.comp hneg))
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 2))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun x : ℝ => 4 * Real.log x / Real.sqrt x)
      atTop (𝓝 0) := by
    have heq : ∀ᶠ x : ℝ in atTop,
        4 * Real.log x / Real.sqrt x =
          4 * (Real.log x / x ^ ((1 : ℝ) / 2)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow]
      ring
    have hmul : Tendsto
        (fun x : ℝ => (4 : ℝ) * (Real.log x / x ^ ((1 : ℝ) / 2)))
        atTop (𝓝 ((4 : ℝ) * 0)) := tendsto_const_nhds.mul hlog
    simpa using! hmul.congr' (Filter.EventuallyEq.symm heq)
  simpa using! hexp.add hsqrt

theorem mediumThetaBlockDelta_square_eq
    (c C : ℝ) (A : ℕ) :
    mediumThetaBlockDelta c C A (A ^ 2) =
      C * Real.exp (-c * Real.log (A : ℝ) ^ ((1 : ℝ) / 10)) +
        4 * Real.log (A : ℝ) / Real.sqrt A := by
  unfold mediumThetaBlockDelta
  push_cast
  rw [Real.log_pow]
  ring

theorem exists_mediumThetaBlockDelta_square_le_quarter
    {c C : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ A : ℕ, N ≤ A →
      mediumThetaBlockDelta c C A (A ^ 2) ≤ 1 / 4 := by
  have htReal := tendsto_mediumThetaSquareDelta_zero (C := C) hc
  have htNat : Tendsto
      (fun A : ℕ =>
        C * Real.exp (-c * Real.log (A : ℝ) ^ ((1 : ℝ) / 10)) +
          4 * Real.log (A : ℝ) / Real.sqrt (A : ℝ))
      atTop (𝓝 0) := htReal.comp tendsto_natCast_atTop_atTop
  have hquarter : ∀ᶠ A : ℕ in atTop,
      C * Real.exp (-c * Real.log (A : ℝ) ^ ((1 : ℝ) / 10)) +
          4 * Real.log (A : ℝ) / Real.sqrt (A : ℝ) < 1 / 4 :=
    (tendsto_order.mp htNat).2 (1 / 4) (by norm_num)
  have hpos : ∀ᶠ A : ℕ in atTop, 0 < A := eventually_gt_atTop 0
  have hfinal : ∀ᶠ A : ℕ in atTop,
      mediumThetaBlockDelta c C A (A ^ 2) ≤ 1 / 4 := by
    filter_upwards [hquarter, hpos] with A hA hApos
    rw [mediumThetaBlockDelta_square_eq c C A]
    exact hA.le
  exact Filter.eventually_atTop.1 hfinal

/-- Unconditional constant two-sided reciprocal mass on every sufficiently
large square block `(A,A²]`. -/
theorem exists_mediumPNT_square_primeReciprocalBlock_bounds :
    ∃ N : ℕ, ∀ A : ℕ, N ≤ A →
      (1 / 4 : ℝ) ≤ freshReciprocalSum A (A ^ 2) ∧
        freshReciprocalSum A (A ^ 2) ≤ 3 / 2 := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, htheta⟩ := exists_mediumThetaError
  obtain ⟨Ndelta, hNdelta⟩ :=
    exists_mediumThetaBlockDelta_square_le_quarter (C := C) hc
  obtain ⟨NX, hNX⟩ := exists_nat_ge X₀
  obtain ⟨Nexp, hNexp⟩ := exists_nat_ge (Real.exp 2)
  let N := max 2 (max Ndelta (max NX Nexp))
  refine ⟨N, ?_⟩
  intro A hNA
  have hA2 : 2 ≤ A := (le_max_left 2 _).trans hNA
  have hAdelta : Ndelta ≤ A := by
    exact (le_max_left Ndelta (max NX Nexp)).trans
      ((le_max_right 2 _).trans hNA)
  have hANX : NX ≤ A := by
    exact (le_max_left NX Nexp).trans
      ((le_max_right Ndelta _).trans ((le_max_right 2 _).trans hNA))
  have hANexp : Nexp ≤ A := by
    exact (le_max_right NX Nexp).trans
      ((le_max_right Ndelta _).trans ((le_max_right 2 _).trans hNA))
  have hAposNat : 0 < A := by omega
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposNat
  have hAone : (1 : ℝ) < A := by exact_mod_cast hA2
  have hlogApos : 0 < Real.log (A : ℝ) := Real.log_pos hAone
  have hAB : A ≤ A ^ 2 := by nlinarith
  have hX₀A : X₀ ≤ (A : ℝ) := hNX.trans (by exact_mod_cast hANX)
  have hexpA : Real.exp 2 ≤ (A : ℝ) := hNexp.trans (by exact_mod_cast hANexp)
  have hlogAgeTwo : 2 ≤ Real.log (A : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hexpA
    simpa using! h
  let delta := mediumThetaBlockDelta c C A (A ^ 2)
  have hdeltaQuarter : delta ≤ 1 / 4 := hNdelta A hAdelta
  have herror : ∀ x ∈ Set.Icc (A : ℝ) (A ^ 2 : ℕ),
      |thetaError x| ≤ delta * x := by
    intro x hx
    exact thetaError_le_mediumThetaBlockDelta hc hC.le htheta
      hA2 hAB hX₀A hx
  have habs :=
    abs_weightedPrimeReciprocalBlock_sub_log_le_of_thetaError
      (show 1 ≤ A by omega) hAB herror
  have hratio : (((A ^ 2 : ℕ) : ℝ) / (A : ℝ)) = (A : ℝ) := by
    push_cast
    field_simp
  have hlogRatio : Real.log (((A ^ 2 : ℕ) : ℝ) / (A : ℝ)) =
      Real.log (A : ℝ) := congrArg Real.log hratio
  rw [hlogRatio] at habs
  have herrorHalf :
      2 * delta + delta * Real.log (A : ℝ) ≤ Real.log (A : ℝ) / 2 := by
    have htwo : 2 * delta ≤ 1 / 2 := by linarith
    have hmul : delta * Real.log (A : ℝ) ≤
        (1 / 4 : ℝ) * Real.log (A : ℝ) :=
      mul_le_mul_of_nonneg_right hdeltaQuarter hlogApos.le
    nlinarith
  have hWlower : Real.log (A : ℝ) / 2 ≤
      weightedPrimeReciprocalBlock A (A ^ 2) := by
    have := neg_le_of_abs_le habs
    linarith
  have hWupper : weightedPrimeReciprocalBlock A (A ^ 2) ≤
      (3 / 2 : ℝ) * Real.log (A : ℝ) := by
    have := le_of_abs_le habs
    linarith
  have hlogB : Real.log (((A ^ 2 : ℕ) : ℝ)) =
      2 * Real.log (A : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hSnonneg : 0 ≤ freshReciprocalSum A (A ^ 2) := by
    unfold freshReciprocalSum
    positivity
  have hweightedUpper :=
    weightedPrimeReciprocalBlock_le_log_mul_freshReciprocalSum
      (A := A) (B := A ^ 2)
  rw [hlogB] at hweightedUpper
  have hweightedLower :=
    log_mul_freshReciprocalSum_le_weightedPrimeReciprocalBlock
      (B := A ^ 2) (show 1 ≤ A by omega)
  constructor
  · have hcancel : (1 / 2 : ℝ) ≤
        2 * freshReciprocalSum A (A ^ 2) := by
      apply (mul_le_mul_iff_of_pos_left hlogApos).mp
      calc
        Real.log (A : ℝ) * (1 / 2 : ℝ) =
            Real.log (A : ℝ) / 2 := by ring
        _ ≤ weightedPrimeReciprocalBlock A (A ^ 2) := hWlower
        _ ≤ 2 * Real.log (A : ℝ) * freshReciprocalSum A (A ^ 2) :=
          hweightedUpper
        _ = Real.log (A : ℝ) *
            (2 * freshReciprocalSum A (A ^ 2)) := by ring
    linarith
  · apply (mul_le_mul_iff_of_pos_left hlogApos).mp
    calc
      Real.log (A : ℝ) * freshReciprocalSum A (A ^ 2) ≤
          weightedPrimeReciprocalBlock A (A ^ 2) := hweightedLower
      _ ≤ (3 / 2 : ℝ) * Real.log (A : ℝ) := hWupper
      _ = Real.log (A : ℝ) * (3 / 2 : ℝ) := by ring

theorem map_harperScheduledPrimeBlock_eq_freshPrimes
    {y j : ℕ}
    (hy : harperBlockEndpoint (j + 1) ≤ y) :
    (harperScheduledPrimeBlock y j).map (Function.Embedding.subtype _) =
      freshPrimes (harperBlockEndpoint j) (harperBlockEndpoint (j + 1)) := by
  ext n
  simp only [Finset.mem_map, mem_freshPrimes]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpInterval := (mem_harperScheduledPrimeBlock p).mp hp
    have hpPrime := Nat.prime_of_mem_primesBelow p.property
    exact ⟨hpPrime, hpInterval⟩
  · rintro ⟨hnPrime, hnlo, hnhi⟩
    let p : HarperPrimeIndex y :=
      ⟨n, Nat.mem_primesBelow.mpr ⟨by omega, hnPrime⟩⟩
    refine ⟨p, ?_, rfl⟩
    exact (mem_harperScheduledPrimeBlock p).mpr ⟨hnlo, hnhi⟩

theorem sum_harperScheduledPrimeBlock_inv_eq_freshReciprocalSum
    {y j : ℕ}
    (hy : harperBlockEndpoint (j + 1) ≤ y) :
    (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) =
      freshReciprocalSum (harperBlockEndpoint j)
        (harperBlockEndpoint (j + 1)) := by
  let e : HarperPrimeIndex y ↪ ℕ := Function.Embedding.subtype _
  calc
    (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) =
        ∑ n ∈ (harperScheduledPrimeBlock y j).map e, (n : ℝ)⁻¹ := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ n ∈ freshPrimes (harperBlockEndpoint j)
          (harperBlockEndpoint (j + 1)), (n : ℝ)⁻¹ := by
      rw [map_harperScheduledPrimeBlock_eq_freshPrimes hy]
    _ = _ := rfl

theorem sum_harperScheduledPrimeBlock_cos_div_eq
    {y j : ℕ}
    (hy : harperBlockEndpoint (j + 1) ≤ y) (tau : ℝ) :
    (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (tau * Real.log (p.1 : ℝ)) / p.1) =
      ∑ p ∈ (Finset.Ioc (harperBlockEndpoint j)
          (harperBlockEndpoint (j + 1))).filter Nat.Prime,
        Real.cos (tau * Real.log (p : ℝ)) / p := by
  let e : HarperPrimeIndex y ↪ ℕ := Function.Embedding.subtype _
  calc
    (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (tau * Real.log (p.1 : ℝ)) / p.1) =
        ∑ n ∈ (harperScheduledPrimeBlock y j).map e,
          Real.cos (tau * Real.log (n : ℝ)) / n := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ n ∈ freshPrimes (harperBlockEndpoint j)
          (harperBlockEndpoint (j + 1)),
          Real.cos (tau * Real.log (n : ℝ)) / n := by
      rw [map_harperScheduledPrimeBlock_eq_freshPrimes hy]
    _ = _ := by
      rw [freshPrimes_eq_Ioc_filter_prime]

/-- Scheduled-coordinate form of the unconditional two-sided block mass,
uniform in every ambient cutoff containing the block. -/
theorem exists_eventually_harperScheduledPrimeBlock_inv_bounds :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        (1 / 4 : ℝ) ≤
            ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ ∧
          (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) ≤ 3 / 2 := by
  obtain ⟨N, hN⟩ := exists_mediumPNT_square_primeReciprocalBlock_bounds
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (hend.eventually_ge_atTop N)
  refine ⟨J, ?_⟩
  intro j hJj y hy
  have hNj : N ≤ harperBlockEndpoint j := hJ j hJj
  have hbounds := hN (harperBlockEndpoint j) hNj
  rw [sum_harperScheduledPrimeBlock_inv_eq_freshReciprocalSum hy]
  rw [harperBlockEndpoint_succ]
  exact hbounds

/-- The explicit strong-PNT cosine-sum estimate on the exact scheduled prime
coordinate subtype. -/
theorem exists_mediumPNT_harperScheduledPrimeOscillation_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ tau : ℝ, tau ≠ 0 →
            |∑ p ∈ harperScheduledPrimeBlock y j,
                Real.cos (tau * Real.log (p.1 : ℝ)) / p.1| ≤
              (2 / |tau| +
                  2 * mediumThetaBlockDelta c C
                    (harperBlockEndpoint j) (harperBlockEndpoint (j + 1)) +
                  mediumThetaBlockDelta c C
                    (harperBlockEndpoint j) (harperBlockEndpoint (j + 1)) *
                    (1 + |tau|) *
                    Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
                      harperBlockEndpoint j)) *
                invLog (harperBlockEndpoint j) := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, hosc⟩ :=
    exists_mediumPNT_primeOscillation_bound
  obtain ⟨NX, hNX⟩ := exists_nat_ge X₀
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (hend.eventually_ge_atTop NX)
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro j hJj y hy tau htau
  have hNXj : NX ≤ harperBlockEndpoint j := hJ j hJj
  have hXj : X₀ ≤ (harperBlockEndpoint j : ℝ) :=
    hNX.trans (by exact_mod_cast hNXj)
  have hA2 : 2 ≤ harperBlockEndpoint j :=
    (by have := harperBlockEndpoint_ge_sixteen j; omega)
  have hAB : harperBlockEndpoint j ≤ harperBlockEndpoint (j + 1) :=
    monotone_harperBlockEndpoint (by omega)
  rw [sum_harperScheduledPrimeBlock_cos_div_eq hy tau]
  exact hosc _ _ hXj hA2 hAB tau htau

end Problem520
end Erdos

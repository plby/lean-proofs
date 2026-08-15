/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PrimePowers
import UnitFractions.Fourier

/-!
# Erdős Problem 285: rough-denominator counting

This file isolates the finite union bound in Martin's Lemma 9.  An integer whose
largest exact prime-power part exceeds `y` is a multiple of a prime power in
`(y,x]`.  Consequently its count, and its reciprocal mass in an interval bounded
away from zero, are controlled by the reciprocal mass of those prime powers.

The last section combines this finite estimate with the prime-power Mertens
estimate already proved in `UnitFractions.ForMathlib.BasicEstimates`.  It is
phrased for a general moving cutoff.  In particular it applies as soon as one
has the elementary logarithmic calculation for `y = x / log(x)^A`.
-/

namespace Erdos285.RoughCounts

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.PrimePowers

/-- Prime powers in the half-open interval `(y,x]`. -/
def largePrimePowers (x y : ℕ) : Finset ℕ :=
  (Icc (y + 1) x).filter IsPrimePow

/-- Integers in `[L,x]` whose largest exact prime-power part is larger than `y`. -/
def roughNumbersIn (L x y : ℕ) : Finset ℕ :=
  (Icc L x).filter fun n ↦ y < largestPrimePowerPart n

/-- Multiples of `q` in `[1,x]`. -/
def multiplesUpTo (x q : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n ↦ q ∣ n

/-- Reciprocal mass of the prime powers in `(y,x]`. -/
def primePowerReciprocalTail (x y : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹

/-- Reciprocal mass of a finite set of natural numbers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (n : ℝ)⁻¹

/-- The prime-power Mertens summatory function. -/
def primePowerReciprocalUpTo (x : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 x).filter IsPrimePow, (q : ℝ)⁻¹

/-- Martin's standard logarithmic cutoff, rounded down to a natural number. -/
def logPowerCutoff (A x : ℕ) : ℕ :=
  ⌊(x : ℝ) / Real.log (x : ℝ) ^ A⌋₊

/-- Natural left endpoint of a terminal interval `[alpha*x,x]`. -/
def proportionalLeftEndpoint (α : ℝ) (x : ℕ) : ℕ :=
  ⌈α * x⌉₊

@[simp] lemma mem_largePrimePowers {x y q : ℕ} :
    q ∈ largePrimePowers x y ↔ y < q ∧ q ≤ x ∧ IsPrimePow q := by
  simp only [largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hyq, hqx⟩, hq⟩
    exact ⟨Nat.lt_of_succ_le hyq, hqx, hq⟩
  · rintro ⟨hyq, hqx, hq⟩
    exact ⟨⟨hyq, hqx⟩, hq⟩

@[simp] lemma mem_roughNumbersIn {L x y n : ℕ} :
    n ∈ roughNumbersIn L x y ↔ L ≤ n ∧ n ≤ x ∧ y < largestPrimePowerPart n := by
  simp [roughNumbersIn, and_assoc]

@[simp] lemma mem_multiplesUpTo {x q n : ℕ} :
    n ∈ multiplesUpTo x q ↔ 1 ≤ n ∧ n ≤ x ∧ q ∣ n := by
  simp [multiplesUpTo, and_assoc]

lemma reciprocalMass_nonneg (A : Finset ℕ) : 0 ≤ reciprocalMass A := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

lemma primePowerReciprocalTail_nonneg (x y : ℕ) :
    0 ≤ primePowerReciprocalTail x y := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Every rough integer is covered by the multiples of its largest exact
prime-power part. -/
lemma roughNumbersIn_subset_biUnion (L x y : ℕ) :
    roughNumbersIn L x y ⊆
      (largePrimePowers x y).biUnion (multiplesUpTo x) := by
  intro n hn
  rw [mem_roughNumbersIn] at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnlt : n < 2 := Nat.lt_of_not_ge h
    have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hnlt
    have hz : largestPrimePowerPart n = 0 := by
      simp [largestPrimePowerPart, hempty]
    omega
  let q := largestPrimePowerPart n
  have hqmem : q ∈ primePowerParts n := largestPrimePowerPart_mem hn2
  have hqspec := (mem_primePowerParts (by omega : n ≠ 0)).mp hqmem
  rw [Finset.mem_biUnion]
  refine ⟨q, ?_, ?_⟩
  · rw [mem_largePrimePowers]
    exact ⟨hn.2.2, largestPrimePowerPart_le.trans hn.2.1, hqspec.1⟩
  · rw [mem_multiplesUpTo]
    exact ⟨by omega, hn.2.1, hqspec.2.1⟩

/-- The number of rough integers is at most the sum of the numbers of multiples
of the relevant prime powers. -/
lemma roughNumbersIn_card_le_sum_div (L x y : ℕ) :
    (roughNumbersIn L x y).card ≤
      ∑ q ∈ largePrimePowers x y, x / q := by
  calc
    (roughNumbersIn L x y).card ≤
        ((largePrimePowers x y).biUnion (multiplesUpTo x)).card :=
      Finset.card_le_card (roughNumbersIn_subset_biUnion L x y)
    _ ≤ ∑ q ∈ largePrimePowers x y, (multiplesUpTo x q).card :=
      Finset.card_biUnion_le
    _ = ∑ q ∈ largePrimePowers x y, x / q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq1 : 1 ≤ q := (mem_largePrimePowers.mp hq).2.2.one_lt.le
      exact UnitFractions.count_multiples hq1

/-- Real-valued form of the union bound. -/
lemma roughNumbersIn_card_le_mul_tail (L x y : ℕ) :
    ((roughNumbersIn L x y).card : ℝ) ≤
      (x : ℝ) * primePowerReciprocalTail x y := by
  have hcast :
      ((↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) : ℝ) =
        ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := by
    norm_cast
  calc
    ((roughNumbersIn L x y).card : ℝ) ≤
        (↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) := by
      exact_mod_cast roughNumbersIn_card_le_sum_div L x y
    _ = ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := hcast
    _ ≤ ∑ q ∈ largePrimePowers x y, (x : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      exact Nat.cast_div_le
    _ = (x : ℝ) * primePowerReciprocalTail x y := by
      simp only [primePowerReciprocalTail, div_eq_mul_inv, Finset.mul_sum]

/-- On an interval with positive left endpoint, reciprocal mass is bounded by
cardinality divided by that endpoint. -/
lemma reciprocalMass_le_card_div {A : Finset ℕ} {L : ℕ} (hL : 1 ≤ L)
    (hA : ∀ n ∈ A, L ≤ n) :
    reciprocalMass A ≤ (A.card : ℝ) / L := by
  calc
    reciprocalMass A ≤ ∑ n ∈ A, (L : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hL.trans (hA n hn)
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
      have hLn : (L : ℝ) ≤ n := by exact_mod_cast hA n hn
      exact (inv_le_inv₀ hnpos hLpos).2 hLn
    _ = (A.card : ℝ) / L := by
      simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Reciprocal-mass version of the rough-number union bound. -/
lemma roughNumbersIn_reciprocalMass_le (L x y : ℕ) (hL : 1 ≤ L) :
    reciprocalMass (roughNumbersIn L x y) ≤
      ((x : ℝ) / L) * primePowerReciprocalTail x y := by
  calc
    reciprocalMass (roughNumbersIn L x y) ≤
        ((roughNumbersIn L x y).card : ℝ) / L := by
      apply reciprocalMass_le_card_div hL
      intro n hn
      exact (mem_roughNumbersIn.mp hn).1
    _ ≤ ((x : ℝ) * primePowerReciprocalTail x y) / L := by
      exact div_le_div_of_nonneg_right (roughNumbersIn_card_le_mul_tail L x y)
        (Nat.cast_nonneg L)
    _ = ((x : ℝ) / L) * primePowerReciprocalTail x y := by ring

/-- The tail is the difference of the two prime-power Mertens sums. -/
lemma primePowerReciprocalTail_eq_sub {x y : ℕ} (hyx : y ≤ x) :
    primePowerReciprocalTail x y =
      primePowerReciprocalUpTo x - primePowerReciprocalUpTo y := by
  let A := (Icc 1 x).filter IsPrimePow
  let B := (Icc 1 y).filter IsPrimePow
  have hBA : B ⊆ A := by
    intro q hq
    simp only [B, A, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans hyx⟩, hq.2⟩
  change (∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹) =
    (∑ q ∈ A, (q : ℝ)⁻¹) - ∑ q ∈ B, (q : ℝ)⁻¹
  rw [← Finset.sum_sdiff hBA]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr
  · ext q
    simp only [largePrimePowers, A, B, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hyq, hqx⟩, hqpp⟩
      refine ⟨⟨⟨hqpp.one_lt.le, hqx⟩, hqpp⟩, ?_⟩
      intro hqy
      omega
    · rintro ⟨⟨⟨hq1, hqx⟩, hqpp⟩, hnot⟩
      refine ⟨⟨?_, hqx⟩, hqpp⟩
      by_contra hyq
      apply hnot
      exact ⟨⟨hq1, Nat.le_of_not_gt hyq⟩, hqpp⟩
  · intro q hq
    rfl

/-- The error term in the prime-power Mertens formula tends to zero along the
natural numbers. -/
lemma exists_primePowerReciprocalUpTo_error_tendsto_zero :
    ∃ b : ℝ,
      Tendsto
        (fun x : ℕ ↦
          primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b))
        atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  refine ⟨b, ?_⟩
  have hb' := hb.comp_tendsto tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hzero := hb'.trans_tendsto hinv
  simpa [Function.comp_def, primePowerReciprocalUpTo, Nat.floor_natCast] using hzero

/-! ## The cutoff `x / log(x)^A` -/

lemma logPowerScale_tendsto_atTop (A : ℕ) :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ A) atTop atTop := by
  have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
    (1 : ℝ) 0 A zero_lt_one).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

lemma logPowerCutoff_tendsto_atTop (A : ℕ) :
    Tendsto (logPowerCutoff A) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (logPowerScale_tendsto_atTop A)

lemma logPowerCutoff_eventually_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hx
  have hden : (1 : ℝ) ≤ Real.log (x : ℝ) ^ A := one_le_pow₀ hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hscale0 : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_nonneg hx0 (zero_le_one.trans hden)
  have hfloor : (logPowerCutoff A x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ A := by
    exact Nat.floor_le hscale0
  have hscale : (x : ℝ) / Real.log (x : ℝ) ^ A ≤ x :=
    div_le_self hx0 hden
  exact_mod_cast hfloor.trans hscale

lemma proportionalLeftEndpoint_eventually_one_le {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ proportionalLeftEndpoint α x := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [proportionalLeftEndpoint, Nat.one_le_ceil_iff]
  exact mul_pos hα (by exact_mod_cast hx)

lemma proportionalLeftEndpoint_eventually_ratio_le_inv {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / proportionalLeftEndpoint α x ≤ α⁻¹ := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hceilpos : (0 : ℝ) < proportionalLeftEndpoint α x := by
    exact_mod_cast (Nat.ceil_pos.mpr (mul_pos hα hxpos))
  rw [div_le_iff₀ hceilpos, inv_mul_eq_div, le_div_iff₀ hα]
  simpa [proportionalLeftEndpoint, mul_comm] using Nat.le_ceil (α * (x : ℝ))

lemma loglog_div_log_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_log_coe_at_top
  simpa [id, Function.comp_def] using h

lemma logPowerCutoff_ratio_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp (logPowerScale_tendsto_atTop A)

lemma log_logPowerCutoff_ratio_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log
        ((logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A)))
      atTop (𝓝 0) := by
  have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto
  exact hcont.comp (logPowerCutoff_ratio_tendsto_one A)

lemma log_logPowerCutoff_div_log_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
  let scale : ℕ → ℝ := fun x ↦ (x : ℝ) / Real.log (x : ℝ) ^ A
  let ratio : ℕ → ℝ := fun x ↦ (logPowerCutoff A x : ℝ) / scale x
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio, scale] using logPowerCutoff_ratio_tendsto_one A
  have hlogratio : Tendsto (fun x ↦ Real.log (ratio x)) atTop (𝓝 0) := by
    simpa [ratio, scale] using log_logPowerCutoff_ratio_tendsto_zero A
  have hlogratio_div : Tendsto
      (fun x : ℕ ↦ Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hmain : Tendsto
      (fun x : ℕ ↦
        1 - (A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 1) := by
    have hmiddle : Tendsto
        (fun x : ℕ ↦ -(A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)))
        atTop (𝓝 0) := by
      simpa using (loglog_div_log_tendsto_zero.const_mul (-(A : ℝ)))
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds.add hmiddle).add hlogratio_div
  apply hmain.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      (logPowerScale_tendsto_atTop A).eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with x hlogx hxone hscale hratioPos
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hxone
  have hlogne : Real.log (x : ℝ) ≠ 0 := hlogx.ne'
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlogx A
  have hscalene : scale x ≠ 0 := hscale.ne'
  have hratione : ratio x ≠ 0 := hratioPos.ne'
  have hcutoff : (logPowerCutoff A x : ℝ) = ratio x * scale x := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hscalene).symm
  rw [hcutoff, Real.log_mul hratione hscalene]
  dsimp [scale]
  rw [Real.log_div hxpos.ne' (pow_ne_zero A hlogne), Real.log_pow]
  field_simp
  ring

lemma logPowerCutoff_loglog_sub_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (logPowerCutoff A x : ℝ)))
      atTop (𝓝 0) := by
  have hratio := log_logPowerCutoff_div_log_tendsto_one A
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hneg := hlogratio.neg
  have hneg0 : Tendsto
      (fun x : ℕ ↦ -Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by simpa using hneg
  apply hneg0.congr'
  have hlogCutoffTop : Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (logPowerCutoff_tendsto_atTop A))
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogCutoffTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hcut
  rw [Real.log_div hcut.ne' hx.ne']
  ring

/-- A moving prime-power tail tends to zero whenever both endpoints tend to
infinity and their logarithmic logarithms become equal.  This is the exact
analytic interface needed for cutoffs such as `x / log(x)^A`. -/
lemma primePowerReciprocalTail_tendsto_zero {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ ↦ primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hby := hb.comp hy_top
  have hsum := hlog.add (hb.sub hby)
  have hsum0 : Tendsto
      (fun x : ℕ ↦
        Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y x : ℝ)) +
          ((primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b)) -
            (primePowerReciprocalUpTo (y x) -
              (Real.log (Real.log (y x : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hy_le] with x hyx
  rw [primePowerReciprocalTail_eq_sub hyx]
  ring

/-- The three moving-cutoff facts used when specializing Martin's union bound. -/
theorem logPowerCutoff_spec (A : ℕ) :
    (∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x) ∧
      Tendsto (logPowerCutoff A) atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (logPowerCutoff A x : ℝ)))
        atTop (𝓝 0) :=
  ⟨logPowerCutoff_eventually_le A, logPowerCutoff_tendsto_atTop A,
    logPowerCutoff_loglog_sub_tendsto_zero A⟩

lemma primePowerReciprocalTail_logPowerCutoff_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ primePowerReciprocalTail x (logPowerCutoff A x))
      atTop (𝓝 0) := by
  exact primePowerReciprocalTail_tendsto_zero
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-- Epsilon form of Martin's rough-count estimate.  The exceptional set has
`o(x)` elements under the moving-cutoff hypotheses. -/
lemma roughNumbersIn_card_isLittleO {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    (fun x : ℕ ↦ ((roughNumbersIn 1 x (y x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have heps : ∀ᶠ x in atTop, primePowerReciprocalTail x (y x) ≤ ε :=
    (htail.eventually (Iio_mem_nhds hε)).mono fun _ h ↦ h.le
  filter_upwards [heps] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    ((roughNumbersIn 1 x (y x)).card : ℝ) ≤
        (x : ℝ) * primePowerReciprocalTail x (y x) :=
      roughNumbersIn_card_le_mul_tail 1 x (y x)
    _ ≤ (x : ℝ) * ε := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg x)
    _ = ε * (x : ℝ) := by ring

lemma roughNumbersIn_logPowerCutoff_card_isLittleO (A : ℕ) :
    (fun x : ℕ ↦
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  exact roughNumbersIn_card_isLittleO
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-- Reciprocal mass tends to zero in any family of terminal intervals whose
left endpoint remains a fixed positive proportion of the right endpoint. -/
lemma roughNumbersIn_reciprocalMass_tendsto_zero
    {L y : ℕ → ℕ} {C : ℝ}
    (hL : ∀ᶠ x : ℕ in atTop, 1 ≤ L x)
    (hratio : ∀ᶠ x : ℕ in atTop, (x : ℝ) / L x ≤ C)
    (hy_le : ∀ᶠ x : ℕ in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass (roughNumbersIn (L x) x (y x)))
      atTop (𝓝 0) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  have hupper : Tendsto
      (fun x : ℕ ↦ C * primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
    simpa using htail.const_mul C
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [hL, hratio] with x hLx hrat
    calc
      reciprocalMass (roughNumbersIn (L x) x (y x)) ≤
          ((x : ℝ) / L x) * primePowerReciprocalTail x (y x) :=
        roughNumbersIn_reciprocalMass_le (L x) x (y x) hLx
      _ ≤ C * primePowerReciprocalTail x (y x) :=
        mul_le_mul_of_nonneg_right hrat (primePowerReciprocalTail_nonneg _ _)
  · exact hupper

/-- Concrete reciprocal-mass form for Martin's interval
`[ceil(alpha*x),x]` and logarithmic prime-power cutoff. -/
lemma roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero
    (A : ℕ) {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (roughNumbersIn (proportionalLeftEndpoint α x) x
          (logPowerCutoff A x)))
      atTop (𝓝 0) := by
  exact roughNumbersIn_reciprocalMass_tendsto_zero
    (proportionalLeftEndpoint_eventually_one_le hα)
    (proportionalLeftEndpoint_eventually_ratio_le_inv hα)
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-! ## A quantitative logarithmic-cutoff estimate -/

/-- The inverse square root of the natural logarithm tends to zero. -/
lemma inv_sqrt_log_tendsto_zero :
    Tendsto (fun x : ℕ ↦ (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top)

/-- `log log x` is negligible compared with `sqrt (log x)`. -/
lemma loglog_div_sqrt_log_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) /
        Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero.comp
      tendsto_log_coe_at_top
  simpa [Function.comp_def, Real.sqrt_eq_rpow] using h

/-- The logarithm of `floor (x / log(x)^A)` is eventually at least half of
`log x`.  The fixed factor `1/2` absorbs the floor, while
`A * log log x = o(log x)`. -/
lemma logPowerCutoff_eventually_log_half_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) / 2 ≤
        Real.log (logPowerCutoff A x : ℝ) := by
  have hinvlog : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hsmall : Tendsto
      (fun x : ℕ ↦
        (A : ℝ) *
            (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log 2 * (Real.log (x : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using
      (loglog_div_log_tendsto_zero.const_mul (A : ℝ)).add
        (hinvlog.const_mul (Real.log 2))
  have hratio := logPowerCutoff_ratio_tendsto_one A
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
      hsmall.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hratio.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))]
      with x hlog hsmallx hratiox
  have hxpos : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hlog
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlogpos A
  have hscale : 0 < (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_pos hxpos hpowpos
  have hcutoffLower :
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ A) <
        (logPowerCutoff A x : ℝ) := by
    rwa [lt_div_iff₀ hscale] at hratiox
  have hlogLower := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hscale) hcutoffLower.le
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcutoffLogLower :
      Real.log (x : ℝ) - (A : ℝ) * Real.log (Real.log (x : ℝ)) -
          Real.log 2 ≤ Real.log (logPowerCutoff A x : ℝ) := by
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hscale.ne',
      Real.log_div hxpos.ne' (pow_ne_zero A hlogpos.ne'), Real.log_pow,
      hloghalf] at hlogLower
    linarith
  have hsmallx' :
      (A : ℝ) * Real.log (Real.log (x : ℝ)) + Real.log 2 <
        Real.log (x : ℝ) / 2 := by
    have heq : (A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log 2 * (Real.log (x : ℝ))⁻¹ =
        ((A : ℝ) * Real.log (Real.log (x : ℝ)) + Real.log 2) /
          Real.log (x : ℝ) := by field_simp
    rw [heq, div_lt_iff₀ hlogpos] at hsmallx
    nlinarith
  linarith

/-- Quantitative lower expansion for the logarithm of the cutoff. -/
lemma logPowerCutoff_eventually_log_sub_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) -
          (A : ℝ) * Real.log (Real.log (x : ℝ)) - Real.log 2 ≤
        Real.log (logPowerCutoff A x : ℝ) := by
  have hratio := logPowerCutoff_ratio_tendsto_one A
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))]
      with x hlog hratiox
  have hxpos : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp hlog)
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlog A
  have hscale : 0 < (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_pos hxpos hpowpos
  have hcutoffLower :
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ A) <
        (logPowerCutoff A x : ℝ) := by
    rwa [lt_div_iff₀ hscale] at hratiox
  have hlogLower := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hscale) hcutoffLower.le
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hscale.ne',
    Real.log_div hxpos.ne' (pow_ne_zero A hlog.ne'), Real.log_pow,
    hloghalf] at hlogLower
  linarith

/-- The main logarithmic difference in the prime-power Mertens formula is
`o(1 / sqrt(log x))` for a fixed logarithmic-power cutoff. -/
lemma logPowerCutoff_loglog_sub_mul_sqrt_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun x : ℕ ↦
        2 * (A : ℝ) *
            (Real.log (Real.log (x : ℝ)) /
              Real.sqrt (Real.log (x : ℝ))) +
          2 * Real.log 2 * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (loglog_div_sqrt_log_tendsto_zero.const_mul (2 * (A : ℝ))).add
        (inv_sqrt_log_tendsto_zero.const_mul (2 * Real.log 2))
  apply squeeze_zero'
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        (logPowerCutoff_tendsto_atTop A).eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
        with x hcutle hhalf hcutone hlog
    have hcutpos : (0 : ℝ) < logPowerCutoff A x := by exact_mod_cast hcutone
    have hcutlogle : Real.log (logPowerCutoff A x : ℝ) ≤
        Real.log (x : ℝ) := by
      exact Real.log_le_log hcutpos (by exact_mod_cast hcutle)
    have hcutlogpos : 0 < Real.log (logPowerCutoff A x : ℝ) :=
      (half_pos hlog).trans_le hhalf
    have hloglogle :
        Real.log (Real.log (logPowerCutoff A x : ℝ)) ≤
          Real.log (Real.log (x : ℝ)) :=
      Real.log_le_log hcutlogpos hcutlogle
    exact mul_nonneg (sub_nonneg.mpr hloglogle)
      (Real.sqrt_nonneg _)
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        logPowerCutoff_eventually_log_sub_le A,
        (logPowerCutoff_tendsto_atTop A).eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
        with x hcutle hhalf hlower hcutone hlog
    let X : ℝ := Real.log (x : ℝ)
    let Y : ℝ := Real.log (logPowerCutoff A x : ℝ)
    let D : ℝ := (A : ℝ) * Real.log X + Real.log 2
    have hX : 0 < X := zero_lt_one.trans hlog
    have hlogX : 0 < Real.log X := Real.log_pos hlog
    have hYhalf : X / 2 ≤ Y := by simpa [X, Y] using hhalf
    have hY : 0 < Y := (half_pos hX).trans_le hYhalf
    have hcutpos : (0 : ℝ) < logPowerCutoff A x := by exact_mod_cast hcutone
    have hYX : Y ≤ X := by
      dsimp [X, Y]
      exact Real.log_le_log hcutpos (by exact_mod_cast hcutle)
    have hdiff : X - Y ≤ D := by
      dsimp [X, Y, D] at hlower ⊢
      linarith
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    have hlogratio : Real.log X - Real.log Y ≤ 2 * D / X := by
      rw [← Real.log_div hX.ne' hY.ne']
      calc
        Real.log (X / Y) ≤ X / Y - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hX hY)
        _ = (X - Y) / Y := by field_simp
        _ ≤ D / Y := div_le_div_of_nonneg_right hdiff hY.le
        _ ≤ D / (X / 2) :=
          div_le_div_of_nonneg_left hD (half_pos hX) hYhalf
        _ = 2 * D / X := by field_simp
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
    calc
      (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
          Real.sqrt (Real.log (x : ℝ)) =
          (Real.log X - Real.log Y) * Real.sqrt X := by rfl
      _ ≤ (2 * D / X) * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hlogratio (Real.sqrt_nonneg X)
      _ = 2 * (A : ℝ) * (Real.log X / Real.sqrt X) +
          2 * Real.log 2 * (Real.sqrt X)⁻¹ := by
        dsimp [D]
        field_simp [hsqrt.ne', hX.ne']
        rw [Real.sq_sqrt hX.le]
  · exact hupper

/-- Quantitative prime-power Mertens tail.  For every fixed logarithmic-power
cutoff, the reciprocal tail is `o(1 / sqrt(log x))`. -/
lemma primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        primePowerReciprocalTail x (logPowerCutoff A x) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc, hcbound⟩ := hb.exists_pos
  have hboundX := tendsto_natCast_atTop_atTop.eventually hcbound.bound
  have hboundY :=
    (tendsto_natCast_atTop_atTop.comp (logPowerCutoff_tendsto_atTop A)).eventually
      hcbound.bound
  have hmain := logPowerCutoff_loglog_sub_mul_sqrt_tendsto_zero A
  have hupper : Tendsto
      (fun x : ℕ ↦
        (Real.log (Real.log (x : ℝ)) -
            Real.log (Real.log (logPowerCutoff A x : ℝ))) *
            Real.sqrt (Real.log (x : ℝ)) +
          3 * c * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
    simpa [mul_assoc] using hmain.add
      (inv_sqrt_log_tendsto_zero.const_mul (3 * c))
  apply squeeze_zero' (g := fun x : ℕ ↦
    (Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (logPowerCutoff A x : ℝ))) *
        Real.sqrt (Real.log (x : ℝ)) +
      3 * c * (Real.sqrt (Real.log (x : ℝ)))⁻¹)
  · filter_upwards with x
    exact mul_nonneg (primePowerReciprocalTail_nonneg _ _)
      (Real.sqrt_nonneg _)
  · filter_upwards
      [logPowerCutoff_eventually_le A,
        logPowerCutoff_eventually_log_half_le A,
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
        hboundX, hboundY]
      with x hcutle hhalf hlog hxbound hybound
    let X : ℝ := Real.log (x : ℝ)
    let Y : ℝ := Real.log (logPowerCutoff A x : ℝ)
    let S : ℝ := Real.sqrt X
    let ex : ℝ := primePowerReciprocalUpTo x -
      (Real.log X + b)
    let ey : ℝ := primePowerReciprocalUpTo (logPowerCutoff A x) -
      (Real.log Y + b)
    have hX : 0 < X := by simpa [X] using hlog
    have hYhalf : X / 2 ≤ Y := by simpa [X, Y] using hhalf
    have hY : 0 < Y := (half_pos hX).trans_le hYhalf
    have hS : 0 < S := by simpa [S] using Real.sqrt_pos.2 hX
    have hSsq : S ^ 2 = X := by
      simpa [S] using Real.sq_sqrt hX.le
    have hex : |ex| ≤ c / X := by
      simpa [ex, X, primePowerReciprocalUpTo, Function.comp_def,
        Nat.floor_natCast, norm_inv, Real.norm_eq_abs, abs_of_pos hX,
        div_eq_mul_inv] using hxbound
    have hey : |ey| ≤ c / Y := by
      simpa [ey, Y, primePowerReciprocalUpTo, Function.comp_def,
        Nat.floor_natCast, norm_inv, Real.norm_eq_abs, abs_of_pos hY,
        div_eq_mul_inv] using hybound
    have hexS : |ex| * S ≤ c * S⁻¹ := by
      calc
        |ex| * S ≤ (c / X) * S :=
          mul_le_mul_of_nonneg_right hex hS.le
        _ = c * S⁻¹ := by
          field_simp [hX.ne', hS.ne']
          nlinarith
    have hcY : c / Y ≤ 2 * c / X := by
      calc
        c / Y ≤ c / (X / 2) :=
          div_le_div_of_nonneg_left hc.le (half_pos hX) hYhalf
        _ = 2 * c / X := by field_simp
    have heyS : |ey| * S ≤ 2 * c * S⁻¹ := by
      calc
        |ey| * S ≤ (c / Y) * S :=
          mul_le_mul_of_nonneg_right hey hS.le
        _ ≤ (2 * c / X) * S :=
          mul_le_mul_of_nonneg_right hcY hS.le
        _ = 2 * c * S⁻¹ := by
          field_simp [hX.ne', hS.ne']
          nlinarith
    have herr : (|ex| + |ey|) * S ≤ 3 * c * S⁻¹ := by
      rw [add_mul]
      calc
        |ex| * S + |ey| * S ≤ c * S⁻¹ + 2 * c * S⁻¹ :=
          add_le_add hexS heyS
        _ = 3 * c * S⁻¹ := by ring
    have htail :
        primePowerReciprocalTail x (logPowerCutoff A x) =
          (Real.log X - Real.log Y) + ex - ey := by
      rw [primePowerReciprocalTail_eq_sub hcutle]
      dsimp [ex, ey]
      ring
    rw [htail]
    calc
      ((Real.log X - Real.log Y) + ex - ey) * S ≤
          ((Real.log X - Real.log Y) + |ex| + |ey|) * S := by
        apply mul_le_mul_of_nonneg_right _ hS.le
        linarith [le_abs_self ex, neg_le_abs ey]
      _ = (Real.log X - Real.log Y) * S + (|ex| + |ey|) * S := by ring
      _ ≤ (Real.log X - Real.log Y) * S + 3 * c * S⁻¹ :=
        add_le_add_right herr _
  · exact hupper

/-- The rough-number count, divided by `x` and multiplied by `sqrt(log x)`,
tends to zero. -/
lemma roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ)) *
          Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun x : ℕ ↦
      primePowerReciprocalTail x (logPowerCutoff A x) *
        Real.sqrt (Real.log (x : ℝ)))
  · filter_upwards with x
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hratio :
        ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ) ≤
          primePowerReciprocalTail x (logPowerCutoff A x) := by
      rw [div_le_iff₀ hxR]
      simpa [mul_comm] using
        roughNumbersIn_card_le_mul_tail 1 x (logPowerCutoff A x)
    exact mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)
  · exact primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero A

/-- Ratio form requested by the last-crossing argument: the rough density is
little-oh of `1 / sqrt(log x)`. -/
theorem roughNumbersIn_logPowerCutoff_card_div_inv_sqrt_tendsto_zero
    (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) / (x : ℝ)) /
          (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      atTop (𝓝 0) := by
  have h := roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  field_simp [hsqrt.ne']

/-- Asymptotic notation for the quantitative rough-count estimate. -/
theorem roughNumbersIn_logPowerCutoff_card_isLittleO_div_sqrt
    (A : ℕ) :
    (fun x : ℕ ↦
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ))
      =o[atTop]
        (fun x : ℕ ↦ (x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  have hratio : Tendsto
      (fun x : ℕ ↦
        ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) /
          ((x : ℝ) / Real.sqrt (Real.log (x : ℝ))))
      atTop (𝓝 0) := by
    have h := roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    field_simp [hxR.ne', hsqrt.ne']
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_ge_atTop 2] with x hx
  intro hzero
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  exact ((div_ne_zero hxR.ne' hsqrt.ne') hzero).elim

/-- In particular, eventually the rough count is at most
`x / sqrt(log x)`. -/
theorem eventually_roughNumbersIn_logPowerCutoff_card_le_div_sqrt
    (A : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ) ≤
        (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) := by
  have hsmall :=
    (roughNumbersIn_logPowerCutoff_card_div_mul_sqrt_tendsto_zero A).eventually
      (Iio_mem_nhds zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 2] with x hsmallx hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  rw [div_mul_eq_mul_div, div_lt_iff₀ hxR] at hsmallx
  rw [le_div_iff₀ hsqrt]
  simpa using hsmallx.le

/-! ## Square tails for the exact-correction stage -/

/-- The elementary telescoping majorant `1/n^2 <= 1/(n-1)-1/n`. -/
lemma inv_sq_le_inv_pred_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2)⁻¹ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsub : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have heq : ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp [hnR.ne', hpredR.ne', hnsub]
    ring
  rw [heq]
  refine (inv_le_inv₀ (sq_pos_of_pos hnR) (mul_pos hnR hpredR)).2 ?_
  nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ n by exact_mod_cast (by omega : n - 1 ≤ n)]

/-- The finite integer square tail above `L` is at most `1/L`. -/
lemma sum_Icc_inv_sq_le_inv (L X : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) ≤ (L : ℝ)⁻¹ := by
  by_cases hLX : L < X
  · have hrewrite :
        (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) =
          ∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      have hsets : Icc (L + 1) X = Ico (L + 1) (X + 1) := by
        ext n
        simp
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      have hlen : X + 1 - (L + 1) = X - L := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    rw [hrewrite]
    calc
      (∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
          ∑ i ∈ range (X - L),
            (((L + i : ℕ) : ℝ)⁻¹ - ((L + i + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_assoc] using
          (inv_sq_le_inv_pred_sub_inv (n := L + i + 1) (by omega))
      _ = (L : ℝ)⁻¹ - (X : ℝ)⁻¹ := by
        change (range (X - L)).sum (fun i ↦
          (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) i -
            (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) (i + 1)) = _
        rw [Finset.sum_range_sub']
        simp [Nat.add_sub_of_le hLX.le]
      _ ≤ (L : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg X))
  · have hempty : Icc (L + 1) X = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [hempty, inv_nonneg.mpr (show (0 : ℝ) ≤ L by positivity)]

/-- Square reciprocal mass of prime powers in `(L,X]`. -/
def primePowerSquareTail (X L : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers X L, ((q : ℝ) ^ 2)⁻¹

/-- A logarithmically dilated intermediate cutoff. -/
def logDilate (L : ℕ) : ℕ :=
  L * ⌈Real.log (L : ℝ)⌉₊

/-- The small-prime/large-prime transition used by Martin's exact correction. -/
def naturalLogCutoff (y : ℕ) : ℕ :=
  ⌊Real.log (y : ℝ)⌋₊

lemma primePowerSquareTail_nonneg (X L : ℕ) :
    0 ≤ primePowerSquareTail X L := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (sq_nonneg _)

/-- Split a square tail at an intermediate point `U`.  Below `U` one gains a
factor `1/L` against the Mertens tail; above `U` the full integer square tail
costs only `1/U`. -/
lemma primePowerSquareTail_le_split (X L U : ℕ) (hL : 1 ≤ L) (hU : 1 ≤ U) :
    primePowerSquareTail X L ≤
      (L : ℝ)⁻¹ * primePowerReciprocalTail U L + (U : ℝ)⁻¹ := by
  let S := largePrimePowers X L
  have hsplit :
      primePowerSquareTail X L =
        ∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹ +
          ∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹ := by
    change (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) = _
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q ↦ q ≤ U)]
    simp only [not_le]
  rw [hsplit]
  apply add_le_add
  · calc
      (∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ S.filter (fun q ↦ q ≤ U),
            (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro q hq
        have hLq : L ≤ q := by
          rcases Finset.mem_filter.mp hq with ⟨hqS, -⟩
          exact (mem_largePrimePowers.mp hqS).1.le
        have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hL.trans hLq
        rw [show ((q : ℝ) ^ 2)⁻¹ = (q : ℝ)⁻¹ * (q : ℝ)⁻¹ by
          rw [sq, mul_inv]]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hqpos hLpos).2 (by exact_mod_cast hLq))
          (inv_nonneg.mpr hqpos.le)
      _ ≤ ∑ q ∈ largePrimePowers U L,
          (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hqU⟩
          rw [mem_largePrimePowers] at hqS ⊢
          exact ⟨hqS.1, hqU, hqS.2.2⟩
        · intro q hq hqnot
          positivity
      _ = (L : ℝ)⁻¹ * primePowerReciprocalTail U L := by
        simp [primePowerReciprocalTail, Finset.mul_sum]
  · calc
      (∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ Icc (U + 1) X, ((q : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hUq⟩
          rw [Finset.mem_Icc]
          exact ⟨hUq, (mem_largePrimePowers.mp hqS).2.1⟩
        · intro q hq hqnot
          positivity
      _ ≤ (U : ℝ)⁻¹ := by
        exact sum_Icc_inv_sq_le_inv U X hU

/-- Moving-endpoint form of the prime-power Mertens tail. -/
lemma primePowerReciprocalTail_between_tendsto_zero {L U : ℕ → ℕ}
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ primePowerReciprocalTail (U n) (L n)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hUtop : Tendsto U atTop atTop := by
    exact tendsto_atTop_mono' atTop hLU hLtop
  have hbL := hb.comp hLtop
  have hbU := hb.comp hUtop
  have hsum := hlog.add (hbU.sub hbL)
  have hsum0 : Tendsto
      (fun n : ℕ ↦
        Real.log (Real.log (U n : ℝ)) - Real.log (Real.log (L n : ℝ)) +
          ((primePowerReciprocalUpTo (U n) -
              (Real.log (Real.log (U n : ℝ)) + b)) -
            (primePowerReciprocalUpTo (L n) -
              (Real.log (Real.log (L n : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hLU] with n hle
  rw [primePowerReciprocalTail_eq_sub hle]
  ring

lemma logDilate_eventually_one_le :
    ∀ᶠ L : ℕ in atTop, 1 ≤ logDilate L := by
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hL)
      (Nat.one_le_iff_ne_zero.mp (Nat.one_le_ceil_iff.mpr hlog)))

lemma eventually_le_logDilate :
    ∀ᶠ L : ℕ in atTop, L ≤ logDilate L := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hlog
  exact Nat.le_mul_of_pos_right L (Nat.ceil_pos.mpr hlog)

lemma logDilate_tendsto_atTop : Tendsto logDilate atTop atTop := by
  exact tendsto_atTop_mono' atTop eventually_le_logDilate tendsto_id

lemma ceil_log_ratio_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_ceil_div_atTop.comp tendsto_log_coe_at_top

lemma log_ceil_log_div_log_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) /
        Real.log (L : ℝ)) atTop (𝓝 0) := by
  let ratio : ℕ → ℝ := fun L ↦
    (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ)
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio] using ceil_log_ratio_tendsto_one
  have hlogratio : Tendsto (fun L ↦ Real.log (ratio L)) atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hlogratioDiv : Tendsto
      (fun L ↦ Real.log (ratio L) / Real.log (L : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hsum := hlogratioDiv.add loglog_div_log_tendsto_zero
  have hsum0 : Tendsto
      (fun L : ℕ ↦ Real.log (ratio L) / Real.log (L : ℝ) +
        Real.log (Real.log (L : ℝ)) / Real.log (L : ℝ))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum0.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with L hlog hrat
  have hceilpos : (0 : ℝ) < ⌈Real.log (L : ℝ)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr hlog
  have heq : (⌈Real.log (L : ℝ)⌉₊ : ℝ) = ratio L * Real.log (L : ℝ) := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hlog.ne').symm
  rw [heq, Real.log_mul hrat.ne' hlog.ne']
  ring

lemma log_logDilate_div_log_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ Real.log (logDilate L : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  have hmain : Tendsto
      (fun L : ℕ ↦ (1 : ℝ) +
        Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add log_ceil_log_div_log_tendsto_zero)
  apply hmain.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hceil : 0 < ⌈Real.log (L : ℝ)⌉₊ := Nat.ceil_pos.mpr hlog
  rw [logDilate, Nat.cast_mul,
    Real.log_mul hLR.ne' (by exact_mod_cast hceil.ne')]
  field_simp

lemma logDilate_loglog_sub_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (Real.log (logDilate L : ℝ)) -
        Real.log (Real.log (L : ℝ))) atTop (𝓝 0) := by
  have hratio := log_logDilate_div_log_tendsto_one
  have hlogratio : Tendsto
      (fun L : ℕ ↦ Real.log
        (Real.log (logDilate L : ℝ) / Real.log (L : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  apply hlogratio.congr'
  have hlogDilateTop : Tendsto (fun L ↦ Real.log (logDilate L : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp logDilate_tendsto_atTop)
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogDilateTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hU
  rw [Real.log_div hU.ne' hL.ne']

lemma logDilate_ratio_tendsto_zero :
    Tendsto (fun L : ℕ ↦ (L : ℝ) / logDilate L) atTop (𝓝 0) := by
  have hceilTop : Tendsto (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_ceil_atTop.comp tendsto_log_coe_at_top)
  have hinv := tendsto_inv_atTop_zero.comp hceilTop
  apply hinv.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hceil : (⌈Real.log (L : ℝ)⌉₊ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ceil_pos.mpr hlog).ne'
  simp only [logDilate, Nat.cast_mul]
  dsimp [Function.comp_def]
  field_simp [hLR, hceil]

lemma naturalLogCutoff_tendsto_atTop :
    Tendsto naturalLogCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_log_coe_at_top

lemma primePowerSquareTail_scaled_tendsto_zero
    {X L U : ℕ → ℕ}
    (hLone : ∀ᶠ n : ℕ in atTop, 1 ≤ L n)
    (hUone : ∀ᶠ n : ℕ in atTop, 1 ≤ U n)
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0))
    (hratio : Tendsto (fun n : ℕ ↦ (L n : ℝ) / U n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ (L n : ℝ) * primePowerSquareTail (X n) (L n))
      atTop (𝓝 0) := by
  have hpp := primePowerReciprocalTail_between_tendsto_zero hLU hLtop hlog
  have hupper : Tendsto
      (fun n : ℕ ↦ primePowerReciprocalTail (U n) (L n) +
        (L n : ℝ) / U n) atTop (𝓝 0) := by
    simpa using hpp.add hratio
  apply squeeze_zero'
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (primePowerSquareTail_nonneg _ _)
  · filter_upwards [hLone, hUone] with n hLn hUn
    have hLpos : (0 : ℝ) < L n := by exact_mod_cast hLn
    calc
      (L n : ℝ) * primePowerSquareTail (X n) (L n) ≤
          (L n : ℝ) *
            ((L n : ℝ)⁻¹ * primePowerReciprocalTail (U n) (L n) +
              (U n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (primePowerSquareTail_le_split (X n) (L n) (U n) hLn hUn)
          (Nat.cast_nonneg _)
      _ = primePowerReciprocalTail (U n) (L n) + (L n : ℝ) / U n := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul]
        rfl
  · exact hupper

lemma primePowerSquareTail_nat_scaled_tendsto_zero (X : ℕ → ℕ) :
    Tendsto (fun L : ℕ ↦ (L : ℝ) * primePowerSquareTail (X L) L)
      atTop (𝓝 0) := by
  exact primePowerSquareTail_scaled_tendsto_zero
    (eventually_ge_atTop 1)
    logDilate_eventually_one_le
    eventually_le_logDilate
    tendsto_id
    logDilate_loglog_sub_tendsto_zero
    logDilate_ratio_tendsto_zero

lemma naturalLogCutoff_ratio_tendsto_one :
    Tendsto
      (fun y : ℕ ↦ (naturalLogCutoff y : ℝ) / Real.log (y : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp tendsto_log_coe_at_top

/-- Proposition 7 square-cost estimate in limit form.  Multiplying the finite
prime-power square tail above `floor(log y)` by `log y` still tends to zero. -/
theorem ten_mul_primePowerSquareTail_mul_log_tendsto_zero :
    Tendsto
      (fun y : ℕ ↦
        10 * primePowerSquareTail y (naturalLogCutoff y) * Real.log (y : ℝ))
      atTop (𝓝 0) := by
  let L := naturalLogCutoff
  let U : ℕ → ℕ := fun y ↦ logDilate (L y)
  have hLtop : Tendsto L atTop atTop := naturalLogCutoff_tendsto_atTop
  have hscaled : Tendsto
      (fun y : ℕ ↦ (L y : ℝ) * primePowerSquareTail y (L y))
      atTop (𝓝 0) := by
    apply primePowerSquareTail_scaled_tendsto_zero
    · exact hLtop.eventually (eventually_ge_atTop 1)
    · exact logDilate_eventually_one_le.filter_mono hLtop
    · exact eventually_le_logDilate.filter_mono hLtop
    · exact hLtop
    · exact logDilate_loglog_sub_tendsto_zero.comp hLtop
    · exact logDilate_ratio_tendsto_zero.comp hLtop
  have hreverse : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ)) atTop (𝓝 1) := by
    have hinv := naturalLogCutoff_ratio_tendsto_one.inv₀ one_ne_zero
    have hinv1 : Tendsto
        (fun y : ℕ ↦ ((naturalLogCutoff y : ℝ) / Real.log (y : ℝ))⁻¹)
        atTop (𝓝 1) := by simpa using hinv
    apply hinv1.congr'
    filter_upwards
      [hLtop.eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
        with y hLy hlog
    dsimp [L]
    field_simp
  have hprod := hreverse.mul hscaled
  have hprod0 : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) *
        primePowerSquareTail y (L y)) atTop (𝓝 0) := by
    have hprod' : Tendsto
        (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ) *
          ((L y : ℝ) * primePowerSquareTail y (L y)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards
      [hLtop.eventually (eventually_ge_atTop 1)] with y hLy
    have hLne : (L y : ℝ) ≠ 0 := by exact_mod_cast (by omega : L y ≠ 0)
    field_simp
  simpa [L, mul_assoc, mul_comm, mul_left_comm] using hprod0.const_mul 10

/-- Epsilon form consumed by the exact-correction recursion. -/
theorem eventually_ten_mul_primePowerSquareTail_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      10 * primePowerSquareTail y (naturalLogCutoff y) <
        c / Real.log (y : ℝ) := by
  have hsmall := ten_mul_primePowerSquareTail_mul_log_tendsto_zero.eventually
    (Metric.ball_mem_nhds 0 hc)
  filter_upwards
    [hsmall,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with y hy hlog
  rw [dist_zero_right, Real.norm_eq_abs] at hy
  rw [lt_div_iff₀ hlog]
  exact (le_abs_self _).trans_lt hy

/-- The weighted square tail in the literal finite-sum form used by the recursion. -/
lemma ten_mul_primePowerSquareTail_eq_sum (X L : ℕ) :
    10 * primePowerSquareTail X L =
      ∑ q ∈ largePrimePowers X L, 10 / (q : ℝ) ^ 2 := by
  simp [primePowerSquareTail, Finset.mul_sum, div_eq_mul_inv]

/-- Direct finite-sum form of the Proposition 7 square-cost estimate. -/
theorem eventually_sum_ten_div_primePower_sq_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      (∑ q ∈ largePrimePowers y (naturalLogCutoff y), 10 / (q : ℝ) ^ 2) <
        c / Real.log (y : ℝ) := by
  filter_upwards [eventually_ten_mul_primePowerSquareTail_lt_div_log hc] with y hy
  rw [← ten_mul_primePowerSquareTail_eq_sum]
  exact hy

end

end Erdos285.RoughCounts

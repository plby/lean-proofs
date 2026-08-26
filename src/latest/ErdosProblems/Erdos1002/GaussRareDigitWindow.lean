import ErdosProblems.Erdos1002.GaussDigitAsymptotics
import ErdosProblems.Erdos1002.GaussDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rare one-digit windows under Gauss measure

The unmarked Poisson calculation repeatedly uses the estimate for a block of
large continued-fraction digits.  This file records the block as one exact
interval, computes its Gauss mass without a Taylor-series shorthand, and
proves the general moving-endpoint asymptotic used by Riemann-sum arguments.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

/-- The union of the consecutive first-digit cylinders with digit between
`lo` and `hi`; it is written directly as their telescoped half-open interval.
The intended use has `1 ≤ lo ≤ hi`. -/
def gaussFirstDigitBlock (lo hi : ℕ) : Set ℝ :=
  Ioc (1 / ((hi + 1 : ℕ) : ℝ)) (1 / (lo : ℝ))

/-- Natural-valued version of the first digit.  It agrees with the integer
digit on the Gauss state space, where that digit is positive. -/
def gaussFirstDigitNat (x : ℝ) : ℕ :=
  (gaussFirstDigit x).toNat

theorem gaussFirstDigit_pos_of_mem_unit
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 < gaussFirstDigit x := by
  have hxinv : (1 : ℝ) ≤ x⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hx.1]
    simpa only [inv_one] using! hx.2
  have hfloor : (1 : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by simpa using! hxinv)
  simpa only [gaussFirstDigit] using! lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hfloor

theorem gaussFirstDigitNat_cast
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    (gaussFirstDigitNat x : ℤ) = gaussFirstDigit x := by
  unfold gaussFirstDigitNat
  exact Int.toNat_of_nonneg (gaussFirstDigit_pos_of_mem_unit hx).le

theorem gaussFirstDigitNat_pos
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 < gaussFirstDigitNat x := by
  rw [← Int.ofNat_lt]
  simpa only [Int.ofNat_zero, gaussFirstDigitNat_cast hx] using!
    gaussFirstDigit_pos_of_mem_unit hx

/-- Exact scaled one-digit event used in the rare-event argument. -/
def scaledGaussFirstDigitWindow
    (scale lower upper : ℝ) : Set ℝ :=
  {x | x ∈ Ioc (0 : ℝ) 1 ∧
    lower ≤ scale / (gaussFirstDigitNat x : ℝ) ∧
    scale / (gaussFirstDigitNat x : ℝ) ≤ upper}

private theorem natCeil_scale_div_le_iff
    {scale upper : ℝ} (hupper : 0 < upper)
    {q : ℕ} (hq : 0 < q) :
    ⌈scale / upper⌉₊ ≤ q ↔ scale / (q : ℝ) ≤ upper := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Nat.ceil_le, div_le_iff₀ hupper, div_le_iff₀ hqR]
  ring_nf

private theorem le_natFloor_scale_div_iff
    {scale lower : ℝ} (hscale : 0 < scale) (hlower : 0 < lower)
    {q : ℕ} (hq : 0 < q) :
    q ≤ ⌊scale / lower⌋₊ ↔ lower ≤ scale / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hquot : 0 ≤ scale / lower := (div_pos hscale hlower).le
  rw [Nat.le_floor_iff hquot, le_div_iff₀ hlower, le_div_iff₀ hqR]
  ring_nf

/-- On the Gauss state space, the interval block is exactly the event that
the integer first digit lies between the stated endpoints. -/
theorem mem_gaussFirstDigitBlock_iff_digit_bounds
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    {lo hi : ℕ} (hlo : 0 < lo) :
    x ∈ gaussFirstDigitBlock lo hi ↔
      (lo : ℤ) ≤ gaussFirstDigit x ∧ gaussFirstDigit x ≤ (hi : ℤ) := by
  have hx0 : 0 < x := hx.1
  have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) < ((hi + 1 : ℕ) : ℝ) := by positivity
  unfold gaussFirstDigitBlock gaussFirstDigit
  constructor
  · intro h
    constructor
    · rw [Int.le_floor]
      have hinv := (le_one_div hx0 hloR).1 h.2
      simpa using! hinv
    · rw [Int.floor_le_iff]
      have hinv := (one_div_lt hhiR hx0).1 h.1
      norm_num [Nat.cast_add] at hinv ⊢
      exact hinv
  · rintro ⟨hlow, hupp⟩
    constructor
    · apply (one_div_lt hhiR hx0).2
      have hfloor : ⌊x⁻¹⌋ < (hi : ℤ) + 1 := by omega
      have hinv : x⁻¹ < (((hi : ℤ) + 1 : ℤ) : ℝ) :=
        Int.floor_lt.mp hfloor
      simpa only [one_div, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one] using! hinv
    · apply (le_one_div hx0 hloR).2
      have hinv : (lo : ℝ) ≤ x⁻¹ := Int.le_floor.mp hlow
      simpa only [one_div] using! hinv

/-- Set-level form, including the state-space restriction explicitly. -/
theorem gaussFirstDigitBlock_eq_digitBounds
    {lo hi : ℕ} (hlo : 0 < lo) :
    gaussFirstDigitBlock lo hi =
      {x : ℝ | x ∈ Ioc (0 : ℝ) 1 ∧
        (lo : ℤ) ≤ gaussFirstDigit x ∧ gaussFirstDigit x ≤ (hi : ℤ)} := by
  ext x
  constructor
  · intro hxBlock
    have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
    have hhiR : (0 : ℝ) < ((hi + 1 : ℕ) : ℝ) := by positivity
    have hx0 : 0 < x :=
      (show 1 / ((hi + 1 : ℕ) : ℝ) < x from hxBlock.1) |>.trans'
        (one_div_pos.mpr hhiR)
    have hx1 : x ≤ 1 := by
      exact hxBlock.2.trans ((div_le_one hloR).2 (by exact_mod_cast hlo))
    exact ⟨⟨hx0, hx1⟩,
      (mem_gaussFirstDigitBlock_iff_digit_bounds ⟨hx0, hx1⟩ hlo).1 hxBlock⟩
  · rintro ⟨hxUnit, hxDigits⟩
    exact (mem_gaussFirstDigitBlock_iff_digit_bounds hxUnit hlo).2 hxDigits

/-- The ceiling/floor block is not merely asymptotically equivalent to the
rare value window: for positive scale and endpoints it is exactly the same
event, including all endpoint conventions. -/
theorem gaussFirstDigitBlock_floorCeil_eq_scaledWindow
    {scale lower upper : ℝ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper) :
    gaussFirstDigitBlock ⌈scale / upper⌉₊ ⌊scale / lower⌋₊ =
      scaledGaussFirstDigitWindow scale lower upper := by
  have hupper0 : 0 < upper := hlower.trans hupper
  have hlo : 0 < ⌈scale / upper⌉₊ :=
    Nat.ceil_pos.mpr (div_pos hscale hupper0)
  ext x
  constructor
  · intro hxBlock
    have hxUnit : x ∈ Ioc (0 : ℝ) 1 := by
      have hset := gaussFirstDigitBlock_eq_digitBounds
        (hi := ⌊scale / lower⌋₊) hlo
      rw [hset] at hxBlock
      exact hxBlock.1
    have hdigitsInt :=
      (mem_gaussFirstDigitBlock_iff_digit_bounds hxUnit hlo).1 hxBlock
    have hqpos := gaussFirstDigitNat_pos hxUnit
    have hlowNat : ⌈scale / upper⌉₊ ≤ gaussFirstDigitNat x := by
      exact_mod_cast hdigitsInt.1.trans_eq (gaussFirstDigitNat_cast hxUnit).symm
    have huppNat : gaussFirstDigitNat x ≤ ⌊scale / lower⌋₊ := by
      exact_mod_cast (gaussFirstDigitNat_cast hxUnit).trans_le hdigitsInt.2
    exact ⟨hxUnit,
      (le_natFloor_scale_div_iff hscale hlower hqpos).1 huppNat,
      (natCeil_scale_div_le_iff hupper0 hqpos).1 hlowNat⟩
  · rintro ⟨hxUnit, hlow, hupp⟩
    have hqpos := gaussFirstDigitNat_pos hxUnit
    have hlowNat : ⌈scale / upper⌉₊ ≤ gaussFirstDigitNat x :=
      (natCeil_scale_div_le_iff hupper0 hqpos).2 hupp
    have huppNat : gaussFirstDigitNat x ≤ ⌊scale / lower⌋₊ :=
      (le_natFloor_scale_div_iff hscale hlower hqpos).2 hlow
    apply (mem_gaussFirstDigitBlock_iff_digit_bounds hxUnit hlo).2
    constructor
    · rw [← gaussFirstDigitNat_cast hxUnit]
      exact_mod_cast hlowNat
    · rw [← gaussFirstDigitNat_cast hxUnit]
      exact_mod_cast huppNat

/-- Exact Gauss mass of a consecutive large-digit block. -/
theorem gaussMeasure_real_gaussFirstDigitBlock
    {lo hi : ℕ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    gaussMeasure.real (gaussFirstDigitBlock lo hi) =
      (Real.log (1 + 1 / (lo : ℝ)) -
        Real.log (1 + 1 / ((hi + 1 : ℕ) : ℝ))) / Real.log 2 := by
  have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) < ((hi + 1 : ℕ) : ℝ) := by positivity
  have hends :
      1 / ((hi + 1 : ℕ) : ℝ) ≤ 1 / (lo : ℝ) := by
    apply one_div_le_one_div_of_le hloR
    exact_mod_cast hlohi.trans (Nat.le_succ hi)
  unfold gaussFirstDigitBlock
  exact gaussMeasure_real_Ioc (by positivity) hends
    ((div_le_one hloR).2 (by exact_mod_cast hlo))

/-- The elementary logarithmic core, pulled back along any natural-valued
sequence tending to infinity. -/
theorem tendsto_nat_mul_log_one_add_inv_comp
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto
      (fun n ↦ (q n : ℝ) * Real.log (1 + 1 / (q n : ℝ)))
      atTop (𝓝 1) := by
  have hqR : Tendsto (fun n ↦ (q n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  simpa only [one_div] using!
    (Real.tendsto_mul_log_one_add_div_atTop 1).comp hqR

/-- Reciprocal rounding estimate for a moving ceiling. -/
theorem tendsto_div_natCeil_comp
    {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    Tendsto (fun n ↦ x n / (⌈x n⌉₊ : ℝ)) atTop (𝓝 1) := by
  have hratio : Tendsto (fun n ↦ (⌈x n⌉₊ : ℝ) / x n)
      atTop (𝓝 1) :=
    (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hx
  have hinv : Tendsto (fun n ↦ ((⌈x n⌉₊ : ℝ) / x n)⁻¹)
      atTop (𝓝 1) := by
    simpa using! hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n := hx.eventually_gt_atTop 0
  filter_upwards [hxpos] with n hn
  have hceil : (⌈x n⌉₊ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ceil_pos.mpr hn).ne'
  have hx0 : x n ≠ 0 := hn.ne'
  change ((⌈x n⌉₊ : ℝ) / x n)⁻¹ = x n / (⌈x n⌉₊ : ℝ)
  field_simp

/-- Reciprocal rounding estimate for `floor x + 1`.  The added one records
the exact lower endpoint of the union of consecutive digit cylinders. -/
theorem tendsto_div_natFloor_add_one_comp
    {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    Tendsto (fun n ↦ x n / (((⌊x n⌋₊ + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  have hfloor : Tendsto (fun n ↦ (⌊x n⌋₊ : ℝ) / x n)
      atTop (𝓝 1) :=
    (tendsto_nat_floor_div_atTop (R := ℝ)).comp hx
  have hinvX : Tendsto (fun n ↦ (x n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hx
  have hden : Tendsto
      (fun n ↦ (((⌊x n⌋₊ + 1 : ℕ) : ℝ)) / x n)
      atTop (𝓝 1) := by
    have hsum := hfloor.add hinvX
    have hsum' : Tendsto
        (fun n ↦ (⌊x n⌋₊ : ℝ) / x n + (x n)⁻¹)
        atTop (𝓝 1) := by simpa only [add_zero] using! hsum
    apply hsum'.congr'
    have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n := hx.eventually_gt_atTop 0
    filter_upwards [hxpos] with n hn
    have hx0 : x n ≠ 0 := hn.ne'
    change (⌊x n⌋₊ : ℝ) / x n + (x n)⁻¹ =
      (((⌊x n⌋₊ + 1 : ℕ) : ℝ)) / x n
    push_cast
    field_simp
  have hinv : Tendsto
      (fun n ↦ ((((⌊x n⌋₊ + 1 : ℕ) : ℝ)) / x n)⁻¹)
      atTop (𝓝 1) := by
    simpa using! hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n := hx.eventually_gt_atTop 0
  filter_upwards [hxpos] with n hn
  have hx0 : x n ≠ 0 := hn.ne'
  have hden0 : (((⌊x n⌋₊ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  change ((((⌊x n⌋₊ + 1 : ℕ) : ℝ)) / x n)⁻¹ =
    x n / (((⌊x n⌋₊ + 1 : ℕ) : ℝ))
  field_simp

/-- General rare-block asymptotic.  The assumptions isolate exactly the two
endpoint calculations: `scale/lo → upper` and
`scale/(hi+1) → lower`.  No uniform `O`-notation or unstated rounding fact is
used. -/
theorem tendsto_scaled_gaussFirstDigitBlock
    (scale : ℕ → ℝ) (lo hi : ℕ → ℕ)
    (lower upper : ℝ)
    (hloPos : ∀ᶠ n : ℕ in atTop, 0 < lo n)
    (hlohi : ∀ᶠ n : ℕ in atTop, lo n ≤ hi n)
    (hloTop : Tendsto lo atTop atTop)
    (hhiTop : Tendsto hi atTop atTop)
    (hUpper : Tendsto (fun n ↦ scale n / (lo n : ℝ))
      atTop (𝓝 upper))
    (hLower : Tendsto
      (fun n ↦ scale n / ((hi n + 1 : ℕ) : ℝ))
      atTop (𝓝 lower)) :
    Tendsto
      (fun n ↦ scale n *
        gaussMeasure.real (gaussFirstDigitBlock (lo n) (hi n)))
      atTop (𝓝 ((upper - lower) / Real.log 2)) := by
  have hloCore := tendsto_nat_mul_log_one_add_inv_comp hloTop
  have hhiSuccTop : Tendsto (fun n ↦ hi n + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ Nat.le_add_right (hi n) 1) hhiTop
  have hhiCore := tendsto_nat_mul_log_one_add_inv_comp hhiSuccTop
  have hUpperLog : Tendsto
      (fun n ↦ scale n * Real.log (1 + 1 / (lo n : ℝ)))
      atTop (𝓝 upper) := by
    have hmul := hUpper.mul hloCore
    have hmul' : Tendsto
        (fun n ↦ (scale n / (lo n : ℝ)) *
          ((lo n : ℝ) * Real.log (1 + 1 / (lo n : ℝ))))
        atTop (𝓝 upper) := by
      simpa only [mul_one] using! hmul
    apply hmul'.congr'
    filter_upwards [hloPos] with n hnpos
    have hlo0 : (lo n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    change (scale n / (lo n : ℝ)) *
        ((lo n : ℝ) * Real.log (1 + 1 / (lo n : ℝ))) =
      scale n * Real.log (1 + 1 / (lo n : ℝ))
    field_simp
  have hLowerLog : Tendsto
      (fun n ↦ scale n *
        Real.log (1 + 1 / ((hi n + 1 : ℕ) : ℝ)))
      atTop (𝓝 lower) := by
    have hmul := hLower.mul hhiCore
    have heq :
        (fun n ↦ scale n *
          Real.log (1 + 1 / ((hi n + 1 : ℕ) : ℝ))) =
          fun n ↦ (scale n / ((hi n + 1 : ℕ) : ℝ)) *
            (((hi n + 1 : ℕ) : ℝ) *
              Real.log (1 + 1 / ((hi n + 1 : ℕ) : ℝ))) := by
      funext n
      have hhi0 : (((hi n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
    rw [heq]
    simpa only [mul_one] using! hmul
  have hdiff : Tendsto
      (fun n ↦ scale n *
        (Real.log (1 + 1 / (lo n : ℝ)) -
          Real.log (1 + 1 / ((hi n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (upper - lower)) := by
    convert! hUpperLog.sub hLowerLog using 1
    funext n
    ring
  have hdiv := hdiff.div_const (Real.log 2)
  apply hdiv.congr'
  filter_upwards [hloPos, hlohi] with n hnpos hnorder
  rw [gaussMeasure_real_gaussFirstDigitBlock hnpos hnorder]
  ring

/-- The manuscript's one-point rare-window asymptotic with the actual
ceiling/floor digit endpoints.  If `scale → ∞` and
`0 < lower < upper`, then

`scale * ν_G{ lower ≤ scale/a₁ ≤ upper } → (upper-lower)/log 2`.

The event is represented by the exact consecutive digit block; the previous
set-level theorem identifies it with the corresponding first-digit bounds. -/
theorem tendsto_scaled_gaussFirstDigitBlock_floorCeil
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {lower upper : ℝ} (hlower : 0 < lower) (hupper : lower < upper) :
    Tendsto
      (fun n ↦ scale n * gaussMeasure.real
        (gaussFirstDigitBlock
          ⌈scale n / upper⌉₊ ⌊scale n / lower⌋₊))
      atTop (𝓝 ((upper - lower) / Real.log 2)) := by
  let xu : ℕ → ℝ := fun n ↦ scale n / upper
  let xl : ℕ → ℝ := fun n ↦ scale n / lower
  let lo : ℕ → ℕ := fun n ↦ ⌈xu n⌉₊
  let hi : ℕ → ℕ := fun n ↦ ⌊xl n⌋₊
  have hupper0 : 0 < upper := hlower.trans hupper
  have hxu : Tendsto xu atTop atTop := by
    exact hscale.atTop_div_const hupper0
  have hxl : Tendsto xl atTop atTop := by
    exact hscale.atTop_div_const hlower
  have hloTop : Tendsto lo atTop atTop :=
    tendsto_nat_ceil_atTop.comp hxu
  have hhiTop : Tendsto hi atTop atTop :=
    tendsto_nat_floor_atTop.comp hxl
  have hUpperRatio : Tendsto
      (fun n ↦ scale n / (lo n : ℝ)) atTop (𝓝 upper) := by
    have hcore := tendsto_div_natCeil_comp hxu
    have hmul := (tendsto_const_nhds (x := upper)).mul hcore
    have hmul' : Tendsto (fun n ↦ upper * (xu n / (lo n : ℝ)))
        atTop (𝓝 upper) := by simpa only [mul_one] using! hmul
    apply hmul'.congr'
    filter_upwards [] with n
    dsimp [xu, lo]
    have hu0 : upper ≠ 0 := hupper0.ne'
    ring_nf
    field_simp
  have hLowerRatio : Tendsto
      (fun n ↦ scale n / (((hi n + 1 : ℕ) : ℝ)))
      atTop (𝓝 lower) := by
    have hcore := tendsto_div_natFloor_add_one_comp hxl
    have hmul := (tendsto_const_nhds (x := lower)).mul hcore
    have hmul' : Tendsto
        (fun n ↦ lower * (xl n / (((hi n + 1 : ℕ) : ℝ))))
        atTop (𝓝 lower) := by simpa only [mul_one] using! hmul
    apply hmul'.congr'
    filter_upwards [] with n
    dsimp [xl, hi]
    have hl0 : lower ≠ 0 := hlower.ne'
    ring_nf
    field_simp
  have hloPos : ∀ᶠ n : ℕ in atTop, 0 < lo n :=
    hloTop.eventually_gt_atTop 0
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscale.eventually_gt_atTop 0
  have hratioOrder : ∀ᶠ n : ℕ in atTop,
      scale n / (((hi n + 1 : ℕ) : ℝ)) <
        scale n / (lo n : ℝ) :=
    hLowerRatio.eventually_lt hUpperRatio hupper
  have hlohi : ∀ᶠ n : ℕ in atTop, lo n ≤ hi n := by
    filter_upwards [hloPos, hscalePos, hratioOrder] with n hnlo hnscale hrat
    have hloR : (0 : ℝ) < (lo n : ℝ) := by exact_mod_cast hnlo
    have hhiR : (0 : ℝ) < (((hi n + 1 : ℕ) : ℝ)) := by positivity
    have hcast : (lo n : ℝ) < ((hi n + 1 : ℕ) : ℝ) := by
      rwa [div_lt_div_iff_of_pos_left hnscale hhiR hloR] at hrat
    exact Nat.le_of_lt_succ (by exact_mod_cast hcast)
  have hmain := tendsto_scaled_gaussFirstDigitBlock
    scale lo hi lower upper hloPos hlohi hloTop hhiTop
      hUpperRatio hLowerRatio
  simpa only [lo, hi, xu, xl] using! hmain

end

end Erdos1002

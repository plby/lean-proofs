/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpBridge

/-!
# Outer scales for the Liu--Sawhney gluing argument

The local interval used for a requested first denominator `t` is independent
of `t`.  Its endpoint is

`log N * (log log N)^3 * (log log log N)^20`.

The deliberately generous exponent 20 absorbs all nine powers of the local
`log log` in `sharpS`, as well as the harmless comparisons between the local
and global iterated logarithms.
-/

open Filter Real Asymptotics
open scoped Topology

namespace Erdos294.SharpOuterScales

open Erdos297
open Erdos294.SharpParameters

noncomputable section

/-- The explicit exponent hidden by the published `O(1)`. -/
def outerExponent : ℕ := 20

/-- Real local endpoint in the two-scale construction. -/
def outerScaleReal (N : ℕ) : ℝ :=
  logScale N * logLogScale N ^ 3 * logLogLogScale N ^ outerExponent

/-- Integer local endpoint. -/
def outerScale (N : ℕ) : ℕ := ⌊outerScaleReal N⌋₊

lemma eventually_outerScaleReal_pos :
    ∀ᶠ N : ℕ in atTop, 0 < outerScaleReal N := by
  filter_upwards [eventually_pos_scales] with N h
  exact mul_pos (mul_pos (zero_lt_one.trans h.2.1)
    (pow_pos (zero_lt_one.trans h.2.2.1) 3))
    (pow_pos h.2.2.2 outerExponent)

lemma tendsto_outerScaleReal_atTop : Tendsto outerScaleReal atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_logScale
  filter_upwards [eventually_pos_scales,
      tendsto_logLogLogScale.eventually_ge_atTop 1] with N h hLLL
  have hLL3 : 1 ≤ logLogScale N ^ 3 := one_le_pow₀ h.2.2.1.le
  have hLLL20 : 1 ≤ logLogLogScale N ^ outerExponent :=
    one_le_pow₀ hLLL
  dsimp [outerScaleReal]
  have hLnonneg : 0 ≤ logScale N := (zero_lt_one.trans h.2.1).le
  have hprodNonneg : 0 ≤ logScale N * logLogScale N ^ 3 :=
    mul_nonneg hLnonneg (pow_nonneg (zero_lt_one.trans h.2.2.1).le _)
  calc
    logScale N = logScale N * 1 * 1 := by ring
    _ ≤ logScale N * logLogScale N ^ 3 *
        logLogLogScale N ^ outerExponent := by gcongr

lemma tendsto_outerScale_atTop : Tendsto outerScale atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_outerScaleReal_atTop

lemma eventually_outerScale_bounds :
    ∀ᶠ N : ℕ in atTop,
      outerScaleReal N / 2 ≤ (outerScale N : ℝ) ∧
      (outerScale N : ℝ) ≤ outerScaleReal N ∧
      logScale (outerScale N) ≤ 24 * logLogScale N ∧
      logLogScale (outerScale N) ≤ 5 * logLogLogScale N := by
  have hlocalPos := tendsto_outerScale_atTop.eventually eventually_pos_scales
  filter_upwards [eventually_pos_scales,
      tendsto_logLogLogScale.eventually_ge_atTop 6,
      eventually_outerScaleReal_pos,
      tendsto_outerScaleReal_atTop.eventually_ge_atTop 2,
      hlocalPos] with N h hLLL6 hDpos hDtwo hXpos
  rcases h with ⟨hN, hLone, hLLone, hLLLpos⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hLLLone : 1 ≤ logLogLogScale N := by linarith
  have hLLLleLL : logLogLogScale N ≤ logLogScale N := by
    dsimp [logLogLogScale]
    exact (Real.log_le_sub_one_of_pos hLLpos).trans (by linarith)
  have hfloorLower : outerScaleReal N / 2 ≤ (outerScale N : ℝ) := by
    exact Erdos297.half_le_floor hDtwo
  have hfloorUpper : (outerScale N : ℝ) ≤ outerScaleReal N := by
    exact Nat.floor_le hDpos.le
  have hXnat : 0 < outerScale N := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < outerScaleReal N / 2)
      hfloorLower)
  have hlogD : Real.log (outerScaleReal N) ≤ 24 * logLogScale N := by
    have hlogLLL : Real.log (logLogLogScale N) ≤ logLogLogScale N := by
      exact (Real.log_le_sub_one_of_pos hLLLpos).trans (by linarith)
    have hformula : Real.log (outerScaleReal N) =
        logLogScale N + 3 * logLogLogScale N +
          20 * Real.log (logLogLogScale N) := by
      rw [outerScaleReal, outerExponent,
        Real.log_mul (mul_ne_zero hLpos.ne' (pow_ne_zero 3 hLLpos.ne'))
          (pow_ne_zero 20 hLLLpos.ne'),
        Real.log_mul hLpos.ne' (pow_ne_zero 3 hLLpos.ne'),
        Real.log_pow, Real.log_pow]
      rfl
    rw [hformula]
    nlinarith
  have hlogX : logScale (outerScale N) ≤ 24 * logLogScale N := by
    dsimp [logScale]
    exact (Real.log_le_log (by exact_mod_cast hXnat) hfloorUpper).trans hlogD
  have hlogXpos : 0 < logScale (outerScale N) :=
    zero_lt_one.trans hXpos.2.1
  have htwentyFourLLpos : 0 < 24 * logLogScale N := by positivity
  have hloglogX : logLogScale (outerScale N) ≤
      5 * logLogLogScale N := by
    dsimp [logLogScale]
    calc
      Real.log (logScale (outerScale N)) ≤
          Real.log (24 * logLogScale N) :=
        Real.log_le_log hlogXpos hlogX
      _ = Real.log 24 + logLogLogScale N := by
        rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) hLLpos.ne']
        rfl
      _ ≤ 5 * logLogLogScale N := by
        have hlog24 : Real.log 24 ≤ 23 := by
          convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24) using 1 <;>
            norm_num
        linarith
  exact ⟨hfloorLower, hfloorUpper, hlogX, hloglogX⟩

lemma eventually_sharpS_outerScale_ge_forty_log :
    ∀ᶠ N : ℕ in atTop,
      40 * logScale N ≤ (sharpS (outerScale N) : ℝ) := by
  let A : ℝ := 160 * sharpConstant * 24 ^ 3 * 5 ^ 9
  have hApos : 0 < A := by dsimp [A, sharpConstant]; positivity
  have hlocalPos := tendsto_outerScale_atTop.eventually eventually_pos_scales
  have hlocalS := tendsto_outerScale_atTop.eventually eventually_sharpSReal_ge_two
  filter_upwards [eventually_pos_scales, eventually_outerScale_bounds,
      tendsto_logLogLogScale.eventually_ge_atTop A,
      hlocalPos, hlocalS] with N h hbounds hLLLA hXpos hSXtwo
  rcases h with ⟨hN, hLone, hLLone, hLLLpos⟩
  rcases hbounds with ⟨hXlower, hXupper, hlogX, hloglogX⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hLLLone : 1 ≤ logLogLogScale N := by
    exact le_trans (by norm_num [A, sharpConstant] : (1 : ℝ) ≤ A) hLLLA
  have hlogXpos : 0 < logScale (outerScale N) := zero_lt_one.trans hXpos.2.1
  have hloglogXpos : 0 < logLogScale (outerScale N) :=
    zero_lt_one.trans hXpos.2.2.1
  have hA : A ≤ logLogLogScale N ^ 11 := by
    exact hLLLA.trans (by
      calc
        logLogLogScale N = logLogLogScale N ^ 1 := by ring
        _ ≤ logLogLogScale N ^ 11 := pow_le_pow_right₀ hLLLone (by norm_num))
  have hdenom :
      sharpConstant * logScale (outerScale N) ^ 3 *
          logLogScale (outerScale N) ^ 9 ≤
        sharpConstant * (24 * logLogScale N) ^ 3 *
          (5 * logLogLogScale N) ^ 9 := by
    have hC0 : 0 ≤ sharpConstant := sharpConstant_pos.le
    have h24LL0 : 0 ≤ 24 * logLogScale N := by positivity
    have h5LLL0 : 0 ≤ 5 * logLogLogScale N := by positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogXpos.le hlogX 3) hC0)
      (pow_le_pow_left₀ hloglogXpos.le hloglogX 9)
      (pow_nonneg hloglogXpos.le 9)
      (mul_nonneg hC0 (pow_nonneg h24LL0 3))
  have htarget :
      80 * logScale N *
          (sharpConstant * (24 * logLogScale N) ^ 3 *
            (5 * logLogLogScale N) ^ 9) ≤
        outerScaleReal N / 2 := by
    have hcoeff : 80 * sharpConstant * 24 ^ 3 * 5 ^ 9 ≤
        logLogLogScale N ^ 11 / 2 := by
      dsimp [A] at hA
      linarith
    dsimp [outerScaleReal, outerExponent]
    calc
      80 * logScale N *
          (sharpConstant * (24 * logLogScale N) ^ 3 *
            (5 * logLogLogScale N) ^ 9) =
          (logScale N * logLogScale N ^ 3 *
            logLogLogScale N ^ 9) *
            (80 * sharpConstant * 24 ^ 3 * 5 ^ 9) := by ring
      _ ≤ (logScale N * logLogScale N ^ 3 *
            logLogLogScale N ^ 9) *
            (logLogLogScale N ^ 11 / 2) := by gcongr
      _ = (logScale N * logLogScale N ^ 3 *
            logLogLogScale N ^ 20) / 2 := by ring
  have hreal : 80 * logScale N ≤ sharpSReal (outerScale N) := by
    rw [sharpSReal, le_div_iff₀]
    · calc
        80 * logScale N *
            (sharpConstant * logScale (outerScale N) ^ 3 *
              logLogScale (outerScale N) ^ 9) ≤
            80 * logScale N *
              (sharpConstant * (24 * logLogScale N) ^ 3 *
                (5 * logLogLogScale N) ^ 9) := by gcongr
        _ ≤ outerScaleReal N / 2 := htarget
        _ ≤ (outerScale N : ℝ) := hXlower
    · exact mul_pos (mul_pos sharpConstant_pos (pow_pos hlogXpos 3))
        (pow_pos hloglogXpos 9)
  have hfloor : sharpSReal (outerScale N) / 2 ≤
      (sharpS (outerScale N) : ℝ) := Erdos297.half_le_floor hSXtwo
  linarith

private lemma eventually_four_sharpConstant_log_pow_36_le_nat :
    ∀ᶠ N : ℕ in atTop,
      4 * sharpConstant * logScale N ^ 36 ≤ (N : ℝ) := by
  let C : ℝ := 4 * sharpConstant
  have hC : 0 < C := by dsimp [C, sharpConstant]; positivity
  have hlittle := Real.isLittleO_pow_log_id_atTop (n := 36)
  have hbound := hlittle.bound (inv_pos.mpr hC)
  have hnat := tendsto_natCast_atTop_atTop.eventually hbound
  filter_upwards [hnat, eventually_pos_scales] with N hN hpos
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    simpa [logScale] using zero_le_one.trans hpos.2.1.le
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hlog0,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N), id_eq] at hN
  dsimp [C] at hN
  have hCne : 4 * sharpConstant ≠ 0 := by
    exact (mul_pos (by norm_num) sharpConstant_pos).ne'
  calc
    4 * sharpConstant * logScale N ^ 36 ≤
        4 * sharpConstant * ((4 * sharpConstant)⁻¹ * (N : ℝ)) := by
      gcongr
      simpa [logScale] using hN
    _ = (4 * sharpConstant) * (4 * sharpConstant)⁻¹ * (N : ℝ) := by ring
    _ = (N : ℝ) := by rw [mul_inv_cancel₀ hCne, one_mul]

lemma eventually_two_outerScale_le_sharpS :
    ∀ᶠ N : ℕ in atTop, 2 * outerScale N ≤ sharpS N := by
  filter_upwards [eventually_pos_scales, eventually_logLogScale_le_logScale,
      eventually_outerScale_bounds, eventually_sharpSReal_ge_two,
      eventually_four_sharpConstant_log_pow_36_le_nat] with
      N h hLLle hX hStwo hgrowth
  rcases h with ⟨hN, hLone, hLLone, hLLLpos⟩
  have hLpos : 0 < logScale N := zero_lt_one.trans hLone
  have hLLLleLL : logLogLogScale N ≤ logLogScale N := by
    dsimp [logLogLogScale]
    exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hLLone)).trans (by linarith)
  have hDpow : outerScaleReal N ≤ logScale N ^ 24 := by
    have hLLLleL : logLogLogScale N ≤ logScale N := hLLLleLL.trans hLLle
    dsimp [outerScaleReal, outerExponent]
    calc
      logScale N * logLogScale N ^ 3 * logLogLogScale N ^ 20 ≤
          logScale N * logScale N ^ 3 * logScale N ^ 20 := by
            gcongr
      _ = logScale N ^ 24 := by ring
  have hXpow : (outerScale N : ℝ) ≤ logScale N ^ 24 := hX.2.1.trans hDpow
  have hdenom :
      sharpConstant * logScale N ^ 3 * logLogScale N ^ 9 ≤
        sharpConstant * logScale N ^ 12 := by
    calc
      sharpConstant * logScale N ^ 3 * logLogScale N ^ 9 ≤
          sharpConstant * logScale N ^ 3 * logScale N ^ 9 := by
            have hC0 : 0 ≤ sharpConstant := sharpConstant_pos.le
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (zero_lt_one.trans hLLone).le hLLle 9)
              (mul_nonneg hC0 (pow_nonneg hLpos.le 3))
      _ = sharpConstant * logScale N ^ 12 := by ring
  have hreal : 4 * logScale N ^ 24 ≤ sharpSReal N := by
    rw [sharpSReal, le_div_iff₀]
    · calc
        4 * logScale N ^ 24 *
            (sharpConstant * logScale N ^ 3 * logLogScale N ^ 9) ≤
            4 * logScale N ^ 24 *
              (sharpConstant * logScale N ^ 12) := by gcongr
        _ = 4 * sharpConstant * logScale N ^ 36 := by ring
        _ ≤ (N : ℝ) := hgrowth
    · exact mul_pos (mul_pos sharpConstant_pos (pow_pos hLpos 3))
        (pow_pos (zero_lt_one.trans hLLone) 9)
  have hfloor : sharpSReal N / 2 ≤ (sharpS N : ℝ) :=
    Erdos297.half_le_floor hStwo
  have hcast : ((2 * outerScale N : ℕ) : ℝ) ≤ (sharpS N : ℝ) := by
    push_cast
    calc
      2 * (outerScale N : ℝ) ≤ 2 * logScale N ^ 24 := by gcongr
      _ ≤ sharpSReal N / 2 := by linarith
      _ ≤ (sharpS N : ℝ) := hfloor
  exact_mod_cast hcast

end

end Erdos294.SharpOuterScales

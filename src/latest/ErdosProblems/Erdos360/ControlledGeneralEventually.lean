/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledNumericalEventually
import ErdosProblems.Erdos360.TotientStep

/-!
# Controlled parameters at an arbitrary resolution constant

The final sieve constants are absolute but not numerically normalized.
Consequently the lower-bound constant must be chosen after those constants
are obtained.  This file develops the controlled parameter ledger uniformly
for every fixed positive `c ≤ 1`.
-/

namespace Erdos360

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Exact upper window estimate retaining the small color coefficient. -/
lemma eventually_initialLowerY_sq_lt_scale_mul_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let r := lowerColorCount c n
      let y := initialLowerY n r
      (y : ℝ) ^ 2 <
        (400 / 3 : ℝ) * c *
          (resolutionScale n * Nat.totient n) * Real.log (n : ℝ) := by
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount hc,
    eventually_initialMissingMertensBounds_lowerColorCount hc] with
      n hn hlog hloglog hr3 hMertens
  dsimp only
  let r := lowerColorCount c n
  let y := initialLowerY n r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; omega
  have hscalePos : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR (by exact_mod_cast Nat.totient_pos.mpr hn)))
      (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hloglog) _))
  have hrScale : (r : ℝ) ≤ c * resolutionScale n := by
    simpa [r] using
      (lowerColorCount_bounds hc.le hscalePos.le).1
  have hrScaleOne : (r : ℝ) ≤ resolutionScale n := by
    exact hrScale.trans (by
      simpa using mul_le_mul_of_nonneg_right hc1 hscalePos.le)
  have hphi : (0 : ℝ) ≤ Nat.totient n := by positivity
  have hrphi : (r : ℝ) * Nat.totient n ≤
      c * (resolutionScale n * Nat.totient n) := by
    calc
      (r : ℝ) * Nat.totient n ≤
          (c * resolutionScale n) * Nat.totient n :=
        mul_le_mul_of_nonneg_right hrScale hphi
      _ = c * (resolutionScale n * Nat.totient n) := by ring
  have hscalePhi : resolutionScale n * Nat.totient n ≤
      Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
    resolutionScale_mul_totient_le_rpow_four_thirds hn hlog hloglog
  have hrPow : (r : ℝ) ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
    calc
      (r : ℝ) ≤ resolutionScale n := hrScaleOne
      _ ≤ resolutionScale n * Nat.totient n := by
        have hphiOne : (1 : ℝ) ≤ Nat.totient n := by
          exact_mod_cast Nat.totient_pos.mpr hn
        nlinarith [mul_le_mul_of_nonneg_left hphiOne hscalePos.le]
      _ ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) := hscalePhi
  have hlogr : Real.log (r : ℝ) ≤
      (4 / 3 : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (r : ℝ) ≤
          Real.log (Real.rpow (n : ℝ) (4 / 3 : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hr) hrPow
      _ = (4 / 3 : ℝ) * Real.log (n : ℝ) := Real.log_rpow hnR _
  have hrlog0 : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hright0 : 0 ≤ c * (resolutionScale n * Nat.totient n) := by
    positivity
  have hyWindow := initialLowerY_coarse_bounds hn hr hMertens
  calc
    (y : ℝ) ^ 2 < 100 * r * Nat.totient n * Real.log (r : ℝ) :=
      by simpa [y, r] using hyWindow.2
    _ ≤ 100 * (c * (resolutionScale n * Nat.totient n)) *
        ((4 / 3 : ℝ) * Real.log (n : ℝ)) := by
      have hleft : 100 * (r : ℝ) * Nat.totient n ≤
          100 * (c * (resolutionScale n * Nat.totient n)) := by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hrphi (by norm_num : (0 : ℝ) ≤ 100)
      exact mul_le_mul hleft hlogr hrlog0 (by positivity)
    _ = (400 / 3 : ℝ) * c *
        (resolutionScale n * Nat.totient n) * Real.log (n : ℝ) := by ring

/-- The tight polynomial upper exponent, uniformly for every fixed
`0 < c ≤ 1`. -/
lemma eventually_initialLowerY_lt_rpow_267_400_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      (initialLowerY n (lowerColorCount c n) : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 1200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_initialLowerY_sq_lt_scale_mul_at hc hc1,
    eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    hpTop.eventually (eventually_ge_atTop (160000 : ℝ))] with
      n hySq hn hlog hloglog hpLarge
  dsimp only at hySq
  let y := initialLowerY n (lowerColorCount c n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscalePhi := resolutionScale_mul_totient_le_rpow_four_thirds hn hlog
    hloglog
  have hlogPower : Real.log (n : ℝ) ≤
      1200 * Real.rpow (n : ℝ) (1 / 1200 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 1200 by norm_num)
  have hscalePos : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR (by exact_mod_cast Nat.totient_pos.mpr hn)))
      (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hloglog) _))
  have hscalePhi0 : 0 ≤ resolutionScale n * Nat.totient n := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hlog
  have hySqBound : (y : ℝ) ^ 2 <
      160000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
    calc
      (y : ℝ) ^ 2 < (400 / 3 : ℝ) * c *
          (resolutionScale n * Nat.totient n) * Real.log (n : ℝ) := hySq
      _ ≤ (400 / 3 : ℝ) * 1 *
          (resolutionScale n * Nat.totient n) * Real.log (n : ℝ) := by
        gcongr
      _ ≤ (400 / 3 : ℝ) * 1 *
          Real.rpow (n : ℝ) (4 / 3 : ℝ) * Real.log (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscalePhi (by norm_num)) hlog0
      _ ≤ (400 / 3 : ℝ) * 1 *
          Real.rpow (n : ℝ) (4 / 3 : ℝ) *
            (1200 * Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogPower
          (mul_nonneg (by norm_num)
            (Real.rpow_nonneg hnR.le (4 / 3 : ℝ)))
      _ = 160000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by ring
  have hsplit : Real.rpow (n : ℝ) (267 / 200 : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        (Real.rpow (n : ℝ) (1 / 1200 : ℝ) *
          Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
    calc
      Real.rpow (n : ℝ) (267 / 200 : ℝ) =
          Real.rpow (n : ℝ) (4 / 3 : ℝ) *
            Real.rpow (n : ℝ) (1 / 600 : ℝ) := by
        convert Real.rpow_add hnR (4 / 3 : ℝ) (1 / 600 : ℝ) using 1 <;>
          norm_num
      _ = _ := by
        congr 1
        convert Real.rpow_add hnR (1 / 1200 : ℝ) (1 / 1200 : ℝ) using 1 <;>
          norm_num
  have hySq' : (y : ℝ) ^ 2 < Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    rw [hsplit]
    have hp0 := Real.rpow_pos_of_pos hnR (4 / 3 : ℝ)
    have hp1 := Real.rpow_pos_of_pos hnR (1 / 1200 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hpLarge
      (mul_nonneg hp0.le hp1.le)]
  have hsquare : (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (267 / 200 : ℝ) := by norm_num
  rw [← hsquare] at hySq'
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hp0 : 0 ≤ Real.rpow (n : ℝ) (267 / 400 : ℝ) :=
    Real.rpow_nonneg hnR.le _
  nlinarith

/-- A stronger lower power for the canonical window.  It is still below
the true `n^(2/3-o(1))` scale, but is convenient for mixed upper/lower
power estimates in the sharp pool rooms. -/
lemma eventually_rpow_sixteen_twentyfive_le_initialLowerY_at
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.rpow (n : ℝ) (16 / 25 : ℝ) ≤
        (initialLowerY n (lowerColorCount c n) : ℝ) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (2 / 75 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount hc,
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    resolutionScale_tendsto_atTop.eventually (eventually_ge_atTop (2 / c)),
    hpTop.eventually (eventually_ge_atTop (10 / c)),
    hpTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      n hn hlog hloglog hr3 hMertens hscaleLarge hpLarge hpOne
  let r := lowerColorCount c n
  let y := initialLowerY n r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; omega
  have hscalePos : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR (by exact_mod_cast Nat.totient_pos.mpr hn)))
      (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hloglog) _))
  have hfloor := (lowerColorCount_bounds hc.le hscalePos.le).2
  have hrLower : c * resolutionScale n / 2 ≤ (r : ℝ) := by
    dsimp [r]
    have hhalf : 1 ≤ c * resolutionScale n / 2 := by
      have hcs : (2 : ℝ) ≤ c * resolutionScale n := by
        calc
        (2 : ℝ) = c * (2 / c) := by field_simp [hc.ne']
        _ ≤ c * resolutionScale n :=
          mul_le_mul_of_nonneg_left hscaleLarge hc.le
      nlinarith
    nlinarith
  have hphi0 : (0 : ℝ) ≤ Nat.totient n := by positivity
  have hrphi : (c / 2) * (resolutionScale n * Nat.totient n) ≤
      (r : ℝ) * Nat.totient n := by
    have := mul_le_mul_of_nonneg_right hrLower hphi0
    nlinarith
  have hscaleLower := (resolutionScale_mul_totient_bounds hn hlog hloglog).1
  have hlogr : (1 : ℝ) ≤ Real.log (r : ℝ) := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      nlinarith [Real.log_three_gt_d9]
    exact hlog3.trans (Real.log_le_log (by norm_num)
      (by exact_mod_cast hr3))
  have hyWindow := initialLowerY_coarse_bounds hn hr hMertens
  have hySqLower : (15 * c / 4) *
      (Real.rpow (n : ℝ) (4 / 3 : ℝ) / Real.log (n : ℝ)) ≤
        (y : ℝ) ^ 2 := by
    calc
      (15 * c / 4) *
          (Real.rpow (n : ℝ) (4 / 3 : ℝ) / Real.log (n : ℝ)) ≤
          (15 / 2 : ℝ) *
            ((c / 2) * (resolutionScale n * Nat.totient n)) := by
        have := mul_le_mul_of_nonneg_left hscaleLower hc.le
        nlinarith
      _ ≤ (15 / 2 : ℝ) * ((r : ℝ) * Nat.totient n) :=
        mul_le_mul_of_nonneg_left hrphi (by norm_num)
      _ ≤ (15 / 2 : ℝ) * (r : ℝ) * Nat.totient n * Real.log (r : ℝ) := by
        have hbase0 : 0 ≤ (15 / 2 : ℝ) * (r : ℝ) * Nat.totient n := by
          positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogr hbase0
      _ ≤ (y : ℝ) ^ 2 := by simpa [y, r] using hyWindow.1
  have hlogPower : Real.log (n : ℝ) ≤
      (75 / 2 : ℝ) * Real.rpow (n : ℝ) (2 / 75 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 2 / 75 by norm_num)
  have hpowSplit : Real.rpow (n : ℝ) (4 / 75 : ℝ) =
      Real.rpow (n : ℝ) (2 / 75 : ℝ) *
        Real.rpow (n : ℝ) (2 / 75 : ℝ) := by
    convert Real.rpow_add hnR (2 / 75 : ℝ) (2 / 75 : ℝ) using 1 <;>
      norm_num
  have htargetSq : Real.rpow (n : ℝ) (32 / 25 : ℝ) ≤
      (15 * c / 4) *
        (Real.rpow (n : ℝ) (4 / 3 : ℝ) / Real.log (n : ℝ)) := by
    have hlogPos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
    rw [show (15 * c / 4) *
        (Real.rpow (n : ℝ) (4 / 3 : ℝ) / Real.log (n : ℝ)) =
      ((15 * c / 4) * Real.rpow (n : ℝ) (4 / 3 : ℝ)) /
        Real.log (n : ℝ) by ring]
    apply (le_div_iff₀ hlogPos).2
    have hpowMain : Real.rpow (n : ℝ) (32 / 25 : ℝ) *
        Real.rpow (n : ℝ) (4 / 75 : ℝ) =
          Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
      convert (Real.rpow_add hnR (32 / 25 : ℝ) (4 / 75 : ℝ)).symm using 1 <;>
        norm_num
    calc
      Real.rpow (n : ℝ) (32 / 25 : ℝ) * Real.log (n : ℝ) ≤
          Real.rpow (n : ℝ) (32 / 25 : ℝ) *
            ((75 / 2 : ℝ) * Real.rpow (n : ℝ) (2 / 75 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogPower
          (Real.rpow_nonneg hnR.le _)
      _ ≤ Real.rpow (n : ℝ) (32 / 25 : ℝ) *
          ((15 * c / 4) * Real.rpow (n : ℝ) (4 / 75 : ℝ)) := by
        rw [hpowSplit]
        have hp0 := Real.rpow_nonneg hnR.le (2 / 75 : ℝ)
        have hcLarge : (10 : ℝ) ≤
            c * Real.rpow (n : ℝ) (2 / 75 : ℝ) := by
          calc
            (10 : ℝ) = c * (10 / c) := by field_simp [hc.ne']
            _ ≤ c * Real.rpow (n : ℝ) (2 / 75 : ℝ) :=
              mul_le_mul_of_nonneg_left hpLarge hc.le
        have hcoef : (75 / 2 : ℝ) ≤
            (15 * c / 4) * Real.rpow (n : ℝ) (2 / 75 : ℝ) := by
          nlinarith
        have hmul := mul_le_mul_of_nonneg_right hcoef hp0
        calc
          Real.rpow (n : ℝ) (32 / 25 : ℝ) *
                ((75 / 2 : ℝ) * Real.rpow (n : ℝ) (2 / 75 : ℝ)) ≤
              Real.rpow (n : ℝ) (32 / 25 : ℝ) *
                (((15 * c / 4) * Real.rpow (n : ℝ) (2 / 75 : ℝ)) *
                  Real.rpow (n : ℝ) (2 / 75 : ℝ)) :=
            mul_le_mul_of_nonneg_left hmul
              (Real.rpow_nonneg hnR.le _)
          _ = _ := by ring
      _ = (15 * c / 4) * Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
        calc
          Real.rpow (n : ℝ) (32 / 25 : ℝ) *
              ((15 * c / 4) * Real.rpow (n : ℝ) (4 / 75 : ℝ)) =
              (15 * c / 4) *
                (Real.rpow (n : ℝ) (32 / 25 : ℝ) *
                  Real.rpow (n : ℝ) (4 / 75 : ℝ)) := by ring
          _ = _ := by rw [hpowMain]
  have hsq : (Real.rpow (n : ℝ) (16 / 25 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (32 / 25 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (16 / 25 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (16 / 25 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (n : ℝ) ((16 / 25 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = _ := by norm_num
  have := htargetSq.trans hySqLower
  rw [← hsq] at this
  have hp0 := Real.rpow_nonneg hnR.le (16 / 25 : ℝ)
  have hy0 : (0 : ℝ) ≤ y := by positivity
  nlinarith

/-- The extraction endpoints at a fixed positive color constant. -/
lemma eventually_controlledPrime_endpoint_parameters_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      0 < controlledPrimeU n ∧
      controlledPrimeU n ≤ y ∧
      0 < controlledPrimeB n y ∧
      controlledPrimeB n y ≤ y / controlledPrimeU n ∧
      5 * y * (controlledPrimeU n + 1) ≤ 6 * n ∧
      controlledPrimeU n ≤ controlledPrimeExtractedFloorTwelve n y ∧
      140 * y ≤ n := by
  have hp19Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (19 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hp83Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (83 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hp133Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (133 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    eventually_CFPDiagonalNumericBounds_lowerColorCount hc,
    eventually_three_le_lowerColorCount hc,
    hp19Top.eventually (eventually_ge_atTop (1002 : ℝ)),
    hp83Top.eventually (eventually_ge_atTop (835 : ℝ)),
    hp133Top.eventually (eventually_ge_atTop (140 : ℝ))] with
      n hn hyUpper hMertens hnum hcolors hp19 hp83 hp133
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hUpos := controlledPrimeU_pos hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8pos := Real.rpow_pos_of_pos hnR (1 / 8 : ℝ)
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    nlinarith
  have hthreeFifths : Real.rpow (n : ℝ) (3 / 5 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (19 / 40 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (19 / 40 : ℝ) using 1 <;>
      norm_num
  have hUyR : (controlledPrimeU n : ℝ) < (y : ℝ) := by
    calc
      (controlledPrimeU n : ℝ) <
          1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := hUrough
      _ ≤ Real.rpow (n : ℝ) (3 / 5 : ℝ) := by
        rw [hthreeFifths]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hp19 hp8pos.le
      _ ≤ (y : ℝ) := by simpa [y, colors] using hyLower
  have hUy : controlledPrimeU n ≤ y := by exact_mod_cast hUyR.le
  have hy : 0 < y := hUpos.trans_le hUy
  have hBpos := controlledPrimeB_pos hUy hn
  have hUone : ((controlledPrimeU n + 1 : ℕ) : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    push_cast
    nlinarith
  have h317 : Real.rpow (n : ℝ) (317 / 400 : ℝ) =
      Real.rpow (n : ℝ) (267 / 400 : ℝ) *
        Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    convert Real.rpow_add hnR (267 / 400 : ℝ) (1 / 8 : ℝ) using 1 <;>
      norm_num
  have hnSplitFit : (n : ℝ) =
      Real.rpow (n : ℝ) (317 / 400 : ℝ) *
        Real.rpow (n : ℝ) (83 / 400 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((317 / 400 : ℝ) + (83 / 400 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hfitR : (5 : ℝ) * y * (controlledPrimeU n + 1) < 6 * n := by
    have hyU : (y : ℝ) * ((controlledPrimeU n + 1 : ℕ) : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) *
          (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) :=
      (mul_lt_mul_of_pos_right hyUpper (by positivity)).trans
        (mul_lt_mul_of_pos_left hUone
          (Real.rpow_pos_of_pos hnR (267 / 400 : ℝ)))
    have hp317 := Real.rpow_pos_of_pos hnR (317 / 400 : ℝ)
    have hcoeff : (5010 : ℝ) * Real.rpow (n : ℝ) (317 / 400 : ℝ) ≤
        6 * (Real.rpow (n : ℝ) (317 / 400 : ℝ) *
          Real.rpow (n : ℝ) (83 / 400 : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hp83 hp317.le]
    calc
      (5 : ℝ) * y * (controlledPrimeU n + 1) <
          5010 * Real.rpow (n : ℝ) (317 / 400 : ℝ) := by
        rw [h317]
        nlinarith
      _ ≤ 6 * (Real.rpow (n : ℝ) (317 / 400 : ℝ) *
          Real.rpow (n : ℝ) (83 / 400 : ℝ)) := hcoeff
      _ = 6 * n := by rw [← hnSplitFit]
  have hfit : 5 * y * (controlledPrimeU n + 1) ≤ 6 * n := by
    exact_mod_cast hfitR.le
  have hnSplitLinear : (n : ℝ) =
      Real.rpow (n : ℝ) (267 / 400 : ℝ) *
        Real.rpow (n : ℝ) (133 / 400 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((267 / 400 : ℝ) + (133 / 400 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hlinearR : (140 : ℝ) * y < n := by
    calc
      (140 : ℝ) * y <
          140 * Real.rpow (n : ℝ) (267 / 400 : ℝ) :=
        mul_lt_mul_of_pos_left hyUpper (by norm_num)
      _ ≤ Real.rpow (n : ℝ) (267 / 400 : ℝ) *
          Real.rpow (n : ℝ) (133 / 400 : ℝ) := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hp133
            (Real.rpow_nonneg hnR.le (267 / 400 : ℝ)))
      _ = n := hnSplitLinear.symm
  have hlinear : 140 * y ≤ n := by exact_mod_cast hlinearR.le
  simpa [y, colors] using
    (show 0 < controlledPrimeU n ∧
      controlledPrimeU n ≤ y ∧
      0 < controlledPrimeB n y ∧
      controlledPrimeB n y ≤ y / controlledPrimeU n ∧
      5 * y * (controlledPrimeU n + 1) ≤ 6 * n ∧
      controlledPrimeU n ≤ controlledPrimeExtractedFloorTwelve n y ∧
      140 * y ≤ n from
        ⟨hUpos, hUy, hBpos, controlledPrimeB_le_cutoff n y,
          hfit, controlledPrimeU_le_extractedFloor hy hfit, hlinear⟩)

/-- The logarithmic extraction loss remains negligible at every fixed
positive color constant. -/
lemma eventually_controlledPrime_loss_room_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      20 * y *
        (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤ n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (13 / 160 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  let CL : ℕ := controlledPrimeCells + 2000000
  let CC : ℕ := 33 * CL
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    hpTop.eventually (eventually_ge_atTop ((20 * CC : ℕ) : ℝ))] with
      n hend hyTight hpLarge
  dsimp only at hend ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hyUpper : (y : ℝ) < Real.rpow (n : ℝ) (7 / 10 : ℝ) := by
    exact hyTight.trans_le (Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      (by norm_num : (267 / 400 : ℝ) ≤ 7 / 10))
  have hUpos : 0 < controlledPrimeU n := hend.1
  have hUy : controlledPrimeU n ≤ y := hend.2.1
  have hy : 0 < y := hUpos.trans_le hUy
  have hBpos : 0 < controlledPrimeB n y := hend.2.2.1
  have hBy : controlledPrimeB n y ≤ y := by
    unfold controlledPrimeB
    exact Nat.div_le_self y (controlledPrimeU n)
  have hlogB : (Nat.log 2 (controlledPrimeB n y) : ℝ) ≤
      32 * Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
    have hlogMono : Real.log (controlledPrimeB n y : ℝ) ≤
        Real.log (y : ℝ) :=
      Real.log_le_log (by exact_mod_cast hBpos) (by exact_mod_cast hBy)
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    have hlogPower : Real.log (y : ℝ) ≤
        16 * Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hyR.le
        (show (0 : ℝ) < 1 / 16 by norm_num)
    nlinarith [natLogTwo_cast_le_two_mul_log hBpos]
  have hyQuarterOne : 1 ≤ Real.rpow (y : ℝ) (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy) (by norm_num)
  have hL : (controlledPrimeL y : ℝ) ≤
      CL * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
    have hroot := fourthRootCeil_cast_lt_two_mul_rpow hy
    have hcells : ((controlledPrimeCells - 1 : ℕ) : ℝ) ≤
        controlledPrimeCells * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
      have hcast : ((controlledPrimeCells - 1 : ℕ) : ℝ) ≤
          (controlledPrimeCells : ℝ) := by exact_mod_cast Nat.sub_le _ _
      exact hcast.trans (by
        simpa using mul_le_mul_of_nonneg_left hyQuarterOne
          (by positivity : (0 : ℝ) ≤ controlledPrimeCells))
    calc
      (controlledPrimeL y : ℝ) =
          1000000 * (fourthRootCeil y : ℝ) +
            (controlledPrimeCells - 1 : ℕ) := by
        rw [controlledPrimeL]
        push_cast
        rfl
      _ ≤ 2000000 * Real.rpow (y : ℝ) (1 / 4 : ℝ) +
          controlledPrimeCells * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
        exact add_le_add (by nlinarith) hcells
      _ = CL * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
        dsimp [CL]
        push_cast
        ring
  have hpowFiveSixteenths :
      Real.rpow (y : ℝ) (5 / 16 : ℝ) =
        Real.rpow (y : ℝ) (1 / 4 : ℝ) *
          Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    convert Real.rpow_add hyR (1 / 4 : ℝ) (1 / 16 : ℝ) using 1 <;>
      norm_num
  have hpFiveOne : 1 ≤ Real.rpow (y : ℝ) (5 / 16 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy) (by norm_num)
  have hloss :
      ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) + 1 : ℕ) : ℝ) ≤
        CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
    push_cast
    have hmul := mul_le_mul hL hlogB
      (by positivity : (0 : ℝ) ≤ (Nat.log 2 (controlledPrimeB n y) : ℝ))
      (by positivity : (0 : ℝ) ≤
        CL * Real.rpow (y : ℝ) (1 / 4 : ℝ))
    have hCLone : (1 : ℝ) ≤ CL := by
      exact_mod_cast (show 1 ≤ CL by dsimp [CL]; omega)
    have hprodOne : (1 : ℝ) ≤ CL *
        (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
          Real.rpow (y : ℝ) (1 / 16 : ℝ)) := by
      rw [← hpowFiveSixteenths]
      simpa using mul_le_mul hCLone hpFiveOne
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ CL)
    calc
      (controlledPrimeL y : ℝ) * Nat.log 2 (controlledPrimeB n y) + 1 ≤
          (CL * Real.rpow (y : ℝ) (1 / 4 : ℝ)) *
            (32 * Real.rpow (y : ℝ) (1 / 16 : ℝ)) + 1 :=
        by simpa [add_comm] using add_le_add_right hmul 1
      _ = 32 * (CL * (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
            Real.rpow (y : ℝ) (1 / 16 : ℝ))) + 1 := by ring
      _ ≤ 33 * (CL * (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
            Real.rpow (y : ℝ) (1 / 16 : ℝ))) := by linarith
      _ = CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
        rw [hpowFiveSixteenths]
        dsimp [CC]
        push_cast
        ring
  have hloss0 :
      ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) : ℕ) : ℝ) ≤
        CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
    exact (by exact_mod_cast (Nat.le_add_right
      (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) 1) :
        ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) : ℕ) : ℝ) ≤
          ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) + 1 : ℕ) : ℝ)).trans
      hloss
  have hpowY : (y : ℝ) * Real.rpow (y : ℝ) (5 / 16 : ℝ) =
      Real.rpow (y : ℝ) (21 / 16 : ℝ) := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    calc
      (y : ℝ) * Real.rpow (y : ℝ) (5 / 16 : ℝ) =
          Real.rpow (y : ℝ) 1 * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
        congr 1
        exact (Real.rpow_one (y : ℝ)).symm
      _ = Real.rpow (y : ℝ) (1 + (5 / 16 : ℝ)) :=
        (Real.rpow_add hyR _ _).symm
      _ = Real.rpow (y : ℝ) (21 / 16 : ℝ) := by norm_num
  have hYPow : Real.rpow (y : ℝ) (21 / 16 : ℝ) ≤
      Real.rpow (n : ℝ) (147 / 160 : ℝ) := by
    have hbase : (y : ℝ) ≤ Real.rpow (n : ℝ) (7 / 10 : ℝ) := hyUpper.le
    calc
      Real.rpow (y : ℝ) (21 / 16 : ℝ) ≤
          Real.rpow (Real.rpow (n : ℝ) (7 / 10 : ℝ))
            (21 / 16 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = Real.rpow (n : ℝ) ((7 / 10 : ℝ) * (21 / 16 : ℝ)) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (147 / 160 : ℝ) := by norm_num
  have hnSplit : (n : ℝ) =
      Real.rpow (n : ℝ) (147 / 160 : ℝ) *
        Real.rpow (n : ℝ) (13 / 160 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((147 / 160 : ℝ) + (13 / 160 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hroomR :
      ((20 * y *
        (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) : ℕ) : ℝ) ≤
        (n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hloss0
    push_cast
    rw [hnSplit]
    calc
      (20 : ℝ) * y *
          (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤
          20 * y * (CC * Real.rpow (y : ℝ) (5 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left hloss0 (by positivity)
      _ = (20 * CC) * Real.rpow (y : ℝ) (21 / 16 : ℝ) := by
        rw [← hpowY]
        ring
      _ ≤ (20 * CC) * Real.rpow (n : ℝ) (147 / 160 : ℝ) :=
        mul_le_mul_of_nonneg_left hYPow (by norm_num)
      _ ≤ Real.rpow (n : ℝ) (147 / 160 : ℝ) *
          Real.rpow (n : ℝ) (13 / 160 : ℝ) := by
        norm_num only [Nat.cast_mul] at hpLarge
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (147 / 160 : ℝ))
  exact_mod_cast hroomR

lemma eventually_controlledPrime_root_large_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      12 * controlledPrimeEll ^ 2 ≤ fourthRootCeil
        (initialLowerY n (lowerColorCount c n)) := by
  let H : ℕ := 12 * controlledPrimeEll ^ 2
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    hpTop.eventually (eventually_ge_atTop ((H ^ 4 : ℕ) : ℝ))] with
      n hend hp
  dsimp only at hend ⊢
  let y := initialLowerY n (lowerColorCount c n)
  have hUcast := (controlledPrimeU_cast_bounds n).1
  have hUlargeR : ((H ^ 4 : ℕ) : ℝ) ≤ controlledPrimeU n := by
    have hpnonneg : (0 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  have hUlarge : H ^ 4 ≤ controlledPrimeU n := by exact_mod_cast hUlargeR
  have hyLarge : H ^ 4 ≤ y := hUlarge.trans hend.2.1
  have hy : 0 < y := by omega
  by_contra hroot
  have hrootLt : fourthRootCeil y < H := Nat.lt_of_not_ge hroot
  have hyLt := fourthRootCeil_add_one_pow_four_gt hy
  have hpLe : (fourthRootCeil y + 1) ^ 4 ≤ H ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  omega

lemma eventually_controlledPrime_two_mul_U_le_y_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      2 * controlledPrimeU n ≤ y := by
  have hp19Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (19 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    eventually_CFPDiagonalNumericBounds_lowerColorCount hc,
    eventually_three_le_lowerColorCount hc,
    hp19Top.eventually (eventually_ge_atTop (2005 : ℝ))] with
      n hend hMertens hnum hcolors hp19
  dsimp only at hend ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8pos := Real.rpow_pos_of_pos hnR (1 / 8 : ℝ)
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have htwoU : ((2 * controlledPrimeU n : ℕ) : ℝ) <
      2005 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    push_cast
    nlinarith
  have hsplit : Real.rpow (n : ℝ) (3 / 5 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (19 / 40 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (19 / 40 : ℝ) using 1 <;>
      norm_num
  have htwoUR : ((2 * controlledPrimeU n : ℕ) : ℝ) < (y : ℝ) := by
    calc
      ((2 * controlledPrimeU n : ℕ) : ℝ) <
          2005 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := htwoU
      _ ≤ Real.rpow (n : ℝ) (3 / 5 : ℝ) := by
        rw [hsplit]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hp19 hp8pos.le
      _ ≤ (y : ℝ) := by simpa [y, colors] using hyLower
  exact_mod_cast htwoUR.le

lemma eventually_controlledPrime_strong_yU_room_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      4 * controlledPrimeEll * y * controlledPrimeU n ≤ n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (83 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    hpTop.eventually (eventually_ge_atTop
      ((4 * controlledPrimeEll * 1002 : ℕ) : ℝ))] with
      n hend hyUpper hpLarge
  dsimp only at hend hyUpper ⊢
  let y := initialLowerY n (lowerColorCount c n)
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by nlinarith
  have hyU : (y : ℝ) * controlledPrimeU n <
      Real.rpow (n : ℝ) (267 / 400 : ℝ) *
        (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) :=
    (mul_lt_mul_of_pos_right hyUpper
      (by exact_mod_cast hend.1 : (0 : ℝ) < controlledPrimeU n)).trans
      (mul_lt_mul_of_pos_left hUrough
        (Real.rpow_pos_of_pos hnR (267 / 400 : ℝ)))
  have hpow : Real.rpow (n : ℝ) (267 / 400 : ℝ) *
      Real.rpow (n : ℝ) (1 / 8 : ℝ) =
        Real.rpow (n : ℝ) (317 / 400 : ℝ) := by
    convert (Real.rpow_add hnR (267 / 400 : ℝ) (1 / 8 : ℝ)).symm using 1 <;>
      norm_num
  have hnSplit : (n : ℝ) =
      Real.rpow (n : ℝ) (317 / 400 : ℝ) *
        Real.rpow (n : ℝ) (83 / 400 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((317 / 400 : ℝ) + (83 / 400 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hroomR :
      (((4 * controlledPrimeEll * y * controlledPrimeU n : ℕ) : ℝ)) <
        (n : ℝ) := by
    push_cast
    calc
      (4 : ℝ) * controlledPrimeEll * y * controlledPrimeU n <
          (4 : ℝ) * controlledPrimeEll *
            (Real.rpow (n : ℝ) (267 / 400 : ℝ) *
              (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ))) := by
        simpa [mul_assoc] using mul_lt_mul_of_pos_left hyU
          (by norm_num [controlledPrimeEll] :
            (0 : ℝ) < (4 : ℝ) * controlledPrimeEll)
      _ = ((4 * controlledPrimeEll * 1002 : ℕ) : ℝ) *
          Real.rpow (n : ℝ) (317 / 400 : ℝ) := by
        push_cast
        rw [← hpow]
        ring
      _ ≤ Real.rpow (n : ℝ) (317 / 400 : ℝ) *
          Real.rpow (n : ℝ) (83 / 400 : ℝ) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (317 / 400 : ℝ))
      _ = n := hnSplit.symm
  exact_mod_cast hroomR.le

lemma eventually_controlledPrime_probability_small_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      (4 : ℝ) * (controlledPrimeClassCapTwelve n y + 1) * (2 * y + 1) *
        Real.exp (- ((controlledPrimeL y -
            (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
          (1024 * (controlledPrimeEll : ℝ) ^ 2)) < 1 := by
  let p : ℕ → ℝ := fun n ↦ Real.rpow (n : ℝ) (3 / 20 : ℝ)
  let a : ℝ := (2048 * controlledPrimeEll ^ 2 : ℕ)
  let x : ℕ → ℝ := fun n ↦ p n / a
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < 2048 * controlledPrimeEll ^ 2 by
      norm_num [controlledPrimeEll])
  have hpTop : Tendsto p atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop
  have hxTop : Tendsto x atTop atTop := hpTop.atTop_div_const ha
  have hdecay : Tendsto (fun n : ℕ ↦
      (x n) ^ 14 * Real.exp (-(x n))) atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 14 |>.comp hxTop
  have hscaled : Tendsto (fun n : ℕ ↦
      (192 * a ^ 14) * ((x n) ^ 14 * Real.exp (-(x n))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  have hsmall := hscaled.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    eventually_CFPDiagonalNumericBounds_lowerColorCount hc,
    eventually_three_le_lowerColorCount hc,
    eventually_ge_atTop (1 : ℕ), hsmall] with
      n hend hMertens hnum hcolors hnOne hsmallN
  dsimp only at hend ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hy : 0 < y := hend.1.trans_le hend.2.1
  have hlinear : 140 * y ≤ n := by
    simpa [y, colors] using hend.2.2.2.2.2.2
  have hyn : y ≤ n := by omega
  have hpLower : p n ≤ (fourthRootCeil y : ℝ) := by
    have hbase : Real.rpow (n : ℝ) (3 / 5 : ℝ) ≤ (y : ℝ) := by
      simpa [y, colors] using hyLower
    have hquarter := Real.rpow_le_rpow
      (Real.rpow_nonneg hnR.le (3 / 5 : ℝ)) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hpow : p n =
        Real.rpow (Real.rpow (n : ℝ) (3 / 5 : ℝ)) (1 / 4 : ℝ) := by
      dsimp [p]
      convert Real.rpow_mul hnR.le (3 / 5 : ℝ) (1 / 4 : ℝ) using 1 <;>
        norm_num
    rw [hpow]
    exact hquarter.trans (rpow_one_fourth_le_fourthRootCeil y)
  have hexponent : Real.exp (- ((controlledPrimeL y -
          (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
        (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
      Real.exp (-(x n)) := by
    apply Real.exp_le_exp.mpr
    have hcoef : (1 / a : ℝ) ≤
        1000000 / (1024 * (controlledPrimeEll : ℝ) ^ 2) := by
      dsimp [a]
      norm_num [controlledPrimeEll]
    have hpNonneg : 0 ≤ p n := by dsimp [p]; positivity
    have hrootNonneg : (0 : ℝ) ≤ fourthRootCeil y := by positivity
    have hquot : x n ≤
        (1000000 * fourthRootCeil y : ℕ) /
          (1024 * (controlledPrimeEll : ℝ) ^ 2) := by
      dsimp [x]
      push_cast
      calc
        p n / a = p n * (1 / a : ℝ) := by ring
        _ ≤ (fourthRootCeil y : ℝ) * (1 / a : ℝ) :=
          mul_le_mul_of_nonneg_right hpLower (by positivity)
        _ ≤ (fourthRootCeil y : ℝ) *
            (1000000 / (1024 * (controlledPrimeEll : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcoef hrootNonneg
        _ = (1000000 : ℝ) * fourthRootCeil y /
            (1024 * (controlledPrimeEll : ℝ) ^ 2) := by ring
    rw [show 8 * controlledPrimeEll = controlledPrimeCells by rfl,
      controlledPrimeL_sub_reserve]
    push_cast
    have hneg := neg_le_neg hquot
    norm_num [controlledPrimeEll] at hneg ⊢
    rw [neg_div]
    exact neg_le_neg hneg
  let M := controlledPrimeClassCapTwelve n y
  have hM : M ≤ 5 * n := by
    dsimp [M, controlledPrimeClassCapTwelve]
    exact Nat.div_le_self (5 * n) (4 * y)
  have hMone : M + 1 ≤ 6 * (n + 1) := by omega
  have hyone : 2 * y + 1 ≤ 2 * (n + 1) := by omega
  have hcoefficientNat :
      4 * (M + 1) * (2 * y + 1) ≤ 48 * (n + 1) ^ 2 := by
    calc
      4 * (M + 1) * (2 * y + 1) ≤
          4 * (6 * (n + 1)) * (2 * (n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hMone) hyone
      _ = 48 * (n + 1) ^ 2 := by ring
  have hcoefficient :
      (4 : ℝ) * (M + 1) * (2 * y + 1) ≤
        48 * ((n + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hcoefficientNat
  have hnPlus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hpoly : (n : ℝ) ^ 2 ≤ (p n) ^ 14 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n by exact_mod_cast hnOne)
      (by norm_num : (2 : ℝ) ≤ 21 / 10)
    have hsquare : (n : ℝ) ^ 2 = Real.rpow (n : ℝ) 2 := by
      simpa using (Real.rpow_natCast (n : ℝ) 2).symm
    have hp14 : (p n) ^ 14 = Real.rpow (n : ℝ) (21 / 10 : ℝ) := by
      dsimp [p]
      calc
        (Real.rpow (n : ℝ) (3 / 20 : ℝ)) ^ 14 =
            Real.rpow (Real.rpow (n : ℝ) (3 / 20 : ℝ)) (14 : ℝ) := by
          simpa using (Real.rpow_natCast
            (Real.rpow (n : ℝ) (3 / 20 : ℝ)) 14).symm
        _ = Real.rpow (n : ℝ) ((3 / 20 : ℝ) * 14) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = Real.rpow (n : ℝ) (21 / 10 : ℝ) := by norm_num
    rw [hsquare, hp14]
    exact hmono
  have hxp : (p n) ^ 14 = a ^ 14 * (x n) ^ 14 := by
    dsimp [x]
    field_simp [a]
  have hmajorant :
      (4 : ℝ) * (M + 1) * (2 * y + 1) *
          Real.exp (- ((controlledPrimeL y -
              (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
            (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
        (192 * a ^ 14) * ((x n) ^ 14 * Real.exp (-(x n))) := by
    have hexpNonneg : 0 ≤ Real.exp (-(x n)) := (Real.exp_pos _).le
    calc
      (4 : ℝ) * (M + 1) * (2 * y + 1) *
          Real.exp (- ((controlledPrimeL y -
              (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
            (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
          (4 : ℝ) * (M + 1) * (2 * y + 1) * Real.exp (-(x n)) :=
        mul_le_mul_of_nonneg_left hexponent (by positivity)
      _ ≤ (48 * ((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-(x n)) :=
        mul_le_mul_of_nonneg_right hcoefficient hexpNonneg
      _ ≤ (192 * (n : ℝ) ^ 2) * Real.exp (-(x n)) := by
        apply mul_le_mul_of_nonneg_right _ hexpNonneg
        calc
          48 * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 48 * (2 * (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hnPlus 2) (by norm_num)
          _ = 192 * (n : ℝ) ^ 2 := by ring
      _ ≤ (192 * (p n) ^ 14) * Real.exp (-(x n)) := by gcongr
      _ = (192 * a ^ 14) * ((x n) ^ 14 * Real.exp (-(x n))) := by
        rw [hxp]
        ring
  exact hmajorant.trans_lt (by simpa [x] using hsmallN)

lemma eventually_controlledPrimeTwelve_choice_numerics_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      ControlledPrimeTwelveChoiceNumerics n
        (initialLowerY n (lowerColorCount c n)) := by
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_controlledPrime_loss_room_at hc hc1] with n hend hloss
  dsimp only at hend hloss ⊢
  let y := initialLowerY n (lowerColorCount c n)
  have hn : 0 < n := by
    have hU := hend.1
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hU
  have hy : 0 < y := hend.1.trans_le hend.2.1
  refine ⟨hend.1, hend.2.1, hend.2.2.1, hend.2.2.2.1,
    controlledPrime_loss_room hy hloss, hend.2.2.2.2.2.1,
    controlledPrime_unused_of_linear_room hy hend.2.2.2.2.2.2, ?_⟩
  intro d hd hdU
  exact ⟨extracted_scale_le_controlledFloor hy hdU hend.2.2.2.2.1,
    controlled_endpoint_quotient_le_two_mul_U hn hd⟩

lemma eventually_controlledPrime_scalarPostRooms_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      ControlledPrimeScalarPostRooms n
        (initialLowerY n (lowerColorCount c n)) := by
  have hp8Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_controlledPrime_root_large_at hc hc1,
    eventually_controlledPrime_loss_room_at hc hc1,
    eventually_controlledPrime_two_mul_U_le_y_at hc hc1,
    eventually_controlledPrime_strong_yU_room_at hc hc1,
    eventually_controlledPrime_probability_small_at hc hc1,
    hp8Top.eventually
      (eventually_ge_atTop (controlledPrimeEll : ℝ))] with
      n hchoice hend hroot hloss htwo hstrong hprob hp8
  dsimp only at hchoice hend hroot hloss htwo hstrong hprob ⊢
  let y := initialLowerY n (lowerColorCount c n)
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at hp8
  have hUlargeR : (controlledPrimeEll : ℝ) ≤ controlledPrimeU n := by
    have hcast := (controlledPrimeU_cast_bounds n).1
    have hpnonneg : (0 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  have hUlarge : controlledPrimeEll ≤ controlledPrimeU n := by
    exact_mod_cast hUlargeR
  have hybig : 2 * controlledPrimeEll ≤ y :=
    (Nat.mul_le_mul_left 2 hUlarge).trans htwo
  have hBtwo : 2 ≤ controlledPrimeB n y := by
    unfold controlledPrimeB
    apply (Nat.le_div_iff_mul_le hchoice.U_pos).2
    simpa [mul_comm] using htwo
  have hlog : 1 ≤ Nat.log 2 (controlledPrimeB n y) := by
    have := Nat.log_pos (by norm_num : 1 < 2) hBtwo
    omega
  exact controlledPrime_scalarRooms_of_growth hchoice
    hend.2.2.2.2.2.2 hroot hlog hloss hybig hstrong hprob

/-- Canonical truthful numerical ledger at a selectable lower-bound
constant. -/
def CanonicalControlledPrimeNumericalLedgerAt (c : ℝ) (n : ℕ) : Prop :=
  let y := initialLowerY n (lowerColorCount c n)
  CFPControlledPrimeNumericalLedger n y
    (controlledPrimeU n) (controlledPrimeB n y) (controlledPrimeL y)
    (controlledPrimeClassCapTwelve n y)
    (controlledPrimeExtractedFloorTwelve n y) controlledPrimeEll

theorem eventually_canonicalControlledPrimeNumericalLedger_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop, CanonicalControlledPrimeNumericalLedgerAt c n := by
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_controlledPrime_scalarPostRooms_at hc hc1] with
      n hchoice hroom
  exact canonicalControlledPrimeNumericalLedger_of_post hchoice
    (controlledPrimePostEstimates_of_scalarRooms hchoice hroom)

end Erdos360

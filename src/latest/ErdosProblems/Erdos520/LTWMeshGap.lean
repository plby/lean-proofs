import ErdosProblems.Erdos520.LTWDyadicInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Summability of the LTW dyadic interpolation cost

The maximal fourth-moment estimate leaves one deterministic series.  This
file bounds its terms by a convergent p-series.  The deliberately generous
constants keep the proof insensitive to floors and dyadic padding.
-/

private theorem eventually_ltwPaddedEndpoint_log_le :
    ∀ᶠ i : ℕ in atTop,
      Real.log
          (ltwRademacherTestPoint i +
            ltwDyadicLength
              (ltwRademacherTestPoint (i + 1) -
                ltwRademacherTestPoint i) : ℝ) ≤
        9 * Real.log (ltwRademacherTestPoint (i + 1) : ℝ) := by
  have htest : Tendsto (fun i : ℕ ↦ ltwRademacherTestPoint (i + 1))
      atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [eventually_ltwPaddedEndpoint_le_nine_mul,
      htest.eventually (eventually_ge_atTop 3)] with i hendpoint hb
  let x : ℝ := (ltwRademacherTestPoint i : ℝ) +
    (ltwDyadicLength
      (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i) : ℝ)
  let b : ℝ := ltwRademacherTestPoint (i + 1)
  have hbR : (3 : ℝ) ≤ b := by
    dsimp only [b]
    exact_mod_cast hb
  have hlogb : 1 ≤ Real.log b := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans hbR
  have hPpos : 0 < ltwDyadicLength
      (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i) := by
    unfold ltwDyadicLength
    positivity
  have hxpos : 0 < x := by
    dsimp only [x]
    exact add_pos_of_nonneg_of_pos (by positivity) (by exact_mod_cast hPpos)
  have hxb : x ≤ 9 * b := by
    simpa only [x, b] using! hendpoint
  have hlogmono : Real.log x ≤ Real.log (9 * b) :=
    Real.log_le_log hxpos hxb
  have hlogNine : Real.log (9 : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    norm_num at h ⊢
    exact h
  change Real.log x ≤ 9 * Real.log b
  calc
    Real.log x ≤ Real.log (9 * b) := hlogmono
    _ = Real.log 9 + Real.log b := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    _ ≤ 8 + Real.log b := by linarith
    _ ≤ 9 * Real.log b := by nlinarith

private theorem ltw_gap_rpow_cube_le_thirteen_tenths_square
    (i : ℕ) (hi : 1 ≤ i) :
    ((i : ℝ) ^ (-(9 / 10 : ℝ))) ^ 3 ≤
      ((i : ℝ) ^ (-(13 / 10 : ℝ))) ^ 2 := by
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le hiR (by norm_num)

noncomputable def ltwMeshFourthMomentConstant : ℝ :=
  (8 : ℝ) ^ 3 * 9 * 18 ^ 80 + 1

theorem ltwMeshFourthMomentConstant_pos :
    0 < ltwMeshFourthMomentConstant := by
  unfold ltwMeshFourthMomentConstant
  positivity

private theorem eventually_ltwFourthMomentBudget_gap_le :
    ∀ᶠ i : ℕ in atTop,
      ltwFourthMomentBudget
          (ltwDyadicLength
            (ltwRademacherTestPoint (i + 1) -
              ltwRademacherTestPoint i))
          (ltwRademacherTestPoint i +
            ltwDyadicLength
              (ltwRademacherTestPoint (i + 1) -
                ltwRademacherTestPoint i)) ≤
        ltwMeshFourthMomentConstant *
          (ltwRademacherTestPoint (i + 1) : ℝ) ^ 2 *
          (i : ℝ) ^ (-(13 / 10 : ℝ)) *
          Real.log (ltwRademacherTestPoint (i + 1) : ℝ) ^ 40 := by
  have htest : Tendsto (fun i : ℕ ↦ ltwRademacherTestPoint (i + 1))
      atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [eventually_ltwDyadicLength_gap_cast_le,
      eventually_ltwPaddedEndpoint_le_nine_mul,
      eventually_ltwPaddedEndpoint_log_le,
      htest.eventually (eventually_ge_atTop 3),
      eventually_ge_atTop (1 : ℕ)] with i hP hx hlog hb hi
  let a : ℕ := ltwRademacherTestPoint i
  let b : ℕ := ltwRademacherTestPoint (i + 1)
  let L : ℕ := b - a
  let P : ℕ := ltwDyadicLength L
  let x : ℕ := a + P
  let q : ℝ := (i : ℝ) ^ (-(9 / 10 : ℝ))
  let r : ℝ := (i : ℝ) ^ (-(13 / 10 : ℝ))
  let C : ℝ := (8 : ℝ) ^ 3 * 9 * 18 ^ 80
  let D : ℝ := C + 1
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hab : a ≤ b := ltwRademacherTestPoint_mono (Nat.le_add_right i 1)
  have hLP : L ≤ P := le_ltwDyadicLength L
  have hbxNat : b ≤ x := by
    calc
      b = a + L := (Nat.add_sub_of_le hab).symm
      _ ≤ a + P := Nat.add_le_add_left hLP a
      _ = x := rfl
  have hbx : (b : ℝ) ≤ (x : ℝ) := by exact_mod_cast hbxNat
  have hbthree : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hxthree : (3 : ℝ) ≤ (x : ℝ) :=
    hbthree.trans hbx
  have hlogb : 0 ≤ Real.log (b : ℝ) :=
    Real.log_nonneg (by linarith [hbthree])
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by linarith)
  have hP' : (P : ℝ) ≤ 8 * (b : ℝ) * q := by
    simpa only [P, L, a, b, q] using! hP
  have hx' : (x : ℝ) ≤ 9 * (b : ℝ) := by
    simpa only [x, P, L, a, b, Nat.cast_add] using! hx
  have hlog' : Real.log (x : ℝ) ≤ 9 * Real.log (b : ℝ) := by
    simpa only [x, P, L, a, b, Nat.cast_add] using! hlog
  have htwoLog : 2 * Real.log (x : ℝ) ≤
      18 * Real.log (b : ℝ) := by linarith
  have hq : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hinside :
      (P : ℝ) ^ 3 *
          ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80) ≤
        C * (b : ℝ) ^ 4 * q ^ 3 * Real.log (b : ℝ) ^ 80 := by
    calc
      (P : ℝ) ^ 3 *
          ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80) ≤
          (8 * (b : ℝ) * q) ^ 3 *
            ((9 * (b : ℝ)) *
              (18 * Real.log (b : ℝ)) ^ 80) := by
        gcongr
      _ = C * (b : ℝ) ^ 4 * q ^ 3 * Real.log (b : ℝ) ^ 80 := by
        dsimp only [C]
        ring
  have hqpow : q ^ 3 ≤ r ^ 2 := by
    simpa only [q, r] using!
      ltw_gap_rpow_cube_le_thirteen_tenths_square i hi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCDsq : C ≤ D ^ 2 := by
    dsimp only [D]
    nlinarith [sq_nonneg C]
  have hmajor :
      C * (b : ℝ) ^ 4 * q ^ 3 * Real.log (b : ℝ) ^ 80 ≤
        (D * (b : ℝ) ^ 2 * r * Real.log (b : ℝ) ^ 40) ^ 2 := by
    calc
      C * (b : ℝ) ^ 4 * q ^ 3 * Real.log (b : ℝ) ^ 80 ≤
          D ^ 2 * (b : ℝ) ^ 4 * r ^ 2 *
            Real.log (b : ℝ) ^ 80 := by
        gcongr
      _ = (D * (b : ℝ) ^ 2 * r *
          Real.log (b : ℝ) ^ 40) ^ 2 := by ring
  unfold ltwFourthMomentBudget
  rw [Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg hD (sq_nonneg _)) hr)
      (pow_nonneg hlogb 40)
  · exact hinside.trans hmajor

private theorem eventually_ltwInterpolationCost_le_logPower :
    ∀ᶠ i : ℕ in atTop,
      ltwDyadicInterpolationCost i ≤
        4096 * ltwMeshFourthMomentConstant *
          (i : ℝ) ^ (-(13 / 10 : ℝ)) *
          Real.log (ltwRademacherTestPoint (i + 1) : ℝ) ^ 44 := by
  have htest : Tendsto (fun i : ℕ ↦ ltwRademacherTestPoint (i + 1))
      atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [eventually_ltwFourthMomentBudget_gap_le,
      htest.eventually (eventually_ge_atTop 3)] with i hbudget hb
  let a : ℕ := ltwRademacherTestPoint i
  let b : ℕ := ltwRademacherTestPoint (i + 1)
  let L : ℕ := b - a
  let P : ℕ := ltwDyadicLength L
  let x : ℕ := a + P
  let r : ℝ := (i : ℝ) ^ (-(13 / 10 : ℝ))
  let D : ℝ := ltwMeshFourthMomentConstant
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hsqrtb : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.2 hbpos
  have hscale : 0 < Real.sqrt (b : ℝ) / Real.log (b : ℝ) :=
    div_pos hsqrtb hlogb
  have hbudget' : ltwFourthMomentBudget P x ≤
      D * (b : ℝ) ^ 2 * r * Real.log (b : ℝ) ^ 40 := by
    simpa only [a, b, L, P, x, r, D] using! hbudget
  have hscaled :
      (4096 * ltwFourthMomentBudget P x) /
          (Real.sqrt (b : ℝ) / Real.log (b : ℝ)) ^ 4 ≤
        (4096 * (D * (b : ℝ) ^ 2 * r *
          Real.log (b : ℝ) ^ 40)) /
          (Real.sqrt (b : ℝ) / Real.log (b : ℝ)) ^ 4 := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hbudget' (by norm_num)
    · exact (pow_pos hscale 4).le
  have hsqrtFour : Real.sqrt (b : ℝ) ^ 4 = (b : ℝ) ^ 2 := by
    calc
      Real.sqrt (b : ℝ) ^ 4 = (Real.sqrt (b : ℝ) ^ 2) ^ 2 := by ring
      _ = (b : ℝ) ^ 2 := by rw [Real.sq_sqrt hbpos.le]
  unfold ltwDyadicInterpolationCost
  dsimp only [a, b, L, P, x, r, D]
  unfold ltwInterpolationScale
  calc
    (4096 * ltwFourthMomentBudget P x) /
        (Real.sqrt (b : ℝ) / Real.log (b : ℝ)) ^ 4 ≤
      (4096 * (D * (b : ℝ) ^ 2 * r *
        Real.log (b : ℝ) ^ 40)) /
        (Real.sqrt (b : ℝ) / Real.log (b : ℝ)) ^ 4 := hscaled
    _ = 4096 * D * r * Real.log (b : ℝ) ^ 44 := by
      rw [div_pow, hsqrtFour]
      field_simp

private theorem eventually_ltw_log_testPoint_pow_le :
    ∀ᶠ i : ℕ in atTop,
      Real.log (ltwRademacherTestPoint (i + 1) : ℝ) ^ 44 ≤
        (2 : ℝ) ^ 44 * (i : ℝ) ^ (3 / 20 : ℝ) := by
  have htest : Tendsto (fun i : ℕ ↦ ltwRademacherTestPoint (i + 1))
      atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [htest.eventually (eventually_ge_atTop 3),
      eventually_ge_atTop (1 : ℕ)] with i hb hi
  let b : ℕ := ltwRademacherTestPoint (i + 1)
  let p : ℝ := 1 / 350
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hlogb : 0 ≤ Real.log (b : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hfloor : (b : ℝ) ≤
      Real.exp (((i + 1 : ℕ) : ℝ) ^ p) := by
    dsimp only [b]
    rw [ltwRademacherTestPoint_eq]
    exact Nat.floor_le (Real.exp_pos _).le
  have hlog : Real.log (b : ℝ) ≤
      ((i + 1 : ℕ) : ℝ) ^ p := by
    calc
      Real.log (b : ℝ) ≤
          Real.log (Real.exp (((i + 1 : ℕ) : ℝ) ^ p)) :=
        Real.log_le_log hbpos hfloor
      _ = ((i + 1 : ℕ) : ℝ) ^ p := Real.log_exp _
  have hiTwo : (((i + 1 : ℕ) : ℝ)) ≤ 2 * (i : ℝ) := by
    push_cast
    linarith
  have hroot : (((i + 1 : ℕ) : ℝ)) ^ p ≤
      2 * (i : ℝ) ^ p := by
    calc
      (((i + 1 : ℕ) : ℝ)) ^ p ≤ (2 * (i : ℝ)) ^ p :=
        Real.rpow_le_rpow (by positivity) hiTwo (by dsimp [p]; positivity)
      _ = (2 : ℝ) ^ p * (i : ℝ) ^ p := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ 2 * (i : ℝ) ^ p := by
        exact mul_le_mul_of_nonneg_right
          (by
            simpa only [Real.rpow_one] using!
              Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
                (show p ≤ 1 by norm_num [p]))
          (Real.rpow_nonneg (by positivity) _)
  have hlogroot : Real.log (b : ℝ) ≤ 2 * (i : ℝ) ^ p :=
    hlog.trans hroot
  have hpow : Real.log (b : ℝ) ^ 44 ≤
      (2 * (i : ℝ) ^ p) ^ 44 :=
    pow_le_pow_left₀ hlogb hlogroot 44
  calc
    Real.log (b : ℝ) ^ 44 ≤ (2 * (i : ℝ) ^ p) ^ 44 := hpow
    _ = (2 : ℝ) ^ 44 * (i : ℝ) ^ (p * 44) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ (2 : ℝ) ^ 44 * (i : ℝ) ^ (3 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hiR (by norm_num [p]))
        (pow_nonneg (by norm_num) 44)

noncomputable def ltwMeshCostConstant : ℝ :=
  4096 * ltwMeshFourthMomentConstant * (2 : ℝ) ^ 44

theorem ltwMeshCostConstant_nonneg : 0 ≤ ltwMeshCostConstant := by
  unfold ltwMeshCostConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) ltwMeshFourthMomentConstant_pos.le)
    (pow_nonneg (by norm_num) 44)

theorem eventually_ltwDyadicInterpolationCost_le_pSeries :
    ∀ᶠ i : ℕ in atTop,
      ltwDyadicInterpolationCost i ≤
        ltwMeshCostConstant * (i : ℝ) ^ (-(23 / 20 : ℝ)) := by
  filter_upwards [eventually_ltwInterpolationCost_le_logPower,
      eventually_ltw_log_testPoint_pow_le,
      eventually_ge_atTop (1 : ℕ)] with i hcost hlog hi
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hr : 0 ≤ (i : ℝ) ^ (-(13 / 10 : ℝ)) :=
    Real.rpow_nonneg hiR.le _
  calc
    ltwDyadicInterpolationCost i ≤
        4096 * ltwMeshFourthMomentConstant *
          (i : ℝ) ^ (-(13 / 10 : ℝ)) *
          Real.log (ltwRademacherTestPoint (i + 1) : ℝ) ^ 44 := hcost
    _ ≤ 4096 * ltwMeshFourthMomentConstant *
          (i : ℝ) ^ (-(13 / 10 : ℝ)) *
          ((2 : ℝ) ^ 44 * (i : ℝ) ^ (3 / 20 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlog
        (mul_nonneg
          (mul_nonneg (by norm_num) ltwMeshFourthMomentConstant_pos.le) hr)
    _ = ltwMeshCostConstant * (i : ℝ) ^ (-(23 / 20 : ℝ)) := by
      unfold ltwMeshCostConstant
      rw [show
        4096 * ltwMeshFourthMomentConstant *
              (i : ℝ) ^ (-(13 / 10 : ℝ)) *
              ((2 : ℝ) ^ 44 * (i : ℝ) ^ (3 / 20 : ℝ)) =
            (4096 * ltwMeshFourthMomentConstant * (2 : ℝ) ^ 44) *
              ((i : ℝ) ^ (-(13 / 10 : ℝ)) *
                (i : ℝ) ^ (3 / 20 : ℝ)) by ring,
        ← Real.rpow_add hiR]
      norm_num

/-- The explicit deterministic cost left by the maximal fourth-moment
argument is summable. -/
theorem summable_ltwDyadicInterpolationCost :
    Summable ltwDyadicInterpolationCost := by
  apply ((Real.summable_nat_rpow.mpr
      (by norm_num : (-(23 / 20 : ℝ)) < -1)).mul_left
      ltwMeshCostConstant).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ltwDyadicInterpolationCost_le_pSeries]
    with i hi
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (ltwDyadicInterpolationCost_nonneg i)] using! hi

/-- Unconditional LTW interpolation for the Rademacher multiplicative
function, proved from the internal fourth-moment estimate. -/
theorem LauTenenbaumWuRademacherInterpolation_unconditional :
    LauTenenbaumWuRademacherInterpolation :=
  LauTenenbaumWuRademacherInterpolation_of_dyadicCost
    summable_ltwDyadicInterpolationCost

end Problem520
end Erdos

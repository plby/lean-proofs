import ErdosProblems.Erdos1038.TaoUpperTwoAtomTrial
import ErdosProblems.Erdos1038.RationalInterval

/-!
# Checked interval interface for Tao's first upper-bound range

The remaining scalar comparison in the two-atom range is expressed as the
positivity of a product-of-logs gap.  This file gives a compositional
rational-interval enclosure for that gap.  Any subsequent finite cover only
has to evaluate the executable interval operations and check that the final
lower endpoint is positive.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseOneGap (t : ℝ) : ℝ :=
  Real.log (t + 1) * Real.log (taoUpperEdge - (t - 1)) -
    (-Real.log (t - 1)) * (-Real.log (taoUpperEdge - (t + 1)))

def taoCaseOneGapDerivative (t : ℝ) : ℝ :=
  Real.log (taoUpperEdge - (t - 1)) / (t + 1) -
    Real.log (t + 1) / (taoUpperEdge - (t - 1)) -
    Real.log (taoUpperEdge - (t + 1)) / (t - 1) +
    Real.log (t - 1) / (taoUpperEdge - (t + 1))

theorem hasDerivAt_taoCaseOneGap {t : ℝ}
    (hleft : t - 1 ≠ 0) (hright : t + 1 ≠ 0)
    (hfarLeft : taoUpperEdge - (t - 1) ≠ 0)
    (hfarRight : taoUpperEdge - (t + 1) ≠ 0) :
    HasDerivAt taoCaseOneGap (taoCaseOneGapDerivative t) t := by
  have hlogLeft : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1))
      (1 / (t - 1)) t := by
    simpa only [one_div] using! ((hasDerivAt_id t).sub_const 1).log hleft
  have hlogRight : HasDerivAt (fun x : ℝ ↦ Real.log (x + 1))
      (1 / (t + 1)) t := by
    simpa only [one_div] using! ((hasDerivAt_id t).add_const 1).log hright
  have hlogFarLeft : HasDerivAt
      (fun x : ℝ ↦ Real.log (taoUpperEdge - (x - 1)))
      (-1 / (taoUpperEdge - (t - 1))) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (((hasDerivAt_const t taoUpperEdge).sub
        ((hasDerivAt_id t).sub_const 1)).log hfarLeft)
  have hlogFarRight : HasDerivAt
      (fun x : ℝ ↦ Real.log (taoUpperEdge - (x + 1)))
      (-1 / (taoUpperEdge - (t + 1))) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (((hasDerivAt_const t taoUpperEdge).sub
        ((hasDerivAt_id t).add_const 1)).log hfarRight)
  have hfun : taoCaseOneGap = fun x : ℝ ↦
      Real.log (x + 1) * Real.log (taoUpperEdge - (x - 1)) -
        Real.log (x - 1) * Real.log (taoUpperEdge - (x + 1)) := by
    funext x
    unfold taoCaseOneGap
    ring
  rw [hfun]
  convert! (hlogRight.mul hlogFarLeft).sub
    (hlogLeft.mul hlogFarRight) using 1
  unfold taoCaseOneGapDerivative
  field_simp [hleft, hright, hfarLeft, hfarRight]
  ring

theorem taoCaseOneGapDerivative_at_sqrt_two :
    taoCaseOneGapDerivative (Real.sqrt 2) = 0 := by
  have hfarLeft :
      taoUpperEdge - (Real.sqrt 2 - 1) = Real.sqrt 2 + 1 := by
    unfold taoUpperEdge
    ring
  have hfarRight :
      taoUpperEdge - (Real.sqrt 2 + 1) = Real.sqrt 2 - 1 := by
    unfold taoUpperEdge
    ring
  unfold taoCaseOneGapDerivative
  rw [hfarLeft, hfarRight]
  ring

theorem taoCaseOneGap_at_sqrt_two :
    taoCaseOneGap (Real.sqrt 2) = 0 := by
  have hfarLeft :
      taoUpperEdge - (Real.sqrt 2 - 1) = Real.sqrt 2 + 1 := by
    unfold taoUpperEdge
    ring
  have hfarRight :
      taoUpperEdge - (Real.sqrt 2 + 1) = Real.sqrt 2 - 1 := by
    unfold taoUpperEdge
    ring
  unfold taoCaseOneGap
  rw [hfarLeft, hfarRight]
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hleft : Real.sqrt 2 - 1 ≠ 0 :=
    sub_ne_zero.mpr one_lt_sqrt_two.ne'
  have hright : Real.sqrt 2 + 1 ≠ 0 := by positivity
  have hprod : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
    nlinarith [sqrt_two_sq]
  have hlogsum :
      Real.log (Real.sqrt 2 - 1) + Real.log (Real.sqrt 2 + 1) = 0 := by
    rw [← Real.log_mul hleft hright, hprod, Real.log_one]
  have hlogneg :
      Real.log (Real.sqrt 2 - 1) = -Real.log (Real.sqrt 2 + 1) := by
    linarith
  rw [hlogneg]
  ring

theorem taoCaseOneGap_pos_iff_ratio {t : ℝ}
    (hMl : 1 < taoUpperEdge - (t - 1))
    (hMr0 : 0 < taoUpperEdge - (t + 1))
    (hMr1 : taoUpperEdge - (t + 1) < 1) :
    0 < taoCaseOneGap t ↔
      -Real.log (t - 1) /
          Real.log (taoUpperEdge - (t - 1)) <
        Real.log (t + 1) /
          (-Real.log (taoUpperEdge - (t + 1))) := by
  have hB : 0 < Real.log (taoUpperEdge - (t - 1)) :=
    Real.log_pos hMl
  have hD : 0 < -Real.log (taoUpperEdge - (t + 1)) :=
    neg_pos.mpr (Real.log_neg hMr0 hMr1)
  rw [div_lt_div_iff₀ hB hD]
  unfold taoCaseOneGap
  constructor <;> intro h <;> nlinarith

def taoCaseOneGapInterval
    (logLeft logFarLeft logRight logFarRight : RatInterval) : RatInterval :=
  RatInterval.sub
    (RatInterval.mul logRight logFarLeft)
    (RatInterval.mul (RatInterval.neg logLeft) (RatInterval.neg logFarRight))

/-- Executable enclosure of the case-one gap on a rational input interval. -/
def evalTaoCaseOneGapInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let left := RatInterval.sub T (RatInterval.point 1)
  let right := RatInterval.add T (RatInterval.point 1)
  let farLeft := RatInterval.sub M left
  let farRight := RatInterval.sub M right
  let logLeft ← RatInterval.log? precision left
  let logFarLeft ← RatInterval.log? precision farLeft
  let logRight ← RatInterval.log? precision right
  let logFarRight ← RatInterval.log? precision farRight
  pure (taoCaseOneGapInterval
    logLeft logFarLeft logRight logFarRight)

/-- Sound interval composition for `taoCaseOneGap`. -/
theorem taoCaseOneGapInterval_contains
    {precision : Nat} {T S logLeft logFarLeft logRight logFarRight : RatInterval}
    {t : ℝ}
    (hT : T.Contains t)
    (hS : S.Contains (Real.sqrt 2))
    (hlogLeft :
      RatInterval.log? precision
        (RatInterval.sub T (RatInterval.point 1)) = some logLeft)
    (hlogFarLeft :
      RatInterval.log? precision
        (RatInterval.sub
          (RatInterval.mul (RatInterval.point 2) S)
          (RatInterval.sub T (RatInterval.point 1))) = some logFarLeft)
    (hlogRight :
      RatInterval.log? precision
        (RatInterval.add T (RatInterval.point 1)) = some logRight)
    (hlogFarRight :
      RatInterval.log? precision
        (RatInterval.sub
          (RatInterval.mul (RatInterval.point 2) S)
          (RatInterval.add T (RatInterval.point 1))) = some logFarRight) :
    (taoCaseOneGapInterval
      logLeft logFarLeft logRight logFarRight).Contains
        (taoCaseOneGap t) := by
  have hOne := RatInterval.point_contains (1 : Rat)
  have hTwo := RatInterval.point_contains (2 : Rat)
  have hleft := RatInterval.sub_contains hT hOne
  have hright := RatInterval.add_contains hT hOne
  have hM := RatInterval.mul_contains hTwo hS
  have hfarLeft := RatInterval.sub_contains hM hleft
  have hfarRight := RatInterval.sub_contains hM hright
  have hlogLeftContains := RatInterval.log_contains hleft hlogLeft
  have hlogFarLeftContains := RatInterval.log_contains hfarLeft hlogFarLeft
  have hlogRightContains := RatInterval.log_contains hright hlogRight
  have hlogFarRightContains := RatInterval.log_contains hfarRight hlogFarRight
  have hfirst := RatInterval.mul_contains
    hlogRightContains hlogFarLeftContains
  have hsecond := RatInterval.mul_contains
    (RatInterval.neg_contains hlogLeftContains)
    (RatInterval.neg_contains hlogFarRightContains)
  have hgap := RatInterval.sub_contains hfirst hsecond
  simpa only [taoCaseOneGapInterval, taoCaseOneGap, taoUpperEdge,
    Rat.cast_ofNat, Rat.cast_one] using! hgap

theorem taoCaseOneGap_pos_of_interval
    {I : RatInterval} {t : ℝ} (hI : I.Contains (taoCaseOneGap t))
    (hpositive : 0 < I.lo) :
    0 < taoCaseOneGap t := by
  have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hpositive
  exact hlo.trans_le hI.1

end

end Erdos1038

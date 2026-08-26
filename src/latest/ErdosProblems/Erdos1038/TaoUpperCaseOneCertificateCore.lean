import ErdosProblems.Erdos1038.TaoUpperCaseOneInterval
import Mathlib.Analysis.Convex.Deriv

set_option maxRecDepth 100000

/-!
# A complete checked certificate for Tao's first upper-bound range

This module closes the scalar comparison left by the two-atom trial.  Close
to `sqrt 2` the comparison has a double zero, so we certify positivity of its
second derivative and use strict convexity.  Away from that endpoint, a
finite chain of rational intervals directly certifies the logarithmic gap.
Every transcendental bound is supplied by `RationalInterval`; the finite
certificate is evaluated by `kernel_decide`.
-/

open Set

namespace Erdos1038

noncomputable section

def taoCaseOneGapSecondDerivative (t : ℝ) : ℝ :=
  -2 / ((t + 1) * (taoUpperEdge - (t - 1))) -
    Real.log (taoUpperEdge - (t - 1)) / (t + 1) ^ 2 -
    Real.log (t + 1) / (taoUpperEdge - (t - 1)) ^ 2 +
    2 / ((t - 1) * (taoUpperEdge - (t + 1))) +
    Real.log (taoUpperEdge - (t + 1)) / (t - 1) ^ 2 +
    Real.log (t - 1) / (taoUpperEdge - (t + 1)) ^ 2

theorem hasDerivAt_taoCaseOneGapDerivative {t : ℝ}
    (hleft : t - 1 ≠ 0) (hright : t + 1 ≠ 0)
    (hfarLeft : taoUpperEdge - (t - 1) ≠ 0)
    (hfarRight : taoUpperEdge - (t + 1) ≠ 0) :
    HasDerivAt taoCaseOneGapDerivative
      (taoCaseOneGapSecondDerivative t) t := by
  have hLeft : HasDerivAt (fun x : ℝ ↦ x - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have hRight : HasDerivAt (fun x : ℝ ↦ x + 1) 1 t :=
    (hasDerivAt_id t).add_const 1
  have hFarLeft : HasDerivAt
      (fun x : ℝ ↦ taoUpperEdge - (x - 1)) (-1) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (hasDerivAt_const t taoUpperEdge).sub hLeft
  have hFarRight : HasDerivAt
      (fun x : ℝ ↦ taoUpperEdge - (x + 1)) (-1) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (hasDerivAt_const t taoUpperEdge).sub hRight
  have hlogLeft : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1))
      (1 / (t - 1)) t := by
    simpa only [one_div] using! hLeft.log hleft
  have hlogRight : HasDerivAt (fun x : ℝ ↦ Real.log (x + 1))
      (1 / (t + 1)) t := by
    simpa only [one_div] using! hRight.log hright
  have hlogFarLeft : HasDerivAt
      (fun x : ℝ ↦ Real.log (taoUpperEdge - (x - 1)))
      (-1 / (taoUpperEdge - (t - 1))) t := by
    simpa only using! hFarLeft.log hfarLeft
  have hlogFarRight : HasDerivAt
      (fun x : ℝ ↦ Real.log (taoUpperEdge - (x + 1)))
      (-1 / (taoUpperEdge - (t + 1))) t := by
    simpa only using! hFarRight.log hfarRight
  unfold taoCaseOneGapDerivative
  convert! (((hlogFarLeft.div hRight hright).sub
    (hlogRight.div hFarLeft hfarLeft)).sub
    (hlogFarRight.div hLeft hleft)).add
    (hlogLeft.div hFarRight hfarRight) using 1
  unfold taoCaseOneGapSecondDerivative
  field_simp [hleft, hright, hfarLeft, hfarRight]
  ring

theorem taoCaseOneInitial_geometry {t : ℝ}
    (htLower : Real.sqrt 2 ≤ t) (htUpper : t ≤ 3 / 2) :
    t - 1 ≠ 0 ∧ t + 1 ≠ 0 ∧
      taoUpperEdge - (t - 1) ≠ 0 ∧
      taoUpperEdge - (t + 1) ≠ 0 := by
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := seven_fifths_lt_sqrt_two
  unfold taoUpperEdge
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Executable enclosure of the second derivative on a rational interval. -/
def evalTaoCaseOneGapSecondDerivativeInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let left := RatInterval.sub T (RatInterval.point 1)
  let right := RatInterval.add T (RatInterval.point 1)
  let farLeft := RatInterval.sub M left
  let farRight := RatInterval.sub M right
  let logLeft ← RatInterval.log? precision left
  let logRight ← RatInterval.log? precision right
  let logFarLeft ← RatInterval.log? precision farLeft
  let logFarRight ← RatInterval.log? precision farRight
  let t₁ ← RatInterval.div? (RatInterval.point (-2))
    (RatInterval.mul right farLeft)
  let t₂ ← RatInterval.div? (RatInterval.neg logFarLeft)
    (RatInterval.powNat 2 right)
  let t₃ ← RatInterval.div? (RatInterval.neg logRight)
    (RatInterval.powNat 2 farLeft)
  let t₄ ← RatInterval.div? (RatInterval.point 2)
    (RatInterval.mul left farRight)
  let t₅ ← RatInterval.div? logFarRight
    (RatInterval.powNat 2 left)
  let t₆ ← RatInterval.div? logLeft
    (RatInterval.powNat 2 farRight)
  pure (RatInterval.add
    (RatInterval.add (RatInterval.add t₁ t₂) (RatInterval.add t₃ t₄))
    (RatInterval.add t₅ t₆))

def taoCaseOneSecondDerivativePositive
    (precision : Nat) (T : RatInterval) : Bool :=
  match evalTaoCaseOneGapSecondDerivativeInterval precision T with
  | some J => decide (0 < J.lo)
  | none => false

def taoCaseOneGapPositive (precision : Nat) (T : RatInterval) : Bool :=
  match evalTaoCaseOneGapInterval precision T with
  | some J => decide (0 < J.lo)
  | none => false

theorem evalTaoCaseOneGapSecondDerivativeInterval_contains
    {precision : Nat} {T J : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseOneGapSecondDerivativeInterval precision T = some J) :
    J.Contains (taoCaseOneGapSecondDerivative t) := by
  simp only [evalTaoCaseOneGapSecondDerivativeInterval,
    Bind.bind, Option.bind_eq_some_iff] at hEval
  rcases hEval with
    ⟨S, hS, logLeft, hlogLeft, logRight, hlogRight,
      logFarLeft, hlogFarLeft, logFarRight, hlogFarRight,
      t₁, ht₁, t₂, ht₂, t₃, ht₃, t₄, ht₄, t₅, ht₅, t₆, ht₆, hJ⟩
  change some
    (RatInterval.add
      (RatInterval.add (RatInterval.add t₁ t₂) (RatInterval.add t₃ t₄))
      (RatInterval.add t₅ t₆)) = some J at hJ
  injection hJ with hJ
  subst J
  have hOne := RatInterval.point_contains (1 : Rat)
  have hTwo := RatInterval.point_contains (2 : Rat)
  have hNegTwo := RatInterval.point_contains (-2 : Rat)
  have hSContains := RatInterval.sqrt_contains
    (RatInterval.point_contains (2 : Rat)) hS
  have hM := RatInterval.mul_contains hTwo hSContains
  have hleft := RatInterval.sub_contains hT hOne
  have hright := RatInterval.add_contains hT hOne
  have hfarLeft := RatInterval.sub_contains hM hleft
  have hfarRight := RatInterval.sub_contains hM hright
  have hlogLeftContains := RatInterval.log_contains hleft hlogLeft
  have hlogRightContains := RatInterval.log_contains hright hlogRight
  have hlogFarLeftContains := RatInterval.log_contains hfarLeft hlogFarLeft
  have hlogFarRightContains := RatInterval.log_contains hfarRight hlogFarRight
  have ht₁Contains := RatInterval.div_contains hNegTwo
    (RatInterval.mul_contains hright hfarLeft) ht₁
  have ht₂Contains := RatInterval.div_contains
    (RatInterval.neg_contains hlogFarLeftContains)
    (RatInterval.powNat_contains 2 hright) ht₂
  have ht₃Contains := RatInterval.div_contains
    (RatInterval.neg_contains hlogRightContains)
    (RatInterval.powNat_contains 2 hfarLeft) ht₃
  have ht₄Contains := RatInterval.div_contains hTwo
    (RatInterval.mul_contains hleft hfarRight) ht₄
  have ht₅Contains := RatInterval.div_contains hlogFarRightContains
    (RatInterval.powNat_contains 2 hleft) ht₅
  have ht₆Contains := RatInterval.div_contains hlogLeftContains
    (RatInterval.powNat_contains 2 hfarRight) ht₆
  have hsum := RatInterval.add_contains
    (RatInterval.add_contains
      (RatInterval.add_contains ht₁Contains ht₂Contains)
      (RatInterval.add_contains ht₃Contains ht₄Contains))
    (RatInterval.add_contains ht₅Contains ht₆Contains)
  convert! hsum using 1
  simp only [taoCaseOneGapSecondDerivative, taoUpperEdge,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_neg, pow_two,
    sub_eq_add_neg]
  ring

theorem evalTaoCaseOneGapInterval_contains_direct
    {precision : Nat} {T J : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseOneGapInterval precision T = some J) :
    J.Contains (taoCaseOneGap t) := by
  simp only [evalTaoCaseOneGapInterval, Bind.bind,
    Option.bind_eq_some_iff] at hEval
  rcases hEval with
    ⟨S, hS, logLeft, hlogLeft, logFarLeft, hlogFarLeft,
      logRight, hlogRight, logFarRight, hlogFarRight, hJ⟩
  change some (taoCaseOneGapInterval
    logLeft logFarLeft logRight logFarRight) = some J at hJ
  injection hJ with hJ
  subst J
  exact taoCaseOneGapInterval_contains hT
    (RatInterval.sqrt_contains (RatInterval.point_contains (2 : Rat)) hS)
    hlogLeft hlogFarLeft hlogRight hlogFarRight

/-- Consecutive rational cells of width `step`, starting at `start`. -/
def uniformRatIntervals : Rat → Rat → Nat → List RatInterval
  | _, _, 0 => []
  | start, step, n + 1 =>
      ⟨start, start + step⟩ ::
        uniformRatIntervals (start + step) step n

private def ratIntervalTailCovers
    (current finish : Rat) : List RatInterval → Bool
  | [] => decide (finish ≤ current)
  | I :: intervals =>
      decide (I.lo ≤ current) &&
        ratIntervalTailCovers I.hi finish intervals

def ratIntervalChainCovers
    (start finish : Rat) : List RatInterval → Bool
  | [] => false
  | I :: intervals =>
      decide (I.lo ≤ start) &&
        ratIntervalTailCovers I.hi finish intervals

private theorem exists_interval_of_tail_covers
    {current finish : Rat} {intervals : List RatInterval}
    (hcover : ratIntervalTailCovers current finish intervals = true)
    {x : ℝ} (hcurrent : (current : ℝ) < x)
    (hfinish : x ≤ (finish : ℝ)) :
    ∃ I ∈ intervals, I.Contains x := by
  induction intervals generalizing current with
  | nil =>
      simp only [ratIntervalTailCovers, decide_eq_true_eq] at hcover
      have hcoverReal : (finish : ℝ) ≤ (current : ℝ) := by
        exact_mod_cast hcover
      linarith
  | cons I intervals ih =>
      simp only [ratIntervalTailCovers, Bool.and_eq_true,
        decide_eq_true_eq] at hcover
      by_cases hxI : x ≤ (I.hi : ℝ)
      · refine ⟨I, by simp, ?_⟩
        constructor
        · have hlo : (I.lo : ℝ) ≤ (current : ℝ) := by
            exact_mod_cast hcover.1
          exact hlo.trans hcurrent.le
        · exact hxI
      · have hIhi : (I.hi : ℝ) < x := lt_of_not_ge hxI
        rcases ih hcover.2 hIhi with ⟨J, hJ, hxJ⟩
        exact ⟨J, by simp [hJ], hxJ⟩

theorem exists_interval_of_chain_covers
    {start finish : Rat} {intervals : List RatInterval}
    (hcover : ratIntervalChainCovers start finish intervals = true)
    {x : ℝ} (hstart : (start : ℝ) ≤ x)
    (hfinish : x ≤ (finish : ℝ)) :
    ∃ I ∈ intervals, I.Contains x := by
  cases intervals with
  | nil => simp [ratIntervalChainCovers] at hcover
  | cons I intervals =>
      simp only [ratIntervalChainCovers, Bool.and_eq_true,
        decide_eq_true_eq] at hcover
      by_cases hxI : x ≤ (I.hi : ℝ)
      · refine ⟨I, by simp, ?_⟩
        constructor
        · have hlo : (I.lo : ℝ) ≤ (start : ℝ) := by
            exact_mod_cast hcover.1
          exact hlo.trans (hstart)
        · exact hxI
      · have hIhi : (I.hi : ℝ) < x := lt_of_not_ge hxI
        rcases exists_interval_of_tail_covers hcover.2 hIhi hfinish with
          ⟨J, hJ, hxJ⟩
        exact ⟨J, by simp [hJ], hxJ⟩

theorem bool_predicate_of_all
    {α : Type*} {p : α → Bool} {xs : List α}
    (hall : xs.all p = true) {x : α} (hx : x ∈ xs) :
    p x = true := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hall.1
      · exact ih hall.2 hx

theorem taoCaseOneSecondDerivative_pos_of_certificate
    {precision : Nat} {I : RatInterval} {t : ℝ}
    (hI : I.Contains t)
    (hcert : taoCaseOneSecondDerivativePositive precision I = true) :
    0 < taoCaseOneGapSecondDerivative t := by
  cases hEval : evalTaoCaseOneGapSecondDerivativeInterval precision I with
  | none => simp [taoCaseOneSecondDerivativePositive, hEval] at hcert
  | some J =>
      have hlo : 0 < J.lo := by
        simpa [taoCaseOneSecondDerivativePositive, hEval] using! hcert
      have hloReal : (0 : ℝ) < (J.lo : ℝ) := by exact_mod_cast hlo
      exact hloReal.trans_le
        (evalTaoCaseOneGapSecondDerivativeInterval_contains hI hEval).1

theorem taoCaseOneGap_pos_of_certificate
    {precision : Nat} {I : RatInterval} {t : ℝ}
    (hI : I.Contains t)
    (hcert : taoCaseOneGapPositive precision I = true) :
    0 < taoCaseOneGap t := by
  cases hEval : evalTaoCaseOneGapInterval precision I with
  | none => simp [taoCaseOneGapPositive, hEval] at hcert
  | some J =>
      have hlo : 0 < J.lo := by
        simpa [taoCaseOneGapPositive, hEval] using! hcert
      have hloReal : (0 : ℝ) < (J.lo : ℝ) := by exact_mod_cast hlo
      exact hloReal.trans_le
        (evalTaoCaseOneGapInterval_contains_direct hI hEval).1

end

end Erdos1038

import Wikipedia.SmoothSixDPoincare.WhitneyBigon
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Actual planar coordinates at a parabolic bigon corner

The two boundary arcs become the positive coordinate axes. Both directions
of this change of variables are explicit, and the chart is a genuine partial
diffeomorphism. The upper and lower arcs retain the same unit-interval time.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- Unit-interval time along either parabolic boundary arc. -/
def arcTime (p : ℝ × ℝ) : ℝ := (p.1 + 1) / 2

/-- Coordinates straightening both boundary arcs at the left corner. -/
def leftCornerCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p - p.2 / (4 * h * (1 - arcTime p)), p.2 / (4 * h * (1 - arcTime p)))

/-- The polynomial inverse of the left-corner coordinate map. -/
def leftCornerInverse (h : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (2 * (q.1 + q.2) - 1, 4 * h * q.2 * (1 - (q.1 + q.2)))

theorem contDiff_arcTime : ContDiff ℝ ∞ arcTime := by unfold arcTime; fun_prop

theorem contDiff_leftCornerInverse (h : ℝ) : ContDiff ℝ ∞ (leftCornerInverse h) := by
  unfold leftCornerInverse
  fun_prop

theorem leftCornerCoordinates_sum (h : ℝ) (p : ℝ × ℝ) :
    (leftCornerCoordinates h p).1 + (leftCornerCoordinates h p).2 = arcTime p := by
  dsimp [leftCornerCoordinates]
  ring

theorem arcTime_leftCornerInverse (h : ℝ) (q : ℝ × ℝ) :
    arcTime (leftCornerInverse h q) = q.1 + q.2 := by
  dsimp [arcTime, leftCornerInverse]
  ring

theorem leftCornerInverse_coordinates {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≠ 1) : leftCornerInverse h (leftCornerCoordinates h p) = p := by
  have hd : 4 * h * (1 - arcTime p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  apply Prod.ext
  · change 2 * ((leftCornerCoordinates h p).1 + (leftCornerCoordinates h p).2) - 1 = p.1
    rw [leftCornerCoordinates_sum]
    dsimp [arcTime]
    ring
  · change 4 * h * (leftCornerCoordinates h p).2 *
        (1 - ((leftCornerCoordinates h p).1 + (leftCornerCoordinates h p).2)) = p.2
    rw [leftCornerCoordinates_sum]
    change 4 * h * (p.2 / (4 * h * (1 - arcTime p))) * (1 - arcTime p) = p.2
    calc
      _ = (p.2 / (4 * h * (1 - arcTime p))) * (4 * h * (1 - arcTime p)) := by ring
      _ = p.2 := div_mul_cancel₀ _ hd

theorem leftCornerCoordinates_inverse {h : ℝ} (hh : h ≠ 0) {q : ℝ × ℝ}
    (hq : q.1 + q.2 ≠ 1) : leftCornerCoordinates h (leftCornerInverse h q) = q := by
  have hd : 4 * h * (1 - (q.1 + q.2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hq))
  have hb : (leftCornerInverse h q).2 / (4 * h * (1 - arcTime (leftCornerInverse h q))) =
      q.2 := by
    rw [arcTime_leftCornerInverse]
    change (4 * h * q.2 * (1 - (q.1 + q.2))) / (4 * h * (1 - (q.1 + q.2))) = q.2
    rw [show 4 * h * q.2 * (1 - (q.1 + q.2)) = q.2 * (4 * h * (1 - (q.1 + q.2))) by ring]
    exact mul_div_cancel_right₀ _ hd
  apply Prod.ext
  · change arcTime (leftCornerInverse h q) -
        (leftCornerInverse h q).2 / (4 * h * (1 - arcTime (leftCornerInverse h q))) = q.1
    rw [hb, arcTime_leftCornerInverse]
    ring
  · exact hb

theorem contDiffOn_leftCornerCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiffOn ℝ ∞ (leftCornerCoordinates h) {p | arcTime p ≠ 1} := by
  have hd : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => p.2 / (4 * h * (1 - arcTime p))) {p | arcTime p ≠ 1} := by
    apply contDiffOn_snd.div
      (contDiff_const.mul (contDiff_const.sub contDiff_arcTime)).contDiffOn
    intro p hp
    exact mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  exact (contDiff_arcTime.contDiffOn.sub hd).prodMk hd

/-- A genuine smooth chart at the left corner, with its explicit polynomial inverse. -/
def leftCornerChart {h : ℝ} (hh : h ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun := leftCornerCoordinates h
  invFun := leftCornerInverse h
  source := {p | arcTime p ≠ 1}
  target := {q | q.1 + q.2 ≠ 1}
  map_source' := by
    intro p hp
    change (leftCornerCoordinates h p).1 + (leftCornerCoordinates h p).2 ≠ 1
    rwa [leftCornerCoordinates_sum]
  map_target' := by
    intro q hq
    change arcTime (leftCornerInverse h q) ≠ 1
    rwa [arcTime_leftCornerInverse]
  left_inv' := fun _ hp => leftCornerInverse_coordinates hh hp
  right_inv' := fun _ hq => leftCornerCoordinates_inverse hh hq
  open_source := isOpen_ne_fun contDiff_arcTime.continuous continuous_const
  open_target := isOpen_ne_fun (continuous_fst.add continuous_snd) continuous_const
  contMDiffOn_toFun := (contDiffOn_leftCornerCoordinates hh).contMDiffOn
  contMDiffOn_invFun := (contDiff_leftCornerInverse h).contMDiff.contMDiffOn

theorem leftCornerCoordinates_lower (h t : ℝ) :
    leftCornerCoordinates h (2 * t - 1, 0) = (t, 0) := by
  simp only [leftCornerCoordinates, arcTime, zero_div, sub_zero]
  congr 1
  ring

theorem leftCornerCoordinates_upper {h : ℝ} (hh : h ≠ 0) {t : ℝ} (ht : t ≠ 1) :
    leftCornerCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = (0, t) := by
  have hq : (0 : ℝ) + t ≠ 1 := by simpa only [zero_add] using ht
  have hinv : leftCornerInverse h (0, t) =
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
    apply Prod.ext <;> dsimp [leftCornerInverse] <;> ring
  rw [← hinv]
  exact leftCornerCoordinates_inverse hh hq

theorem leftCornerCoordinates_corner (h : ℝ) : leftCornerCoordinates h (-1, 0) = (0, 0) := by
  convert leftCornerCoordinates_lower h 0 using 1
  norm_num

/-- Off both boundary arcs, the corner map has both coordinates nonzero. -/
theorem leftCornerCoordinates_axes {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≠ 1) :
    ((leftCornerCoordinates h p).2 = 0 ↔ p.2 = 0) ∧
      ((leftCornerCoordinates h p).1 = 0 ↔ p.2 = h * (1 - p.1 ^ 2)) := by
  have hd : 4 * h * (1 - arcTime p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  constructor
  · change p.2 / (4 * h * (1 - arcTime p)) = 0 ↔ p.2 = 0
    exact div_eq_zero_iff.trans (or_iff_left (fun h => hd h))
  · change arcTime p - p.2 / (4 * h * (1 - arcTime p)) = 0 ↔ _
    rw [sub_eq_zero, eq_div_iff hd]
    have hid : arcTime p * (4 * h * (1 - arcTime p)) = h * (1 - p.1 ^ 2) := by
      dsimp [arcTime]
      ring
    rw [hid]
    exact eq_comm

/-- Reflection interchanging the two bigon endpoints. -/
def bigonReflection : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem bigonReflection_apply (p : ℝ × ℝ) : bigonReflection p = (-p.1, p.2) := rfl

theorem arcTime_bigonReflection (p : ℝ × ℝ) :
    arcTime (bigonReflection p) = 1 - arcTime p := by
  dsimp [arcTime, bigonReflection]
  ring

def rightCornerCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  leftCornerCoordinates h ∘ bigonReflection

/-- The corresponding genuine smooth chart at the right corner. -/
def rightCornerChart {h : ℝ} (hh : h ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ :=
  bigonReflection.toDiffeomorph.toPartialDiffeomorph.trans (leftCornerChart hh)

theorem rightCornerChart_apply {h : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ) :
    rightCornerChart hh p = rightCornerCoordinates h p := rfl

theorem rightCornerCoordinates_corner (h : ℝ) : rightCornerCoordinates h (1, 0) = (0, 0) :=
  leftCornerCoordinates_corner h

theorem leftCornerCoordinates_exchange {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≠ 1) :
    leftCornerCoordinates h (p.1, h * (1 - p.1 ^ 2) - p.2) =
      (leftCornerCoordinates h p).swap := by
  have hd : 4 * h * (1 - arcTime p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  have hheight : h * (1 - p.1 ^ 2) = arcTime p * (4 * h * (1 - arcTime p)) := by
    dsimp [arcTime]
    ring
  have hv : (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) =
      arcTime p - p.2 / (4 * h * (1 - arcTime p)) := by
    rw [sub_div, hheight, mul_div_cancel_right₀ _ hd]
  apply Prod.ext
  · change arcTime p - (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) = _
    rw [hv]
    dsimp [leftCornerCoordinates]
    ring
  · exact hv

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel

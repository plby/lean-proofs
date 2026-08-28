import Wikipedia.HopfProblem.SpecialPeriodsTriangleInterior
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Analytic boundary coordinates for the half-Ford triangle

The circular side is straightened by the explicit Möbius coordinate
`i z / (z + 2)`.  Its imaginary part is positive exactly outside the circle
`|z + 1| = 1`.  Together with the affine coordinates on the vertical sides,
these are genuine analytic local coordinates for applying boundary
reflection to the actual triangle, not assumed boundary regularity.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def circleStraighten (z : ℂ) : ℂ := I * z / (z + 2)

def circleUnstraighten (w : ℂ) : ℂ := 2 * w / (I - w)

theorem circleStraighten_sub_I {z : ℂ} (hz : z + 2 ≠ 0) :
    I - circleStraighten z = 2 * I / (z + 2) := by
  unfold circleStraighten
  field_simp
  ring

theorem circleStraighten_ne_I {z : ℂ} (hz : z + 2 ≠ 0) :
    circleStraighten z ≠ I := by
  have h : I - circleStraighten z ≠ 0 := by
    rw [circleStraighten_sub_I hz]
    exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz
  exact fun he => h (by rw [he, sub_self])

theorem circleUnstraighten_add_two {w : ℂ} (hw : I - w ≠ 0) :
    circleUnstraighten w + 2 = 2 * I / (I - w) := by
  unfold circleUnstraighten
  field_simp
  ring

theorem circleUnstraighten_add_two_ne_zero {w : ℂ} (hw : I - w ≠ 0) :
    circleUnstraighten w + 2 ≠ 0 := by
  rw [circleUnstraighten_add_two hw]
  exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hw

theorem circleUnstraighten_straighten {z : ℂ} (hz : z + 2 ≠ 0) :
    circleUnstraighten (circleStraighten z) = z := by
  rw [circleUnstraighten, circleStraighten_sub_I hz]
  unfold circleStraighten
  field_simp

theorem circleStraighten_unstraighten {w : ℂ} (hw : I - w ≠ 0) :
    circleStraighten (circleUnstraighten w) = w := by
  rw [circleStraighten, circleUnstraighten_add_two hw]
  unfold circleUnstraighten
  field_simp

/-- The circular-side coordinate is an actual partial homeomorphism,
with its rational inverse and complete domains. -/
def circleBoundaryChart : OpenPartialHomeomorph ℂ ℂ where
  toFun := circleStraighten
  invFun := circleUnstraighten
  source := {z | z + 2 ≠ 0}
  target := {w | I - w ≠ 0}
  map_source' z hz := sub_ne_zero.mpr (circleStraighten_ne_I hz).symm
  map_target' w hw := circleUnstraighten_add_two_ne_zero hw
  left_inv' z hz := circleUnstraighten_straighten hz
  right_inv' w hw := circleStraighten_unstraighten hw
  open_source := isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
  open_target := isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const
  continuousOn_toFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz
  continuousOn_invFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz

theorem circleStraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleStraighten {z | z + 2 ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_id.add analyticAt_const) hz

theorem circleUnstraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleUnstraighten {w | I - w ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_const.sub analyticAt_id) hz

theorem circleStraighten_im (z : ℂ) :
    (circleStraighten z).im = (normSq (z + 1) - 1) / normSq (z + 2) := by
  simp only [circleStraighten, div_im, mul_im, I_re, I_im, zero_mul,
    one_mul, zero_add, mul_re, zero_sub, add_re, re_ofNat, add_im, im_ofNat, add_zero]
  rw [← sub_div]
  congr 1
  simp only [normSq_apply, add_re, one_re, add_im, one_im, add_zero]
  ring

theorem circleStraighten_im_pos_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    0 < (circleStraighten z).im ↔ 1 < ‖z + 1‖ := by
  rw [circleStraighten_im, div_pos_iff_of_pos_right (normSq_pos.mpr hz), sub_pos]
  rw [normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    nlinarith

theorem circleStraighten_im_eq_zero_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    (circleStraighten z).im = 0 ↔ ‖z + 1‖ = 1 := by
  rw [circleStraighten_im, div_eq_zero_iff, or_iff_left (normSq_pos.mpr hz).ne',
    sub_eq_zero, normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    rw [h]
    norm_num

/-- On the open circular side, the actual triangle is locally the upper
side of the proved analytic chart. -/
theorem exists_circle_side_neighborhood {a : ℂ}
    (haL : stripLeft < a.re) (haR : a.re < -1 / 2) (hai : 0 < a.im) :
    ∃ r > 0, ∀ z ∈ ball a r,
      z ∈ circleBoundaryChart.source ∧
        (z ∈ triangleInterior ↔ 0 < (circleBoundaryChart z).im) := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_re continuous_const).inter
        (isOpen_lt continuous_const continuous_im))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a ⟨haL, haR, hai⟩
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  have hzden : z + 2 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im, im_ofNat, add_zero, zero_im] at hi
    exact h.2.2.ne' hi
  refine ⟨hzden, ?_⟩
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖) ↔
    0 < (circleStraighten z).im
  rw [circleStraighten_im_pos_iff hzden]
  exact ⟨fun hz' => hz'.2.2.2, fun hnorm => ⟨h.1, h.2.1, h.2.2, hnorm⟩⟩

/-- An affine complex coordinate on the left vertical side. -/
def leftBoundaryChart : ℂ ≃ₜ ℂ where
  toFun z := I * (z - stripLeft)
  invFun w := -I * w + stripLeft
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- An affine complex coordinate on the right vertical side. -/
def rightBoundaryChart : ℂ ≃ₜ ℂ where
  toFun z := -I * (z + 1 / 2)
  invFun w := I * w - 1 / 2
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem leftBoundaryChart_im (z : ℂ) :
    (leftBoundaryChart z).im = z.re - stripLeft := by
  change (I * (z - (stripLeft : ℂ))).im = _
  simp

@[simp] theorem rightBoundaryChart_im (z : ℂ) :
    (rightBoundaryChart z).im = -(z.re + 1 / 2) := by
  change (-I * (z + 1 / 2)).im = _
  simp

theorem leftBoundaryChart_analyticAt (z : ℂ) : AnalyticAt ℂ leftBoundaryChart z :=
  analyticAt_const.mul (analyticAt_id.sub analyticAt_const)

theorem leftBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ leftBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem rightBoundaryChart_analyticAt (z : ℂ) : AnalyticAt ℂ rightBoundaryChart z :=
  analyticAt_const.mul (analyticAt_id.add analyticAt_const)

theorem rightBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ rightBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).sub analyticAt_const

theorem stripLeft_lt_right : stripLeft < -1 / 2 := by
  unfold stripLeft
  linarith [width_pos]

/-- The open left side of the actual triangle has a genuine affine
coordinate in which its interior is locally the upper half-plane. -/
theorem exists_left_side_neighborhood {a : ℂ} (ha : a.re = stripLeft)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ ball a r,
      z ∈ triangleInterior ↔ 0 < (leftBoundaryChart z).im := by
  let V : Set ℂ := {z | z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt continuous_re continuous_const).inter
      ((isOpen_lt continuous_const continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [leftBoundaryChart_im, sub_pos]
  exact ⟨fun hz' => hz'.1, fun hz' => ⟨hz', h.1, h.2.1, h.2.2⟩⟩

/-- The open right side has the corresponding affine upper-half-plane
coordinate, with the direction chosen toward the triangle's interior. -/
theorem exists_right_side_neighborhood {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ ball a r,
      z ∈ triangleInterior ↔ 0 < (rightBoundaryChart z).im := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_lt continuous_const continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [rightBoundaryChart_im]
  have he : 0 < -(z.re + 1 / 2) ↔ z.re < -1 / 2 := by
    constructor <;> intro hi <;> linarith
  rw [he]
  exact ⟨fun hz' => hz'.2.1, fun hz' => ⟨h.1, hz', h.2.1, h.2.2⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

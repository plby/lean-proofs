import Wikipedia.HopfProblem.SpecialPeriodsTriangleInterior
import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The actual elliptic corners in centered Cayley coordinates

The half-Ford triangle has angles `π / 3` and `π / 4` at its two
elliptic vertices.  The sector descriptions below are derived from the
actual circle and vertical-line inequalities, using the concrete centers.
No geometric sector hypothesis is imposed.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem cayley_re_sub (a z : ℂ) (hz : 1 - z ≠ 0) :
    (cayley a z).re - a.re =
      -2 * a.im * z.im / normSq (1 - z) := by
  have hd : normSq (1 - z) ≠ 0 := (normSq_pos.mpr hz).ne'
  simp only [cayley, div_re, sub_re, mul_re, conj_re, conj_im,
    sub_im, mul_im, one_re, one_im]
  field_simp [hd]
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im]
  ring

theorem cayley_add_one (a z : ℂ) (hz : 1 - z ≠ 0) :
    cayley a z + 1 = ((a + 1) - conj (a + 1) * z) / (1 - z) := by
  unfold cayley
  simp only [map_add, map_one]
  field_simp
  ring

theorem cayley_circle_normSq (a z : ℂ) (hz : 1 - z ≠ 0)
    (ha : normSq (a + 1) = 1) :
    normSq (cayley a z + 1) - 1 =
      (2 * z.re - 2 * ((a + 1) ^ 2 * conj z).re) / normSq (1 - z) := by
  have hd : normSq (1 - z) ≠ 0 := (normSq_pos.mpr hz).ne'
  rw [cayley_add_one a z hz, map_div₀]
  field_simp [hd]
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im,
    conj_re, conj_im, add_re, add_im, one_re, one_im, add_zero,
    pow_two] at ha ⊢
  linear_combination (1 + z.re ^ 2 + z.im ^ 2) * ha

theorem centerOne_re : centerOne.re = -1 / 2 := by
  simp only [UpperHalfPlane.re, centerOne_val, sub_re, rho_re, one_re]
  norm_num

theorem centerOne_im : centerOne.im = Real.sqrt 3 / 2 := by
  simp [UpperHalfPlane.im, centerOne_val]

theorem centerOne_circle_normSq : normSq ((centerOne : ℂ) + 1) = 1 := by
  rw [centerOne_val, sub_add_cancel, normSq_eq_norm_sq, norm_rho]
  norm_num

theorem centerTwo_circle_normSq : normSq ((centerTwo : ℂ) + 1) = 1 := by
  simp only [normSq_apply, add_re, add_im, one_re, one_im, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
  nlinarith [width_sq]

theorem cayley_centerOne_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    normSq (cayley centerOne z + 1) - 1 =
      (3 * z.re - Real.sqrt 3 * z.im) / normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (one_sub_ne_zero_of_norm_lt_one hz)
    centerOne_circle_normSq]
  congr 1
  simp only [centerOne_val, sub_add_cancel, rho_sq, mul_re, sub_re, sub_im,
    conj_re, conj_im, one_re, one_im, sub_zero, rho_re, rho_im]
  ring

theorem cayley_centerTwo_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    normSq (cayley centerTwo z + 1) - 1 =
      2 * (z.re + z.im) / normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (one_sub_ne_zero_of_norm_lt_one hz)
    centerTwo_circle_normSq]
  congr 1
  simp only [pow_two, mul_re, mul_im, add_re, add_im, one_re, one_im,
    add_zero, conj_re, conj_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    centerTwo_re, centerTwo_im]
  linear_combination z.im * width_sq

/-- The straight sector of angle `π / 3` at the first vertex. -/
def cornerSectorThree : Set ℂ :=
  {z | 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re}

/-- The straight sector of angle `π / 4` at the second vertex. -/
def cornerSectorFour : Set ℂ := {z | z.im < 0 ∧ 0 < z.re + z.im}

theorem cayley_centerOne_right_iff {z : ℂ} (hz : ‖z‖ < 1) :
    (cayley centerOne z).re < -1 / 2 ↔ 0 < z.im := by
  have h := cayley_re_sub centerOne z (one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerOne_re] at h
  have hd := normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerOne : ℂ).im := centerOne.im_pos
  have hsign : -2 * (centerOne : ℂ).im * z.im / normSq (1 - z) < 0 ↔
      0 < z.im := by
    rw [div_lt_iff₀ hd, zero_mul]
    constructor
    · intro hi
      by_contra hn
      have hle : z.im ≤ 0 := le_of_not_gt hn
      have hnonneg : 0 ≤ -2 * (centerOne : ℂ).im * z.im :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hle
      linarith
    · intro hi
      exact mul_neg_of_neg_of_pos (by linarith) hi
  rw [← h, sub_neg] at hsign
  exact hsign

theorem cayley_centerTwo_left_iff {z : ℂ} (hz : ‖z‖ < 1) :
    stripLeft < (cayley centerTwo z).re ↔ z.im < 0 := by
  have h := cayley_re_sub centerTwo z (one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerTwo_re] at h
  change (cayley centerTwo z).re - stripLeft = _ at h
  have hd := normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerTwo : ℂ).im := centerTwo.im_pos
  have hsign : 0 < -2 * (centerTwo : ℂ).im * z.im / normSq (1 - z) ↔
      z.im < 0 := by
    rw [div_pos_iff_of_pos_right hd]
    constructor
    · intro hi
      by_contra hn
      have hle : 0 ≤ z.im := le_of_not_gt hn
      have hnonpos : -2 * (centerTwo : ℂ).im * z.im ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hle
      linarith
    · intro hi
      exact mul_pos_of_neg_of_neg (by linarith) hi
  rw [← h, sub_pos] at hsign
  exact hsign

theorem one_lt_norm_iff_normSq_sub_pos (u : ℂ) :
    1 < ‖u‖ ↔ 0 < normSq u - 1 := by
  rw [normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg u]

theorem cayley_centerOne_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖cayley centerOne z + 1‖ ↔ Real.sqrt 3 * z.im < 3 * z.re := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerOne_circle_normSq hz,
    div_pos_iff_of_pos_right (normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)),
    sub_pos]

theorem cayley_centerTwo_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖cayley centerTwo z + 1‖ ↔ 0 < z.re + z.im := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerTwo_circle_normSq hz,
    div_pos_iff_of_pos_right (normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz))]
  exact mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)

theorem cayley_analyticAt (a : ℂ) {z : ℂ} (hz : 1 - z ≠ 0) :
    AnalyticAt ℂ (cayley a) z :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hz

/-- Near the first actual center, the distant left wall imposes no further
condition.  The circular and right walls give the stated straight sector. -/
theorem exists_cornerThree_radius :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, ‖z‖ < r →
      (cayley centerOne z ∈ triangleInterior ↔ z ∈ cornerSectorThree) := by
  have hc : ContinuousAt (fun z : ℂ => (cayley centerOne z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerOne (z := 0) (by simp)).continuousAt
  have hleft : ∀ᶠ z : ℂ in 𝓝 0, stripLeft < (cayley centerOne z).re :=
    continuousAt_const.eventually_lt hc (by
      simp only [cayley_zero, UpperHalfPlane.coe_re, centerOne_re]
      unfold stripLeft
      linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hleft
  refine ⟨min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := cayley_im_pos centerOne.im_pos hz1
  change (stripLeft < (cayley centerOne z).re ∧
    (cayley centerOne z).re < -1 / 2 ∧ 0 < (cayley centerOne z).im ∧
    1 < ‖cayley centerOne z + 1‖) ↔ _
  rw [cayley_centerOne_right_iff hz1, cayley_centerOne_circle_iff hz1]
  exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩,
    fun h => ⟨hball hzs, h.1, hzi, h.2⟩⟩

/-- At the second actual center, the distant right wall is absent on a
sufficiently small Cayley ball. -/
theorem exists_cornerFour_radius :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, ‖z‖ < r →
      (cayley centerTwo z ∈ triangleInterior ↔ z ∈ cornerSectorFour) := by
  have hc : ContinuousAt (fun z : ℂ => (cayley centerTwo z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerTwo (z := 0) (by simp)).continuousAt
  have hright : ∀ᶠ z : ℂ in 𝓝 0, (cayley centerTwo z).re < -1 / 2 :=
    hc.eventually_lt continuousAt_const (by
      simp only [cayley_zero, UpperHalfPlane.coe_re, centerTwo_re]
      linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hright
  refine ⟨min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := cayley_im_pos centerTwo.im_pos hz1
  change (stripLeft < (cayley centerTwo z).re ∧
    (cayley centerTwo z).re < -1 / 2 ∧ 0 < (cayley centerTwo z).im ∧
    1 < ‖cayley centerTwo z + 1‖) ↔ _
  rw [cayley_centerTwo_left_iff hz1, cayley_centerTwo_circle_iff hz1]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩,
    fun h => ⟨h.1, hball hzs, hzi, h.2⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

import Wikipedia.HopfProblem.TriangleCornerCoordinates
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Connected small neighbourhoods inside the two triangle corner sectors

The two actual linear sectors are convex.  Their intersections with every
positive-radius ball around the vertex are nonempty, as witnessed by explicit
positive multiples of `1 + I` and `2 - I`.  Thus the small sector neighbourhoods
are path connected, not merely unions of possible local branches.
-/

noncomputable section

open Complex Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem convex_cornerSectorThree : Convex ℝ cornerSectorThree := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => 3 * z.re - Real.sqrt 3 * z.im) := by
    constructor
    · intro z w
      simp only [add_re, add_im]
      ring
    · intro c z
      simp only [smul_re, smul_im, smul_eq_mul]
      ring
  have h := (convex_halfSpace_im_gt 0).inter (convex_halfSpace_gt hlin 0)
  simpa only [cornerSectorThree, ofPred_and, sub_pos] using h

theorem convex_cornerSectorFour : Convex ℝ cornerSectorFour := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re + z.im) := by
    constructor
    · intro z w
      simp only [add_re, add_im]
      ring
    · intro c z
      simp only [smul_re, smul_im, smul_eq_mul]
      ring
  exact (convex_halfSpace_im_lt 0).inter (convex_halfSpace_gt hlin 0)

theorem isOpen_cornerSectorThree : IsOpen cornerSectorThree :=
  (isOpen_lt continuous_const continuous_im).inter
    (isOpen_lt (continuous_const.mul continuous_im) (continuous_const.mul continuous_re))

theorem isOpen_cornerSectorFour : IsOpen cornerSectorFour :=
  (isOpen_lt continuous_im continuous_const).inter
    (isOpen_lt continuous_const (continuous_re.add continuous_im))

theorem convex_cornerSectorThree_inter_ball (r : ℝ) :
    Convex ℝ (cornerSectorThree ∩ ball 0 r) :=
  convex_cornerSectorThree.inter (convex_ball 0 r)

theorem convex_cornerSectorFour_inter_ball (r : ℝ) :
    Convex ℝ (cornerSectorFour ∩ ball 0 r) :=
  convex_cornerSectorFour.inter (convex_ball 0 r)

/-- An explicit point inside every positive-radius cubic sector neighbourhood. -/
theorem cornerSectorThree_small_point {r : ℝ} (hr : 0 < r) :
    (((r / 4 : ℝ) : ℂ) * (1 + I)) ∈ cornerSectorThree ∩ ball 0 r := by
  have hscale : 0 < r / 4 := div_pos hr (by norm_num)
  have hsqrt : Real.sqrt 3 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  constructor
  · change 0 < _ ∧ Real.sqrt 3 * _ < 3 * _
    simp only [mul_im, mul_re, ofReal_re, ofReal_im, add_im, add_re,
      one_re, one_im, I_re, I_im, zero_add, add_zero, mul_one, sub_zero]
    exact ⟨hscale, mul_lt_mul_of_pos_right hsqrt hscale⟩
  · rw [mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hscale]
    have hn : ‖(1 : ℂ) + I‖ ≤ 2 := by
      simpa only [norm_one, norm_I, one_add_one_eq_two] using norm_add_le (1 : ℂ) I
    calc
      (r / 4) * ‖(1 : ℂ) + I‖ ≤ (r / 4) * 2 :=
        mul_le_mul_of_nonneg_left hn hscale.le
      _ < r := by linarith

/-- An explicit point inside every positive-radius quartic sector neighbourhood. -/
theorem cornerSectorFour_small_point {r : ℝ} (hr : 0 < r) :
    (((r / 6 : ℝ) : ℂ) * (2 - I)) ∈ cornerSectorFour ∩ ball 0 r := by
  have hscale : 0 < r / 6 := div_pos hr (by norm_num)
  constructor
  · change _ < 0 ∧ 0 < _ + _
    simp only [mul_im, mul_re, ofReal_re, ofReal_im, sub_im, sub_re,
      re_ofNat, im_ofNat, I_re, I_im, zero_sub, sub_zero, mul_neg, mul_one,
      zero_mul, add_zero]
    constructor <;> linarith
  · rw [mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hscale]
    have hn : ‖(2 : ℂ) - I‖ ≤ 3 := by
      simpa only [norm_ofNat, norm_I, show (2 : ℝ) + 1 = 3 by norm_num]
        using norm_sub_le (2 : ℂ) I
    calc
      (r / 6) * ‖(2 : ℂ) - I‖ ≤ (r / 6) * 3 :=
        mul_le_mul_of_nonneg_left hn hscale.le
      _ < r := by linarith

theorem cornerSectorThree_inter_ball_nonempty {r : ℝ} (hr : 0 < r) :
    (cornerSectorThree ∩ ball 0 r).Nonempty :=
  ⟨_, cornerSectorThree_small_point hr⟩

theorem cornerSectorFour_inter_ball_nonempty {r : ℝ} (hr : 0 < r) :
    (cornerSectorFour ∩ ball 0 r).Nonempty :=
  ⟨_, cornerSectorFour_small_point hr⟩

theorem isPathConnected_cornerSectorThree_inter_ball {r : ℝ} (hr : 0 < r) :
    IsPathConnected (cornerSectorThree ∩ ball 0 r) :=
  (convex_cornerSectorThree_inter_ball r).isPathConnected
    (cornerSectorThree_inter_ball_nonempty hr)

theorem isPathConnected_cornerSectorFour_inter_ball {r : ℝ} (hr : 0 < r) :
    IsPathConnected (cornerSectorFour ∩ ball 0 r) :=
  (convex_cornerSectorFour_inter_ball r).isPathConnected
    (cornerSectorFour_inter_ball_nonempty hr)

theorem isConnected_cornerSectorThree_inter_ball {r : ℝ} (hr : 0 < r) :
    IsConnected (cornerSectorThree ∩ ball 0 r) :=
  (isPathConnected_cornerSectorThree_inter_ball hr).isConnected

theorem isConnected_cornerSectorFour_inter_ball {r : ℝ} (hr : 0 < r) :
    IsConnected (cornerSectorFour ∩ ball 0 r) :=
  (isPathConnected_cornerSectorFour_inter_ball hr).isConnected

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

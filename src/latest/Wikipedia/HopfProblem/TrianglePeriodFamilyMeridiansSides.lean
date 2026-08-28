import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansElliptic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingHalf

/-!
# Elliptic meridian base points on the actual vertical sides

The positive real normalized Cayley coordinate puts each chosen meridian
base point vertically above its elliptic centre.  The exact height formula
and the actual Ford inequalities place these points on the two vertical
sides of the closed half-Ford triangle.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

/-- The actual unnormalized disc coordinate of the chosen base point. -/
theorem ellipticBasePoint_coe (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ((ellipticBasePoint j r hr hr1 : ℍ) : ℂ) =
      cayley (ellipticCenter j) ((ellipticNeighborhoodRadius j * r : ℝ) : ℂ) := by
  change (((ellipticNeighborhoodChart j).symm (ellipticDiscBase r hr hr1) : ℍ) : ℂ) = _
  rw [ellipticNeighborhoodChart_symm_val, fromDisc_val, cayleyBallDiscScale_val,
    ellipticDiscBase_val, Complex.ofReal_mul]

private theorem ellipticBasePoint_discRadius_pos (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) : 0 < ellipticNeighborhoodRadius j * r :=
  mul_pos (ellipticNeighborhoodRadius_pos j) hr

private theorem ellipticBasePoint_discRadius_lt_one (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) : ellipticNeighborhoodRadius j * r < 1 := by
  calc
    ellipticNeighborhoodRadius j * r ≤ 1 * r :=
      mul_le_mul_of_nonneg_right (ellipticNeighborhoodRadius_le_one j) hr.le
    _ < 1 := by simpa only [one_mul] using hr1

private theorem cayley_real_re (a : ℍ) (u : ℝ) (hu : u < 1) :
    (cayley (a : ℂ) (u : ℂ)).re = a.re := by
  have hd : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by simp
  rw [cayley, hd, Complex.div_ofReal_re]
  simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, UpperHalfPlane.coe_re]
  apply (div_eq_iff (sub_pos.mpr hu).ne').mpr
  ring

private theorem cayley_real_im (a : ℍ) (u : ℝ) :
    (cayley (a : ℂ) (u : ℂ)).im = a.im * (1 + u) / (1 - u) := by
  have hd : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by simp
  rw [cayley, hd, Complex.div_ofReal_im]
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, UpperHalfPlane.coe_im]
  ring

private theorem cayley_real_im_gt (a : ℍ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    a.im < (cayley (a : ℂ) (u : ℂ)).im := by
  rw [cayley_real_im]
  apply (lt_div_iff₀ (sub_pos.mpr hu1)).mpr
  nlinarith [mul_pos a.im_pos hu]

/-- The chosen meridian base point lies on the vertical line through its
actual elliptic centre. -/
theorem ellipticBasePoint_re (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (ellipticBasePoint j r hr hr1 : ℍ).re = (ellipticCenter j).re := by
  change (((ellipticBasePoint j r hr hr1 : ℍ) : ℂ)).re = _
  rw [ellipticBasePoint_coe]
  exact cayley_real_re _ _ (ellipticBasePoint_discRadius_lt_one j r hr hr1)

/-- Exact height of the positive normalized Cayley base point. -/
theorem ellipticBasePoint_im (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (ellipticBasePoint j r hr hr1 : ℍ).im =
      (ellipticCenter j).im * (1 + ellipticNeighborhoodRadius j * r) /
        (1 - ellipticNeighborhoodRadius j * r) := by
  change (((ellipticBasePoint j r hr hr1 : ℍ) : ℂ)).im = _
  rw [ellipticBasePoint_coe]
  exact cayley_real_im _ _

/-- Every chosen meridian base point lies strictly above its elliptic
vertex, not at that vertex or on the lower circular side. -/
theorem ellipticBasePoint_im_gt_center (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (ellipticCenter j).im < (ellipticBasePoint j r hr hr1 : ℍ).im := by
  change (ellipticCenter j).im < (((ellipticBasePoint j r hr hr1 : ℍ) : ℂ)).im
  rw [ellipticBasePoint_coe]
  exact cayley_real_im_gt _ _ (ellipticBasePoint_discRadius_pos j r hr)
    (ellipticBasePoint_discRadius_lt_one j r hr hr1)

private theorem norm_mono_of_re_eq_im_le {a z : ℂ} (hre : z.re = a.re)
    (ha : 0 ≤ a.im) (him : a.im ≤ z.im) : ‖a‖ ≤ ‖z‖ := by
  have hi : a.im ^ 2 ≤ z.im ^ 2 := (sq_le_sq₀ ha (ha.trans him)).mpr him
  apply (sq_le_sq₀ (norm_nonneg a) (norm_nonneg z)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, hre]
  nlinarith

/-- Moving upward along a vertical line preserves the closed half-Ford
region.  This uses its actual strip and circle inequalities. -/
theorem halfFordRegion_vertical_mono (a z : ℍ) (ha : a ∈ halfFordRegion)
    (hre : z.re = a.re) (him : a.im ≤ z.im) : z ∈ halfFordRegion := by
  have hn : ‖(a : ℂ)‖ ≤ ‖(z : ℂ)‖ :=
    norm_mono_of_re_eq_im_le hre a.im_pos.le him
  have hp : ‖(a : ℂ) + 1‖ ≤ ‖(z : ℂ) + 1‖ := by
    apply norm_mono_of_re_eq_im_le
    · simpa only [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re] using
        congrArg (fun x : ℝ => x + 1) hre
    · simpa only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im]
        using a.im_pos.le
    · simpa only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im]
        using him
  refine ⟨⟨hre ▸ ha.1.1, hre ▸ ha.1.2.1, ha.1.2.2.1.trans hp,
    ha.1.2.2.2.trans hn⟩, ?_⟩
  change z.re ≤ -(1 / 2)
  rw [hre]
  exact ha.2

/-- Both genuine elliptic centres are vertices of the closed half-Ford
triangle. -/
theorem ellipticCenter_mem_halfFordRegion (j : Elliptic.Kind) :
    ellipticCenter j ∈ halfFordRegion := by
  cases j
  · change centerOne ∈ halfFordRegion
    have hre : centerOne.re = -(1 / 2) := by
      norm_num [UpperHalfPlane.re, centerOne]
    have hn : ‖(centerOne : ℂ)‖ = 1 := by
      rw [centerOne_val, ← rho_sq, norm_pow, norm_rho, one_pow]
    have hp : ‖(centerOne : ℂ) + 1‖ = 1 := by
      rw [centerOne_val, sub_add_cancel, norm_rho]
    refine ⟨⟨?_, ?_, hp.ge, hn.ge⟩, hre.le⟩
    · rw [hre]
      unfold stripLeft
      linarith [width_pos]
    · rw [hre]
      linarith [stripRight_pos]
  · change centerTwo ∈ halfFordRegion
    have hf : centerTwo ∈ fordRegion ∧ centerTwo.re = stripLeft :=
      (mem_fordRegion_and_re_eq_stripLeft_iff centerTwo).mpr
        ⟨centerTwo_re, centerTwo_im.ge⟩
    refine ⟨hf.1, ?_⟩
    change centerTwo.re ≤ -(1 / 2)
    rw [centerTwo_re]
    linarith [width_pos]

/-- The actual meridian base point belongs to the closed half-Ford
triangle for every positive normalized radius smaller than one. -/
theorem ellipticBasePoint_mem_halfFordRegion (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (ellipticBasePoint j r hr hr1 : ℍ) ∈ halfFordRegion :=
  halfFordRegion_vertical_mono _ _ (ellipticCenter_mem_halfFordRegion j)
    (ellipticBasePoint_re j r hr hr1) (ellipticBasePoint_im_gt_center j r hr hr1).le

/-- The order-three base point is on the right vertical side of the
half-triangle. -/
theorem ellipticBasePoint_three_re (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (ellipticBasePoint .three r hr hr1 : ℍ).re = -(1 / 2) := by
  rw [ellipticBasePoint_re]
  change centerOne.re = -(1 / 2)
  norm_num [UpperHalfPlane.re, centerOne]

/-- The order-four base point is on the left vertical side. -/
theorem ellipticBasePoint_four_re (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (ellipticBasePoint .four r hr hr1 : ℍ).re = stripLeft := by
  rw [ellipticBasePoint_re]
  exact centerTwo_re

theorem ellipticBasePoint_three_rightReflection (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    rightReflection (ellipticBasePoint .three r hr hr1 : ℍ) =
      (ellipticBasePoint .three r hr hr1 : ℍ) :=
  (rightReflection_fixed_iff _).mpr (ellipticBasePoint_three_re r hr hr1)

theorem ellipticBasePoint_four_leftReflection (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    leftReflection (ellipticBasePoint .four r hr hr1 : ℍ) =
      (ellipticBasePoint .four r hr hr1 : ℍ) :=
  (leftReflection_fixed_iff _).mpr (ellipticBasePoint_four_re r hr hr1)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

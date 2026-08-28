import Wikipedia.NoExoticSixSphere.SmoothCornerRounding
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Supported smooth rounding in the actual transverse-radius and height variables

Substitute `q = r² - ‖v‖²` in the planar rounding. At every zero of the
resulting smooth function, the transverse vector is nonzero and the actual
differential is surjective. The rounded domain contains the original corner
and differs from it only in a controlled height and radial band.
-/

noncomputable section

open Function Set Metric
open scoped ContDiff

namespace NoExoticSixSphere.RoundedHandleCorner

open GLOrthonormalization

variable {d : ℕ}

def coordinates (r : ℝ) (p : Vector d × ℝ) : ℝ × ℝ :=
  (p.2, r ^ 2 - ‖p.1‖ ^ 2)

theorem contDiff_coordinates (r : ℝ) : ContDiff ℝ ∞ (coordinates (d := d) r) :=
  contDiff_snd.prodMk (contDiff_const.sub (contDiff_fst.norm_sq ℝ))

theorem fderiv_coordinates_apply (r : ℝ) (p w : Vector d × ℝ) :
    fderiv ℝ (coordinates r) p w = (w.2, -2 * inner ℝ p.1 w.1) := by
  have hf : HasFDerivAt (Prod.fst : Vector d × ℝ → Vector d)
      (ContinuousLinearMap.fst ℝ (Vector d) ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (Prod.snd : Vector d × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ (Vector d) ℝ) p := hasFDerivAt_snd
  have hn := (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p hf
  have hd := (hg.prodMk ((hasFDerivAt_const (r ^ 2) p).sub hn)).fderiv
  change fderiv ℝ (coordinates r) p = _ at hd
  rw [hd]
  apply Prod.ext
  · rfl
  · change 0 - (2 • innerSL ℝ p.1) w.1 = -2 * inner ℝ p.1 w.1
    rw [two_smul, add_apply]
    change 0 - (inner ℝ p.1 w.1 + inner ℝ p.1 w.1) = -2 * inner ℝ p.1 w.1
    ring

def diagonalLift (p : Vector d × ℝ) : Vector d × ℝ :=
  (-(2 * ‖p.1‖ ^ 2)⁻¹ • p.1, 1)

theorem fderiv_coordinates_diagonalLift (r : ℝ) {p : Vector d × ℝ} (hp : p.1 ≠ 0) :
    fderiv ℝ (coordinates r) p (diagonalLift p) = (1, 1) := by
  rw [fderiv_coordinates_apply]
  apply Prod.ext
  · rfl
  · change -2 * inner ℝ p.1 (-(2 * ‖p.1‖ ^ 2)⁻¹ • p.1) = 1
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    have hn : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    field_simp

def level (χ : ContDiffBump (0 : ℝ)) (r : ℝ) : Vector d × ℝ → ℝ :=
  SmoothCornerRounding.level χ ∘ coordinates r

theorem contDiff_level (χ : ContDiffBump (0 : ℝ)) (r : ℝ) :
    ContDiff ℝ ∞ (level (d := d) χ r) :=
  (SmoothCornerRounding.contDiff_level χ).comp (contDiff_coordinates r)

theorem fderiv_level_diagonalLift (χ : ContDiffBump (0 : ℝ)) (r : ℝ)
    {p : Vector d × ℝ} (hp : p.1 ≠ 0) :
    fderiv ℝ (level χ r) p (diagonalLift p) = 2 := by
  have hd := fderiv_comp p
    ((SmoothCornerRounding.contDiff_level χ).differentiable (by simp) (coordinates r p))
    ((contDiff_coordinates r).differentiable (by simp) p)
  change fderiv ℝ (level χ r) p = _ at hd
  rw [hd]
  change fderiv ℝ (SmoothCornerRounding.level χ) (coordinates r p)
    (fderiv ℝ (coordinates r) p (diagonalLift p)) = 2
  rw [fderiv_coordinates_diagonalLift r hp, SmoothCornerRounding.fderiv_level_diagonal]

theorem surjective_fderiv_level_of_ne_zero (χ : ContDiffBump (0 : ℝ)) (r : ℝ)
    {p : Vector d × ℝ} (hp : p.1 ≠ 0) : Surjective (fderiv ℝ (level χ r) p) := by
  intro y
  refine ⟨(y / 2) • diagonalLift p, ?_⟩
  rw [map_smul, fderiv_level_diagonalLift χ r hp]
  change (y / 2) * 2 = y
  ring

theorem transverse_ne_zero_of_level_zero (χ : ContDiffBump (0 : ℝ)) {r : ℝ}
    (hr : 0 < r) {p : Vector d × ℝ} (hp : level χ r p = 0) : p.1 ≠ 0 := by
  intro hv
  have h := SmoothCornerRounding.two_snd_le_level χ (coordinates r p)
  change 2 * (r ^ 2 - ‖p.1‖ ^ 2) ≤ level χ r p at h
  rw [hp, hv, norm_zero] at h
  nlinarith

theorem regular_zero (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)
    {p : Vector d × ℝ} (hp : level χ r p = 0) : Surjective (fderiv ℝ (level χ r) p) :=
  surjective_fderiv_level_of_ne_zero χ r (transverse_ne_zero_of_level_zero χ hr hp)

theorem nonneg_of_corner (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 ≤ r)
    {p : Vector d × ℝ} (hp : 0 ≤ p.2 ∨ p.1 ∈ closedBall (0 : Vector d) r) :
    0 ≤ level χ r p := by
  apply SmoothCornerRounding.nonneg_of_corner
  rcases hp with ht | hv
  · exact Or.inl ht
  · apply Or.inr
    change 0 ≤ r ^ 2 - ‖p.1‖ ^ 2
    have hn : ‖p.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hv
    nlinarith [norm_nonneg p.1]

theorem added_point_bounds (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 ≤ r)
    {p : Vector d × ℝ} (hp : 0 ≤ level χ r p) (ht : p.2 < 0)
    (hv : p.1 ∉ closedBall (0 : Vector d) r) :
    -2 * χ.rOut < p.2 ∧ ‖p.1‖ ^ 2 < r ^ 2 + 2 * χ.rOut := by
  have hn : r < ‖p.1‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hv
  have hq : (coordinates r p).2 < 0 := by
    change r ^ 2 - ‖p.1‖ ^ 2 < 0
    nlinarith [norm_nonneg p.1]
  have h := SmoothCornerRounding.added_point_bounds χ hp ht hq
  refine ⟨h.1, ?_⟩
  have hb : -2 * χ.rOut < r ^ 2 - ‖p.1‖ ^ 2 := h.2
  linarith

theorem nonneg_iff_corner_outside_band (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 ≤ r)
    {p : Vector d × ℝ}
    (hfar : p.2 ≤ -2 * χ.rOut ∨ r ^ 2 + 2 * χ.rOut ≤ ‖p.1‖ ^ 2) :
    0 ≤ level χ r p ↔ 0 ≤ p.2 ∨ p.1 ∈ closedBall (0 : Vector d) r := by
  constructor
  · intro hp
    by_cases ht : 0 ≤ p.2
    · exact Or.inl ht
    · apply Or.inr
      by_contra hv
      have h := added_point_bounds χ hr hp (lt_of_not_ge ht) hv
      rcases hfar with hfar | hfar
      · exact (not_lt_of_ge hfar) h.1
      · exact (not_lt_of_ge hfar) h.2
  · exact nonneg_of_corner χ hr

end NoExoticSixSphere.RoundedHandleCorner

import Wikipedia.SmoothSixDPoincare.SmoothRadialDiffeomorph
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Exact supported smooth shrinking of a whole closed disk

For any factor in `(0, 1]`, the whole unit disk is scaled by that factor.
Outside radius `3/2` every point is fixed. The map has a proved smooth
inverse and belongs to a jointly smooth isotopy with the same support.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothRadial

def shrinkScale (a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((4 * s - 4) / 5)

theorem contDiff_shrinkScale (a : ℝ) : ContDiff ℝ ∞ (shrinkScale a) :=
  contDiff_const.add (contDiff_const.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 5)))

theorem shrinkScale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (s : ℝ) :
    0 < shrinkScale a s :=
  add_pos_of_pos_of_nonneg ha
    (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

theorem shrinkScale_monotone {a : ℝ} (ha₁ : a ≤ 1) : Monotone (shrinkScale a) := by
  intro s t hst
  unfold shrinkScale
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ha₁)
  apply Real.smoothTransition.monotone
  linarith

theorem shrinkScale_inner (a : ℝ) {s : ℝ} (hs : s ≤ 1) : shrinkScale a s = a := by
  rw [shrinkScale, Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp only [mul_zero, add_zero]

theorem shrinkScale_outer (a : ℝ) {s : ℝ} (hs : (3 / 2 : ℝ) ^ 2 ≤ s) :
    shrinkScale a s = 1 := by
  rw [shrinkScale, Real.smoothTransition.one_of_one_le (by nlinarith)]
  ring

theorem shrinkScale_one (s : ℝ) : shrinkScale 1 s = 1 := by
  simp only [shrinkScale, sub_self, zero_mul, add_zero]

/-- The factor varies smoothly between one and the desired shrink factor. -/
def shrinkTimeFactor (a t : ℝ) : ℝ := 1 + (a - 1) * Real.smoothTransition t

theorem shrinkTimeFactor_bounds {a : ℝ} (ha₁ : a ≤ 1) (t : ℝ) :
    a ≤ shrinkTimeFactor a t ∧ shrinkTimeFactor a t ≤ 1 := by
  have ht₀ := Real.smoothTransition.nonneg t
  have ht₁ := Real.smoothTransition.le_one t
  unfold shrinkTimeFactor
  constructor <;> nlinarith

theorem shrinkTimeFactor_zero (a : ℝ) : shrinkTimeFactor a 0 = 1 := by
  simp only [shrinkTimeFactor, Real.smoothTransition.zero, mul_zero, add_zero]

theorem shrinkTimeFactor_one (a : ℝ) : shrinkTimeFactor a 1 = a := by
  simp only [shrinkTimeFactor, Real.smoothTransition.one, mul_one]
  ring

theorem contDiff_shrinkTimeFactor (a : ℝ) : ContDiff ℝ ∞ (shrinkTimeFactor a) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := ⊤)))

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [FiniteDimensional ℝ N]

/-- Exact shrinking on the closed disk, smoothly joined to the identity outside. -/
def shrinkingDiffeomorph {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ :=
  diffeomorph (contDiff_shrinkScale a) (shrinkScale_pos ha ha₁)
    (shrinkScale_monotone ha₁) (show 0 < (3 / 2 : ℝ) by norm_num)
    (fun _ hs => shrinkScale_outer a hs)

theorem shrinkingDiffeomorph_apply {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (x : N) :
    shrinkingDiffeomorph ha ha₁ x = shrinkScale a (‖x‖ ^ 2) • x := rfl

theorem shrinkingDiffeomorph_inner {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {x : N} (hx : ‖x‖ ≤ 1) : shrinkingDiffeomorph ha ha₁ x = a • x := by
  rw [shrinkingDiffeomorph_apply, shrinkScale_inner a (by nlinarith [norm_nonneg x])]

theorem shrinkingDiffeomorph_outer {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    {x : N} (hx : (3 / 2 : ℝ) ≤ ‖x‖) : shrinkingDiffeomorph ha ha₁ x = x := by
  rw [shrinkingDiffeomorph_apply, shrinkScale_outer a
    ((sq_le_sq₀ (by norm_num) (norm_nonneg x)).mpr hx), one_smul]

def shrinkingFamily (a : ℝ) (p : ℝ × N) : N :=
  radialMap (shrinkScale (shrinkTimeFactor a p.1)) p.2

omit [FiniteDimensional ℝ N] in
theorem contMDiff_shrinkingFamily (a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (shrinkingFamily (N := N) a) := by
  have ht : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => shrinkTimeFactor a p.1) :=
    (contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from contDiff_id.norm_sq ℝ).contMDiff.comp
      contMDiff_snd
  have hz : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => (4 * ‖p.2‖ ^ 2 - 4) / 5) := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using
      (((contMDiff_const.mul hn).sub contMDiff_const).mul contMDiff_const :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × N => (4 * ‖p.2‖ ^ 2 - 4) * (5 : ℝ)⁻¹))
  have hs := (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz
  exact (ht.add ((contMDiff_const.sub ht).mul hs)).smul contMDiff_snd

omit [FiniteDimensional ℝ N] in
theorem shrinkingFamily_zero (a : ℝ) (x : N) : shrinkingFamily a (0, x) = x := by
  simp only [shrinkingFamily, shrinkTimeFactor_zero, radialMap, shrinkScale_one, one_smul]

theorem shrinkingFamily_one {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (x : N) :
    shrinkingFamily a (1, x) = shrinkingDiffeomorph ha ha₁ x := by
  rw [shrinkingDiffeomorph_apply]
  simp only [shrinkingFamily, shrinkTimeFactor_one, radialMap]

theorem shrinkingFamily_slices {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞,
      ∀ x, D x = shrinkingFamily a (t, x) := by
  have ht := shrinkTimeFactor_bounds ha₁ t
  exact ⟨shrinkingDiffeomorph (ha.trans_le ht.1) ht.2, fun _ => rfl⟩

theorem shrinkingFamily_outer {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (t : ℝ) {x : N} (hx : (3 / 2 : ℝ) ≤ ‖x‖) : shrinkingFamily a (t, x) = x := by
  have ht := shrinkTimeFactor_bounds ha₁ t
  exact shrinkingDiffeomorph_outer (ha.trans_le ht.1) ht.2 hx

omit [FiniteDimensional ℝ N] in
theorem shrinkingFamily_origin (a t : ℝ) : shrinkingFamily a (t, (0 : N)) = 0 := by
  simp only [shrinkingFamily, radialMap, smul_zero]

/-- Every time slice has the same compact support bound and fixes the center. -/
def shrinkingIsotopy {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    SupportedDiffeomorph.SupportedRelativeIsotopy
      (shrinkingDiffeomorph (N := N) ha ha₁) (closedBall 0 (3 / 2 : ℝ)) {0} where
  family := shrinkingFamily a
  smooth := contMDiff_shrinkingFamily a
  zero := shrinkingFamily_zero a
  one := shrinkingFamily_one ha ha₁
  slices := shrinkingFamily_slices ha ha₁
  fixedOutside := fun t x hx => shrinkingFamily_outer ha ha₁ t
    (le_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h)))
  fixedOn := by
    intro t x hx
    rcases mem_singleton_iff.mp hx with rfl
    exact shrinkingFamily_origin a t

/-- The image is precisely the smaller closed disk, not just a subset of it. -/
theorem shrinkingDiffeomorph_image_unitDisk {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    shrinkingDiffeomorph (N := N) ha ha₁ '' closedBall 0 1 = closedBall 0 a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff, shrinkingDiffeomorph_inner ha ha₁
      (mem_closedBall_zero_iff.mp hx), norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_of_le_one_right ha.le (mem_closedBall_zero_iff.mp hx)
  · intro hy
    have hnorm : ‖a⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      exact (inv_mul_le_iff₀ ha).mpr (by simpa only [mul_one] using mem_closedBall_zero_iff.mp hy)
    refine ⟨a⁻¹ • y, mem_closedBall_zero_iff.mpr hnorm, ?_⟩
    rw [shrinkingDiffeomorph_inner ha ha₁ hnorm, smul_inv_smul₀ ha.ne']

end Wikipedia.SmoothSixDPoincare.SmoothRadial

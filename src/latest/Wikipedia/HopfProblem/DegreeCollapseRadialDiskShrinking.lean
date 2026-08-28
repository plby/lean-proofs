import Wikipedia.SmoothSixDPoincare.SupportedDiskShrinking

/-!
# Disk shrinking with an arbitrarily thin outer collar

The exact unit-disk scaling is supported in any prescribed larger ball.
The whole time family is smooth, and each slice has a genuine smooth inverse.
This permits extension through a tubular chart whose source need not contain
the radius-three-halves ball used by the fixed-radius shrinking construction.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

def scale (R a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (R ^ 2 - 1))

theorem contDiff_scale (R a : ℝ) : ContDiff ℝ ∞ (scale R a) :=
  contDiff_const.add (contDiff_const.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.sub contDiff_const).div_const _)))

theorem scale_pos {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (R s : ℝ) :
    0 < scale R a s :=
  add_pos_of_pos_of_nonneg ha
    (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

theorem scale_monotone {R a : ℝ} (hR : 1 < R) (ha₁ : a ≤ 1) :
    Monotone (scale R a) := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  intro s t hst
  exact add_le_add_right (mul_le_mul_of_nonneg_left
    (Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hden.le))
    (sub_nonneg.mpr ha₁)) a

theorem scale_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    scale R a s = a := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hden.le)]
  simp only [mul_zero, add_zero]

theorem scale_outer {R : ℝ} (hR : 1 < R) (a : ℝ) {s : ℝ} (hs : R ^ 2 ≤ s) :
    scale R a s = 1 := by
  have hden : 0 < R ^ 2 - 1 := by nlinarith
  rw [scale, Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hden).mpr (by linarith))]
  ring

theorem scale_one (R s : ℝ) : scale R 1 s = 1 := by
  simp only [scale, sub_self, zero_mul, add_zero]

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [FiniteDimensional ℝ N]

def family (R a : ℝ) (p : ℝ × N) : N :=
  SmoothRadial.radialMap (scale R (SmoothRadial.shrinkTimeFactor a p.1)) p.2

theorem contMDiff_family (R a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ (family (N := N) R a) := by
  have ht : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => SmoothRadial.shrinkTimeFactor a p.1) :=
    (SmoothRadial.contDiff_shrinkTimeFactor a).contMDiff.comp contMDiff_fst
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from
      contDiff_id.norm_sq ℝ).contMDiff.comp contMDiff_snd
  have hz : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => (‖p.2‖ ^ 2 - 1) / (R ^ 2 - 1)) := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using
      (hn.sub contMDiff_const).mul (contMDiff_const (c := (R ^ 2 - 1)⁻¹))
  exact (ht.add ((contMDiff_const.sub ht).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz))).smul contMDiff_snd

theorem family_zero (R a : ℝ) (x : N) : family R a (0, x) = x := by
  simp only [family, SmoothRadial.shrinkTimeFactor_zero,
    SmoothRadial.radialMap, scale_one, one_smul]

theorem family_slices {R a : ℝ} (hR : 1 < R) (ha : 0 < a) (ha₁ : a ≤ 1) (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞, ∀ x, D x = family R a (t, x) := by
  have ht := SmoothRadial.shrinkTimeFactor_bounds ha₁ t
  exact ⟨SmoothRadial.diffeomorph (contDiff_scale R _)
    (scale_pos (ha.trans_le ht.1) ht.2 R) (scale_monotone hR ht.2)
    (zero_lt_one.trans hR) (fun _ hs => scale_outer hR _ hs), fun _ => rfl⟩

theorem family_outer {R : ℝ} (hR : 1 < R) (a t : ℝ) {x : N} (hx : R ≤ ‖x‖) :
    family R a (t, x) = x := by
  rw [family, SmoothRadial.radialMap, scale_outer hR _
    ((sq_le_sq₀ (zero_lt_one.trans hR).le (norm_nonneg x)).mpr hx), one_smul]

theorem family_one_inner {R : ℝ} (hR : 1 < R) (a : ℝ) {x : N} (hx : ‖x‖ ≤ 1) :
    family R a (1, x) = a • x := by
  rw [family, SmoothRadial.radialMap, SmoothRadial.shrinkTimeFactor_one,
    scale_inner hR a (by nlinarith [norm_nonneg x])]

theorem family_origin (R a t : ℝ) : family R a (t, (0 : N)) = 0 := by
  simp only [family, SmoothRadial.radialMap, smul_zero]

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

import Wikipedia.SmoothSixDPoincare.SupportedDiskShrinking

/-!
# Exact disk shrinking with any prescribed larger support radius

The unit disk can be shrunk while fixing every point outside any radius
strictly greater than one. This permits reuse in an arbitrary open chart
containing a closed face, rather than requiring a fixed extra collar width.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothRadial

def flexibleShrinkScale (r a s : ℝ) : ℝ :=
  a + (1 - a) * Real.smoothTransition ((s - 1) / (r ^ 2 - 1))

theorem contDiff_flexibleShrinkScale (r a : ℝ) : ContDiff ℝ ∞ (flexibleShrinkScale r a) :=
  contDiff_const.add (contDiff_const.mul ((Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).div_const _)))

theorem flexibleShrinkScale_pos {a : ℝ} (r : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) (s : ℝ) :
    0 < flexibleShrinkScale r a s :=
  add_pos_of_pos_of_nonneg ha
    (mul_nonneg (sub_nonneg.mpr ha₁) (Real.smoothTransition.nonneg _))

theorem flexibleShrinkScale_monotone {r a : ℝ} (hr : 1 < r) (ha₁ : a ≤ 1) :
    Monotone (flexibleShrinkScale r a) := by
  have hr₂ : 0 < r ^ 2 - 1 := by nlinarith
  intro s t hst
  unfold flexibleShrinkScale
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (sub_le_sub_right hst 1) hr₂.le))
    (sub_nonneg.mpr ha₁)

theorem flexibleShrinkScale_inner {r : ℝ} (hr : 1 < r) (a : ℝ) {s : ℝ} (hs : s ≤ 1) :
    flexibleShrinkScale r a s = a := by
  have hr₂ : 0 < r ^ 2 - 1 := by nlinarith
  rw [flexibleShrinkScale, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hr₂.le)]
  simp only [mul_zero, add_zero]

theorem flexibleShrinkScale_outer {r : ℝ} (hr : 1 < r) (a : ℝ) {s : ℝ} (hs : r ^ 2 ≤ s) :
    flexibleShrinkScale r a s = 1 := by
  have hr₂ : 0 < r ^ 2 - 1 := by nlinarith
  rw [flexibleShrinkScale, Real.smoothTransition.one_of_one_le
    ((one_le_div hr₂).mpr (sub_le_sub_right hs 1))]
  ring

theorem flexibleShrinkScale_one (r s : ℝ) : flexibleShrinkScale r 1 s = 1 := by
  simp only [flexibleShrinkScale, sub_self, zero_mul, add_zero]

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [FiniteDimensional ℝ N]

def flexibleShrinkingDiffeomorph {r a : ℝ} (hr : 1 < r) (ha : 0 < a) (ha₁ : a ≤ 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ :=
  diffeomorph (contDiff_flexibleShrinkScale r a) (flexibleShrinkScale_pos r ha ha₁)
    (flexibleShrinkScale_monotone hr ha₁) (zero_lt_one.trans hr)
    (fun _ hs => flexibleShrinkScale_outer hr a hs)

def flexibleShrinkingFamily (r a : ℝ) (p : ℝ × N) : N :=
  radialMap (flexibleShrinkScale r (shrinkTimeFactor a p.1)) p.2

omit [FiniteDimensional ℝ N] in
theorem contMDiff_flexibleShrinkingFamily (r a : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞
      (flexibleShrinkingFamily (N := N) r a) := by
  have ht : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => shrinkTimeFactor a p.1) := (contDiff_shrinkTimeFactor a).contMDiff.comp
    (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞ Prod.fst)
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => ‖p.2‖ ^ 2) :=
    (show ContDiff ℝ ∞ (fun x : N => ‖x‖ ^ 2) from contDiff_id.norm_sq ℝ).contMDiff.comp
      (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, N) ∞ Prod.snd)
  have hz : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, N)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => (‖p.2‖ ^ 2 - 1) / (r ^ 2 - 1)) := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using (hn.sub contMDiff_const).mul
      (contMDiff_const (c := (r ^ 2 - 1)⁻¹))
  have hs := (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp hz
  exact (ht.add ((contMDiff_const.sub ht).mul hs)).smul contMDiff_snd

omit [FiniteDimensional ℝ N] in
theorem flexibleShrinkingFamily_zero (r a : ℝ) (x : N) :
    flexibleShrinkingFamily r a (0, x) = x := by
  simp only [flexibleShrinkingFamily, shrinkTimeFactor_zero, radialMap,
    flexibleShrinkScale_one, one_smul]

theorem flexibleShrinkingFamily_slices {r a : ℝ} (hr : 1 < r) (ha : 0 < a) (ha₁ : a ≤ 1)
    (t : ℝ) : ∃ D : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞,
      ∀ x, D x = flexibleShrinkingFamily r a (t, x) := by
  have ht := shrinkTimeFactor_bounds ha₁ t
  exact ⟨flexibleShrinkingDiffeomorph hr (ha.trans_le ht.1) ht.2, fun _ => rfl⟩

omit [FiniteDimensional ℝ N] in
theorem flexibleShrinkingFamily_outer {r : ℝ} (hr : 1 < r) (a t : ℝ) {x : N}
    (hx : r ≤ ‖x‖) : flexibleShrinkingFamily r a (t, x) = x := by
  rw [flexibleShrinkingFamily, radialMap, flexibleShrinkScale_outer hr _
    ((sq_le_sq₀ (zero_lt_one.trans hr).le (norm_nonneg x)).mpr hx), one_smul]

omit [FiniteDimensional ℝ N] in
theorem flexibleShrinkingFamily_inner {r : ℝ} (hr : 1 < r) (a : ℝ) {x : N}
    (hx : ‖x‖ ≤ 1) : flexibleShrinkingFamily r a (1, x) = a • x := by
  rw [flexibleShrinkingFamily, shrinkTimeFactor_one, radialMap,
    flexibleShrinkScale_inner hr a (by nlinarith [norm_nonneg x])]

omit [FiniteDimensional ℝ N] in
theorem flexibleShrinkingFamily_origin (r a t : ℝ) :
    flexibleShrinkingFamily r a (t, (0 : N)) = 0 := by
  simp only [flexibleShrinkingFamily, radialMap, smul_zero]

end Wikipedia.SmoothSixDPoincare.SmoothRadial

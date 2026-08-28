import Wikipedia.HopfProblem.DegreeCollapseNativeLevelVerticalModel
import Wikipedia.HopfProblem.DegreeCollapseScalarHeightChange
import Wikipedia.HopfProblem.DegreeCollapseOrbitPreservingNormalization
import Wikipedia.HopfProblem.DegreeCollapseLocalHeightTranslation

/-!
# A normalized cylinder on the actual whole regular level

An auxiliary scalar height normalizes any positive regular gap. The
native cylinder is still constructed from the original function's level
and original level atlas, not from a replacement model or auxiliary level.
All critical field germs and complete orbit geometry are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem exists_normalized_whole_level_cylinder {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    {a b c : ℝ} (ha : a < c) (hb : c < b)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : {y : M // f y = c}) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ (r : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M)
      (A : PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({y : M // f y = c} × ℝ) M ∞),
      0 < r ∧ r < c - a ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
      (∀ y, W y = 0 ↔ V y = 0) ∧
      (∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
      (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 y, W x = V x) ∧
      (∀ y, range (fun t => G t y) = range (fun t => F t y) ∧
        (∀ p, Tendsto (fun t => G t y) atTop (𝓝 p) ↔ Tendsto (fun t => F t y) atTop (𝓝 p)) ∧
        ∀ p, Tendsto (fun t => G t y) atBot (𝓝 p) ↔ Tendsto (fun t => F t y) atBot (𝓝 p)) ∧
      A.source = univ ∧ A.target = FlowCancellation.levelBasin G f c ∧
      (∀ p, A p = G p.2 p.1) ∧
      (∀ p, p.2 ∈ Icc (0 : ℝ) 1 → f (A p) = c - r * p.2) ∧
      ∀ y ∈ A.target, W y = VectorField.mpullback 𝓘(ℝ, E)
        (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) A.symm FlowSuspension.nativeVerticalField y := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let r : ℝ := (c - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr ha) (by norm_num)
  have hrbound : r < c - a := by dsimp [r]; linarith
  let g : M → ℝ := fun y => f y / r
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g := hf.div_const r
  have hcrit : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f :=
    criticalPoints_height_div_const hf hr.ne'
  have hdescent : ∀ y, y ∉ ManifoldMorse.criticalPoints E g →
      mvfderiv 𝓘(ℝ, E) g y (V y) < 0 := by
    intro y hy
    rw [hcrit] at hy
    exact (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (V y)).mpr
      (hdesc y hy)
  have hregular : ∀ y, g y ∈ Icc (a / r) (b / r) →
      y ∉ ManifoldMorse.criticalPoints E g := by
    intro y hy
    rw [hcrit]
    exact hband y ⟨(div_le_div_iff_of_pos_right hr).mp hy.1,
      (div_le_div_iff_of_pos_right hr).mp hy.2⟩
  obtain ⟨U, W, G, hU, hIU, hW, hG, hzero, hneg, hspeed, hgerm, -, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hg hV hdescent F hF hregular
  have hnegf (y : M) (hy : y ∉ ManifoldMorse.criticalPoints E f) :
      mvfderiv 𝓘(ℝ, E) f y (W y) < 0 :=
    (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (W y)).mp
      (hneg y (hcrit ▸ hy))
  obtain ⟨A, hsource, htarget, hformula, hfield⟩ :=
    FlowSuspension.exists_native_level_flow_cylinder_with_field hf hreg hW G hG
      (fun y hy => hnegf y (hreg y hy)) z
  have hc : c / r ∈ Icc (a / r) (b / r) :=
    ⟨div_le_div_of_nonneg_right ha.le hr.le, div_le_div_of_nonneg_right hb.le hr.le⟩
  refine ⟨r, W, G, A, hr, hrbound, hW, hG, hzero, hnegf,
    (fun y hy => hgerm y (hcrit ▸ hy)), hgeometry, hsource, htarget, hformula, ?_, hfield⟩
  intro p ht
  have hi : g p.1 = c / r := by change f p.1 / r = c / r; rw [p.1.property]
  have he : c / r - p.2 = (c - r * p.2) / r := by field_simp
  have hend : g p.1 - p.2 ∈ Icc (a / r) (b / r) := by
    rw [hi, he]
    constructor
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [ht.2]
    · apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [mul_nonneg hr.le ht.1]
  have hh := native_local_height_translation hg G hG hU hIU hspeed p.1 p.2 (hi ▸ hc) hend
  rw [hi, he] at hh
  rw [hformula]
  exact (div_left_inj' hr.ne').mp hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

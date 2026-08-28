import Wikipedia.HopfProblem.DegreeCollapseScalarHeightChange
import Wikipedia.HopfProblem.DegreeCollapseEuclideanFlowCylinder
import Wikipedia.HopfProblem.DegreeCollapseLocalHeightTranslation
import Wikipedia.HopfProblem.DegreeCollapseNativePhaseCylinder

/-!
# An actual full native cylinder inside any positive regular height gap

Normalize an auxiliary scalar multiple of the height, preserving the
original critical germs, descent, zeros, and complete orbit geometry.
The regular-level cylinder is put in the finite coordinate model used by
the endpoint charts. Its full source and actual vertical field are
retained, and the original height has a proved positive constant speed
on the unit time slab. No unit lower bound on the height gap is assumed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem exists_arbitrary_gap_flow_cylinder {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = m + 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    {a b c : ℝ} (ha : a < c) (hb : c < b)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    {x : M} (hx : f x = c) :
    ∃ (r : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M)
      (U : Set (Fin m → ℝ))
      (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞),
      0 < r ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
      (∀ y, W y = 0 ↔ V y = 0) ∧
      (∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
      (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, W z = V z) ∧
      (∀ y, range (fun t => G t y) = range (fun t => F t y) ∧
        (∀ p, Tendsto (fun t => G t y) atTop (𝓝 p) ↔ Tendsto (fun t => F t y) atTop (𝓝 p)) ∧
        ∀ p, Tendsto (fun t => G t y) atBot (𝓝 p) ↔ Tendsto (fun t => F t y) atBot (𝓝 p)) ∧
      IsOpen U ∧ (0 : Fin m → ℝ) ∈ U ∧ Φ.source = U ×ˢ univ ∧
      (∀ t : ℝ, Φ (0, t) = G t x) ∧
      (∀ z ∈ Φ.source, z.2 ∈ Icc (0 : ℝ) 1 → f (Φ z) = c - r * z.2) ∧
      ∀ y ∈ Φ.target, W y = FlowConstruction.partialChartField Φ.symm
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y := by
  let r : ℝ := (c - a) / 2
  have hr : 0 < r := div_pos (sub_pos.mpr ha) (by norm_num)
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
  obtain ⟨H, W, G, hH, hIH, hW, hG, hzero, hneg, hspeed, hgerms, _, hgeometry⟩ :=
    exists_orbit_preserving_band_normalization hg hV hdescent F hF hregular
  have hc : c / r ∈ Icc (a / r) (b / r) :=
    ⟨div_le_div_of_nonneg_right ha.le hr.le, div_le_div_of_nonneg_right hb.le hr.le⟩
  have hreg (y : M) (hy : g y = c / r) : y ∉ ManifoldMorse.criticalPoints E g :=
    hregular y (hy ▸ hc)
  have hboundary (y : M) (hy : g y = c / r) : mvfderiv 𝓘(ℝ, E) g y (W y) < 0 := by
    rw [hspeed y (hy ▸ hIH hc)]
    norm_num
  obtain ⟨O, ι, A, hO, h0O, hι0, hAsource, hlevel, hAmap, hAfield⟩ :=
    FlowCancellation.exists_euclidean_level_flow_cylinder hg hreg hW G hG hboundary
      (show g x = c / r by change f x / r = c / r; rw [hx])
  let e : (Fin m → ℝ) ≃L[ℝ] RegularLevel.Model E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [RegularLevel.Model, hdim])
  let Q := PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hQtarget : Q.target = O := by
    ext z
    change (z ∈ (univ : Set (RegularLevel.Model E)) ∧ z ∈ O) ↔ z ∈ O
    simp only [mem_univ, true_and]
  have hQ0 : (0 : Fin m → ℝ) ∈ Q.source := by
    change (0 : Fin m → ℝ) ∈ univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨mem_univ _, h0O⟩
  obtain ⟨Φ, hΦsource, _, hΦmap, hΦfield⟩ :=
    FlowSuspension.exists_native_phase_cylinder A hAsource Q hQtarget
      (fun _ => (0 : ℝ)) contDiff_const W hAfield
  have hmap (z : (Fin m → ℝ) × ℝ) : Φ z = A (Q z.1, z.2) := by
    rw [hΦmap, add_zero]
  have hnegf (y : M) (hy : y ∉ ManifoldMorse.criticalPoints E f) :
      mvfderiv 𝓘(ℝ, E) f y (W y) < 0 :=
    (descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hr (W y)).mp
      (hneg y (hcrit ▸ hy))
  refine ⟨r, W, G, Q.source, Φ, hr, hW, hG, hzero, hnegf,
    (fun y hy => hgerms y (hcrit ▸ hy)), hgeometry, Q.open_source, hQ0,
    hΦsource, ?_, ?_, hΦfield⟩
  · intro t
    rw [hmap, hAmap]
    change G t (ι (e 0)) = G t x
    rw [map_zero, hι0]
  · intro z hz ht
    rw [hΦsource] at hz
    have hQo : Q z.1 ∈ O := hQtarget ▸ Q.map_source' hz.1
    have hi : g (ι (Q z.1)) = c / r := hlevel _ hQo
    have he : c / r - z.2 = (c - r * z.2) / r := by field_simp
    have hend : g (ι (Q z.1)) - z.2 ∈ Icc (a / r) (b / r) := by
      rw [hi, he]
      constructor
      · apply div_le_div_of_nonneg_right _ hr.le
        dsimp [r]
        nlinarith [ht.2]
      · apply div_le_div_of_nonneg_right _ hr.le
        nlinarith [mul_nonneg hr.le ht.1]
    have hh := native_local_height_translation hg G hG hH hIH hspeed
      (ι (Q z.1)) z.2 (hi ▸ hc) hend
    rw [hi, he] at hh
    have hhf : f (G z.2 (ι (Q z.1))) = c - r * z.2 := (div_left_inj' hr.ne').mp hh
    rw [hmap, hAmap]
    exact hhf

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

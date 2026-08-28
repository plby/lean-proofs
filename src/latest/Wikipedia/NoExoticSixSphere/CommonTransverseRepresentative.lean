import Wikipedia.NoExoticSixSphere.ManifoldTransverseRepresentative

/-!
# A common transverse representative preserving an open target condition

Intersect the two full-measure sets of actual affine parameters before
choosing a parameter. Compactness keeps the perturbed image in the given
open set. Scaling the small parameter gives the genuine homotopy.
-/

noncomputable section

open Set Function Filter Topology
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily ManifoldIntersectionFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem eventually_fixed_time_image_in_open (k : ℝ → Sphere 3 → M)
    (hk : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry k))
    (t : ℝ) {V : Set M} (hV : IsOpen V) (hkV : ∀ x, k t x ∈ V) :
    ∀ᶠ p in 𝓝 (0 : Parameters e),
      ∀ x : Sphere 3, ManifoldAffineSphereFamily.map e r k p t x ∈ V := by
  obtain ⟨δ, hδ, _, hsmooth⟩ := exists_smooth_parameter_ball e r k hk
  have hcont : ContinuousOn (fun q : Parameters e × (ℝ × Sphere 3) ↦
      ManifoldAffineSphereFamily.map e r k q.1 q.2.1 q.2.2) {q | ‖q.1‖ < δ} :=
    hsmooth.continuousOn
  have ho : IsOpen {q : Parameters e × (ℝ × Sphere 3) | ‖q.1‖ < δ} :=
    isOpen_lt continuous_fst.norm continuous_const
  have h : ∀ᶠ p in 𝓝 (0 : Parameters e), ∀ x ∈ (univ : Set (Sphere 3)),
      ManifoldAffineSphereFamily.map e r k p t x ∈ V := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro x _
    have hz : (0, (t, x)) ∈ {q : Parameters e × (ℝ × Sphere 3) | ‖q.1‖ < δ} := by
      change ‖(0 : Parameters e)‖ < δ
      simpa only [norm_zero] using hδ
    have hc : ContinuousAt (fun q : Parameters e × (ℝ × Sphere 3) ↦
        ManifoldAffineSphereFamily.map e r k q.1 q.2.1 q.2.2) (0, (t, x)) :=
      hcont.continuousAt (ho.mem_nhds hz)
    have hi : Continuous (fun q : Parameters e × Sphere 3 ↦ (q.1, (t, q.2))) :=
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
    have hj : ContinuousAt (fun q : Parameters e × Sphere 3 ↦
        ManifoldAffineSphereFamily.map e r k q.1 t q.2) (0, x) :=
      ContinuousAt.comp (x := (0, x))
        (f := fun q : Parameters e × Sphere 3 ↦ (q.1, (t, q.2)))
        (g := fun q : Parameters e × (ℝ × Sphere 3) ↦
          ManifoldAffineSphereFamily.map e r k q.1 q.2.1 q.2.2) hc hi.continuousAt
    apply hj.preimage_mem_nhds
    apply hV.mem_nhds
    simpa only [map_zero_parameter] using hkV x
  exact h.mono (fun _ hp x ↦ hp x (mem_univ x))

include e r in
theorem exists_smooth_common_transverse_homotopic (k f g : C(Sphere 3, M))
    (hk : ContMDiff (𝓡 3) (𝓡 6) ∞ k) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) {V : Set M} (hV : IsOpen V)
    (hkV : ∀ x, k x ∈ V) :
    ∃ K : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧ k.Homotopic K ∧
      (∀ x, K x ∈ V) ∧
      (∀ x y, K x = f y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) K x).coprod (mfderiv (𝓡 3) (𝓡 6) f y))) ∧
      (∀ x y, K x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) K x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) := by
  let k₀ : ℝ → Sphere 3 → M := fun _ x ↦ k x
  let f₀ : ℝ → Sphere 3 → M := fun _ x ↦ f x
  let g₀ : ℝ → Sphere 3 → M := fun _ x ↦ g x
  have hk₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry k₀) :=
    hk.comp contMDiff_snd
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  have hg₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g₀) :=
    hg.comp contMDiff_snd
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover 6 M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r k₀ hk₀
  have hkeep := e.eventually_fixed_time_image_in_open r k₀ hk₀ (1 / 2) hV hkV
  obtain ⟨ε, hε, hεkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hae₁ := ae_spatial_generic_in_charts e r k₀ f₀ hk₀ hf₀ addHaar
    S hS.countable C hC.countable (1 / 2)
  have hae₂ := ae_spatial_generic_in_charts e r k₀ g₀ hk₀ hg₀ addHaar
    S hS.countable C hC.countable (1 / 2)
  obtain ⟨p, hgen, hdist⟩ := (Measure.dense_of_ae (hae₁.and hae₂)).exists_dist_lt 0
    (lt_min hδ hε)
  have hp : ‖p‖ < min δ ε := by simpa only [dist_zero_left] using hdist
  have hpδ := (lt_min_iff.mp hp).1
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (ManifoldAffineSphereFamily.map e r k₀ p)) :=
    hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  have hK : ContMDiff (𝓡 3) (𝓡 6) ∞
      (ManifoldAffineSphereFamily.map e r k₀ p (1 / 2)) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  let K : C(Sphere 3, M) := ⟨ManifoldAffineSphereFamily.map e r k₀ p (1 / 2), hK.continuous⟩
  have hsmall (s : unitInterval) : ‖(s : ℝ) • p‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg p) s.property.2).trans_lt hpδ
  have hparam : Continuous (fun q : unitInterval × Sphere 3 ↦
      ((q.1 : ℝ) • p, ((1 / 2 : ℝ), q.2))) :=
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
      (continuous_const.prodMk continuous_snd)
  have H : k.Homotopy K := {
    toFun q := ManifoldAffineSphereFamily.map e r k₀ ((q.1 : ℝ) • p) (1 / 2) q.2
    continuous_toFun := hsmooth.continuousOn.comp_continuous hparam (fun q ↦ hsmall q.1)
    map_zero_left x := by
      change ManifoldAffineSphereFamily.map e r k₀ ((0 : ℝ) • p) (1 / 2) x = k x
      rw [zero_smul, map_zero_parameter]
    map_one_left x := by
      change ManifoldAffineSphereFamily.map e r k₀ ((1 : ℝ) • p) (1 / 2) x = K x
      rw [one_smul]
      rfl }
  refine ⟨K, hK, ⟨H⟩, ?_, ?_, ?_⟩
  · exact hεkeep (by simpa only [Metric.mem_ball, dist_zero_right]
      using (lt_min_iff.mp hp).2)
  · exact native_transverse_of_spatial_generic e r k₀ f₀ hk₀ hf₀
      S C hScov hCcov (1 / 2) (by constructor <;> norm_num) p
      (hmem p hpδ (1 / 2)) hP hgen.1
  · exact native_transverse_of_spatial_generic e r k₀ g₀ hk₀ hg₀
      S C hScov hCcov (1 / 2) (by constructor <;> norm_num) p
      (hmem p hpδ (1 / 2)) hP hgen.2

end NoExoticSixSphere.EuclideanEmbedding

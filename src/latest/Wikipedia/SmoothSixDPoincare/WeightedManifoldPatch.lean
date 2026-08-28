import Wikipedia.SmoothSixDPoincare.WeightedDerivativePerturbation
import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ChartCoordinateApproximation
import Wikipedia.SmoothSixDPoincare.ChartMapHomotopy

/-!
# Weighted derivative repair in the original target manifold

A scalar-weighted chart translation may fix a boundary while changing its
transverse derivative. Cutoff coordinates globalize the analytic good-parameter
argument. The resulting native derivative is injective wherever the old map
and weight have trivial common kernel, on a prescribed low-dimensional locus
inside the coordinate plateau.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {B E G F H H' X N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Repair the native derivative along a small-dimensional locus in one target chart, fixing
the zero set of the scalar weight and retaining any sufficiently-small-parameter property. -/
theorem exists_weighted_immersive_patch_with_property
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {β χ : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {S : Set X}
    (hplateau : ∀ x ∈ S, b x ∈ interior {y | χ y = 1})
    (hcommon : ∀ x ∈ S, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 →
      fderiv ℝ β (b x) v = 0 → v = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F)
    (Q : (E → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (ChartMapPerturbation.perturb c f β a)) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ Q g ∧
      f.HomotopicRel g {y | β y = 0} ∧
      ∀ x ∈ S, Function.Injective (mfderiv 𝓘(ℝ, E) J g (b x)) := by
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k := fun _ =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff
    hcompact hsupport
  have hQmem : {a : F | Q (ChartMapPerturbation.perturb c f β a)} ∈ 𝓝 0 := hQ
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨a, ha, -, hkernel⟩ := WeightedPerturbation.exists_small_parameter_with_common_kernel
    hb hk hβ hdim (lt_min hε hδ)
  have haε : ‖a‖ < ε := (lt_min_iff.mp ha).1
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).2
  have hv := hvalid a haε
  have hsmooth := ChartMapPerturbation.contMDiff_perturb c hf hβ.contMDiff hsupport hv
  let g : C(E, N) := ⟨ChartMapPerturbation.perturb c f β a, hsmooth.continuous⟩
  have hQg : Q g := hδkeep (show a ∈ Metric.ball 0 δ by
    simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine ⟨g, hsmooth, hQg,
    ⟨ChartMapPerturbation.homotopyRel c hf hβ.contMDiff hsupport hvalid haε⟩, ?_⟩
  intro x hx
  have hxplateau := hplateau x hx
  have hsource (y : E) (hy : χ y = 1) : f y ∈ c.source :=
    hχsupport (subset_tsupport χ (by change χ y ≠ 0; rw [hy]; exact one_ne_zero))
  have hxone : χ (b x) = 1 := interior_subset (s := {y | χ y = 1}) hxplateau
  have hfx := hsource (b x) hxone
  have hgx : g (b x) ∈ c.source := ChartMapPerturbation.perturb_mem_source c f β hv hfx
  have heqold : k =ᶠ[𝓝 (b x)] (c ∘ f) := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    exact ChartMapPerturbation.cutoffCoordinates_eq_of_one c f χ
      (interior_subset (s := {y | χ y = 1}) hy)
  have heqnew : (c ∘ g) =ᶠ[𝓝 (b x)] WeightedPerturbation.perturb k β a := by
    filter_upwards [isOpen_interior.mem_nhds hxplateau] with y hy
    have hyone : χ y = 1 := interior_subset (s := {y | χ y = 1}) hy
    change c (ChartMapPerturbation.perturb c f β a y) = _
    rw [ChartMapPerturbation.chart_perturb c f β hv (hsource y hyone)]
    simp only [ChartMapPerturbation.coordinateFamily, WeightedPerturbation.perturb,
      k, ChartMapPerturbation.cutoffCoordinates, hyone, one_smul]
  apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgx).mp
  change Function.Injective (fderiv ℝ (c ∘ g) (b x))
  rw [heqnew.fderiv_eq]
  intro v w hvw
  have hzero : fderiv ℝ (WeightedPerturbation.perturb k β a) (b x) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  obtain ⟨hkzero, hβzero⟩ := (hkernel x (v - w)).mp hzero
  have hnative : mfderiv 𝓘(ℝ, E) J f (b x) (v - w) = 0 := by
    apply (fderiv_chart_eq_zero_iff c (hf.mdifferentiableAt (by simp)) hfx (v - w)).mp
    rw [← heqold.fderiv_eq]
    exact hkzero
  exact sub_eq_zero.mp (hcommon x hx (v - w) hnative hβzero)

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

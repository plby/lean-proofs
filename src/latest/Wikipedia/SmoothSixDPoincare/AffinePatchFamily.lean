import Wikipedia.SmoothSixDPoincare.AffineManifoldPatch
import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability

/-!
# Smooth affine patch families preserve compact immersive regions

The localized patch depends smoothly on both its parameter and the source
point throughout an open neighborhood of the zero parameter. Compact native
derivative stability can therefore be applied to this actual family.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)

variable {G F H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

theorem affinePatch_zero (f : Plane → N) (β : Plane → ℝ) :
    affinePatch c f β (0 : F × F) = f := by
  funext x
  change ChartMapPerturbation.perturb c f β (PlaneImmersion.displacement β 0 x) x = f x
  rw [PlaneImmersion.displacement_zero, ChartMapPerturbation.perturb_zero]

/-- Joint smoothness at every parameter-point pair with valid displacement. -/
theorem contMDiffAt_affinePatch_family {f : Plane → N} {β : Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : (F × F) × Plane)
    (hvalid : ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β q.1 q.2)) :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Plane)) J ∞
      (fun r : (F × F) × Plane => affinePatch c f β r.1 r.2) q := by
  have hid : ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, Plane))
      𝓘(ℝ, (F × F) × Plane) ∞ (fun r : (F × F) × Plane => r) q :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst, contMDiffAt_snd⟩
  have hd := (PlaneImmersion.contDiff_displacement_family (F := F) hβ).contMDiff.contMDiffAt
    |>.comp q hid
  exact (ChartMapPerturbation.contMDiffAt_perturb c hf hβ.contMDiff hsupport
    (PlaneImmersion.displacement β q.1 q.2, q.2) hvalid).comp q
      (f := fun r : (F × F) × Plane => (PlaneImmersion.displacement β r.1 r.2, r.2))
      (hd.prodMk contMDiffAt_snd)

/-- Compact target-chart constraints survive every sufficiently small affine patch parameter. -/
theorem eventually_affinePatch_maps_compact_into_open {f : Plane → N} {β : Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Plane} (hK : IsCompact K) {U : Set N} (hU : IsOpen U) (hmap : MapsTo f K U) :
    ∀ᶠ A : F × F in 𝓝 0, MapsTo (affinePatch c f β A) K U := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hvalid : ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β (0 : F × F) x) := by
    rw [PlaneImmersion.displacement_zero]
    exact ChartMapPerturbation.valid_zero c f β hsupport
  have hc := (contMDiffAt_affinePatch_family c hf hβ hsupport (0, x) hvalid).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  rw [affinePatch_zero]
  exact hmap hx

variable [J.Boundaryless] [IsManifold J ∞ N]

/-- The affine chart patch preserves injective native derivatives on an old compact set
for every sufficiently small parameter. -/
theorem eventually_affinePatch_injective_derivative {f : Plane → N} {β : Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x)) :
    ∀ᶠ A : F × F in 𝓝 0,
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J (affinePatch c f β A) x) := by
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff
    hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ := PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  let W : Set ((F × F) × Plane) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily : ContMDiffOn (𝓘(ℝ, F × F).prod 𝓘(ℝ, Plane)) J ∞
      (fun q : (F × F) × Plane => affinePatch c f β q.1 q.2) W := by
    intro q hq
    exact (contMDiffAt_affinePatch_family c hf hβ hsupport q
      (hvalid _ (hδbound q.1 hq q.2))).contMDiffWithinAt
  apply eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F × F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    change Function.Injective (mfderiv 𝓘(ℝ, Plane) J (affinePatch c f β (0 : F × F)) x)
    rw [affinePatch_zero]
    exact hinj x hx

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

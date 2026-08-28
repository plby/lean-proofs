import Wikipedia.SmoothSixDPoincare.PlaneEmbeddingPerturbation
import Wikipedia.SmoothSixDPoincare.CompactAffineDisplacement
import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ChartCoordinateApproximation
import Wikipedia.SmoothSixDPoincare.VariableChartPerturbation

/-!
# A compactly supported affine embedding patch in a native manifold

On the unit plateau of a source cutoff, the actual target-chart perturbation
agrees with an affine perturbation of globally smooth cutoff coordinates.
The map is unchanged where the cutoff vanishes. A small good parameter gives
injective native derivatives on the open plateau and a closed embedding on
any compact subset of it.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)

variable {G F H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

def affinePatch (f : Plane → N) (β : Plane → ℝ) (A : F × F) : Plane → N :=
  ChartMapPerturbation.variablePerturb c f β (PlaneImmersion.displacement β A)

theorem chart_affinePatch_on_plateau {f : Plane → N} {β χ : Plane → ℝ} {A : F × F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχ : ∀ x ∈ tsupport β, χ x = 1)
    (hvalid : ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x))
    {x : Plane} (hx : β x = 1) :
    c (affinePatch c f β A x) =
      PlaneImmersion.perturb (ChartMapPerturbation.cutoffCoordinates c f χ) A x := by
  have hxs : x ∈ tsupport β := subset_tsupport β (by change β x ≠ 0; rw [hx]; norm_num)
  change c (ChartMapPerturbation.perturb c f β (PlaneImmersion.displacement β A x) x) = _
  rw [ChartMapPerturbation.chart_perturb c f β (hvalid x) (hsupport hxs)]
  simp only [ChartMapPerturbation.coordinateFamily, PlaneImmersion.perturb,
    ChartMapPerturbation.cutoffCoordinates, PlaneImmersion.displacement, hx, hχ x hxs, one_smul]

theorem contMDiff_affinePatch {f : Plane → N} {β : Plane → ℝ} {A : F × F}
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hvalid : ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x)) :
    ContMDiff 𝓘(ℝ, Plane) J ∞ (affinePatch c f β A) := by
  have hd := (PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
    (contDiff_const (c := A) |>.prodMk contDiff_id)
  intro x
  exact ChartMapPerturbation.contMDiffAt_variablePerturb c hsupport hf.contMDiffAt
    hβ.contMDiff.contMDiffAt hd.contMDiff.contMDiffAt (hvalid x)

variable [FiniteDimensional ℝ F] [T2Space N]

/-- The new embedding patch can retain any property satisfied by every sufficiently small
parameter in this actual affine family. No global injectivity is asserted. -/
theorem exists_affine_embedding_patch_with_property (f : C(Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) {β χ : Plane → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) (hχone : ∀ x ∈ tsupport β, χ x = 1)
    (hdim : 5 ≤ Module.finrank ℝ F) (Q : (Plane → N) → Prop)
    (hQ : ∀ᶠ A : F × F in 𝓝 0, Q (affinePatch c f β A))
    {K : Set Plane} (hK : IsCompact K)
    (hKsub : K ⊆ interior {x | β x = 1}) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧ Q g ∧
      Nonempty (f.HomotopyRel g {x | β x = 0}) ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ interior {x | β x = 1}, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro x hx
    exact hχsupport (subset_tsupport χ (by change χ x ≠ 0; rw [hχone x hx]; norm_num))
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, F) ∞ k := fun x =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff
    hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ := PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  have hQmem : {A : F × F | Q (affinePatch c f β A)} ∈ 𝓝 0 := hQ
  obtain ⟨η, hη, hηkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨A, hA, -, hinj, hderiv⟩ :=
    PlaneImmersion.exists_small_affine_injective_immersion hk hdim (lt_min hδ hη)
  have hbound : ∀ x, ‖PlaneImmersion.displacement β A x‖ < ε :=
    hδbound A (lt_of_lt_of_le hA (min_le_left _ _))
  have hv : ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x) :=
    fun x => hvalid _ (hbound x)
  have hsmooth := contMDiff_affinePatch c hf hβ hsupport hv
  let g : C(Plane, N) := ⟨affinePatch c f β A, hsmooth.continuous⟩
  have hcoord (x : Plane) (hx : β x = 1) : c (g x) = PlaneImmersion.perturb k A x :=
    chart_affinePatch_on_plateau c hsupport hχone hv hx
  have hQg : Q g := hηkeep (show A ∈ Metric.ball 0 η by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (lt_of_lt_of_le hA (min_le_right δ η)))
  refine ⟨g, hsmooth, hQg, ?_, ?_, ?_⟩
  · have hd := (PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
      (contDiff_const (c := A) |>.prodMk contDiff_id)
    exact ⟨ChartMapPerturbation.variableHomotopyRel c f.continuous hβ.continuous hsupport
      hd.continuous hvalid hbound (fun _ hx => Or.inl hx)⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    change g x = g y at hxy
    apply Subtype.ext
    apply hinj
    rw [← hcoord x (interior_subset (s := {z | β z = 1}) (hKsub x.property)),
      ← hcoord y (interior_subset (s := {z | β z = 1}) (hKsub y.property)), hxy]
  · intro x hx
    have hβx : β x = 1 := interior_subset (s := {z | β z = 1}) hx
    have hxs : f x ∈ c.source :=
      hsupport (subset_tsupport β (by change β x ≠ 0; rw [hβx]; norm_num))
    have hgs : g x ∈ c.source :=
      ChartMapPerturbation.perturb_mem_source c f β (hv x) hxs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 x] PlaneImmersion.perturb k A := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hcoord y (interior_subset (s := {z | β z = 1}) hy)
    change Function.Injective (fderiv ℝ (c ∘ g) x)
    rw [heq.fderiv_eq]
    exact hderiv x

/-- An actual smooth map becomes an embedded immersion on a compact new patch through a
homotopy fixing every zero of the cutoff. -/
theorem exists_affine_embedding_patch (f : C(Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) {β χ : Plane → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) (hχone : ∀ x ∈ tsupport β, χ x = 1)
    (hdim : 5 ≤ Module.finrank ℝ F) {K : Set Plane} (hK : IsCompact K)
    (hKsub : K ⊆ interior {x | β x = 1}) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧
      Nonempty (f.HomotopyRel g {x | β x = 0}) ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ interior {x | β x = 1}, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  obtain ⟨g, hg, -, hhom, hemb, hderiv⟩ := exists_affine_embedding_patch_with_property c f hf
    hβ hχ hcompact hχsupport hχone hdim (fun _ => True) (Eventually.of_forall (fun _ => trivial))
    hK hKsub
  exact ⟨g, hg, hhom, hemb, hderiv⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

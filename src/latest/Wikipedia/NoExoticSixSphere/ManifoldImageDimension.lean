import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Dimension bounds for smooth images of Lindelöf manifolds

In each chart a smooth map is locally Lipschitz, so its image has Hausdorff
dimension at most the dimension of the model space. A countable chart cover of a
Lindelöf manifold gives the same bound globally, including on an open subdomain.
This supplies the point-avoidance ingredient for sphere-connectivity arguments.
-/

open scoped Manifold ContDiff Topology ENNReal
open Set Module

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C¹` map on an open domain does not increase Hausdorff dimension. -/
theorem dimH_image_le_of_contDiffOn_isOpen {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) : dimH (f '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  obtain ⟨C, U, hU, hL⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The image of the part of an open domain lying in one chart has the model's dimension bound. -/
theorem dimH_image_chart_le {f : M → F} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (x : M) :
    dimH (f '' ((modelChartPartialDiffeomorph (I := I) x).source ∩ s)) ≤ finrank ℝ E := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hV : IsOpen V :=
    c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hs
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right).contDiffOn
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source' hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        have hc : c.symm (c y) = y := c.left_inv' hyc
        rwa [hc]
      · exact congrArg f (c.left_inv' hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target' hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact (dimH_image_le_of_contDiffOn_isOpen hV (hfc.of_le (by simp))).trans
    ((dimH_mono (subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

/-- A smooth image of an open part of a Lindelöf manifold has Hausdorff dimension at most
the manifold's dimension. No metric or Hausdorff-dimension assumption on the source is needed. -/
theorem dimH_image_manifold_le [LindelofSpace M] {f : M → F} {s : Set M}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) :
    dimH (f '' s) ≤ finrank ℝ E := by
  let U : M → Set M := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).source
  have hU : ∀ x, IsOpen (U x) := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).open_source
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x ↦ iSup_le (fun _ ↦ dimH_image_chart_le hs hf x))

/-- The same bound for the entire range of a smooth map from a Lindelöf manifold. -/
theorem dimH_range_manifold_le [LindelofSpace M] {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) : dimH (range f) ≤ finrank ℝ E := by
  rw [← image_univ]
  exact dimH_image_manifold_le isOpen_univ hf.contMDiffOn

/-- In strictly higher Euclidean dimension, the complement of a smooth manifold image is dense. -/
theorem dense_compl_manifold_image [LindelofSpace M] [FiniteDimensional ℝ F]
    {f : M → F} {s : Set M} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : finrank ℝ E < finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

/-- A smooth map from a Lindelöf manifold cannot cover a nonempty manifold of larger dimension. -/
theorem not_surjective_contMDiff_of_dim_lt [LindelofSpace M] [FiniteDimensional ℝ F]
    {G N : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [Nonempty N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (hd : finrank ℝ E < finrank ℝ F) :
    ¬ Function.Surjective f := by
  intro hsurj
  let y : N := Classical.choice inferInstance
  let d := modelChartPartialDiffeomorph (I := J) y
  let s : Set M := f ⁻¹' d.source
  have hs : IsOpen s := d.open_source.preimage hf.continuous
  have hdf : ContMDiffOn I 𝓘(ℝ, F) ∞ (d ∘ f) s :=
    d.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ h ↦ h)
  have himage : (d ∘ f) '' s = d.target := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact d.map_source' hx
    · intro hz
      obtain ⟨x, hx⟩ := hsurj (d.symm z)
      refine ⟨x, ?_, ?_⟩
      · change f x ∈ d.source
        rw [hx]
        exact d.map_target' hz
      · change d (f x) = z
        rw [hx]
        exact d.right_inv' hz
  have hne : (interior d.target).Nonempty := by
    rw [d.open_target.interior_eq]
    exact ⟨d y, d.map_source' (mem_extChartAt_source y)⟩
  have hdim := dimH_image_manifold_le hs hdf
  rw [himage, Real.dimH_of_nonempty_interior hne] at hdim
  exact (not_le_of_gt (Nat.cast_lt.mpr hd : (finrank ℝ E : ℝ≥0∞) < finrank ℝ F)) hdim

end NoExoticSixSphere

import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Dimension of smooth images, including manifolds with boundary and corners

Extended-chart domains are relatively open in the convex model range.
Within that convex range, smooth maps are locally Lipschitz. The usual
countable chart-cover argument therefore does not require boundaryless sources.
-/

noncomputable section

open Set Filter Module
open scoped ContDiff Manifold Topology ENNReal

namespace Wikipedia.SmoothSixDPoincare.GeneralPosition

variable {E F H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A smooth image in one extended chart has dimension at most the model dimension. -/
theorem dimH_image_chart_le {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (x : X) :
    dimH (f '' ((extChartAt I x).source ∩ s)) ≤ finrank ℝ E := by
  let c := extChartAt I x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
      inter_subset_right).contDiffOn
  have hVsub : V ⊆ range I := fun y hy => extChartAt_target_subset_range x hy.1
  have hdim : dimH ((f ∘ c.symm) '' V) ≤ dimH V := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro y hy
    have ht : c.target ∈ 𝓝[range I] y := extChartAt_target_mem_nhdsWithin_of_mem hy.1
    have hp : c.symm ⁻¹' s ∈ 𝓝[range I] y := by
      rw [← nhdsWithin_extChartAt_target_eq_of_mem hy.1]
      exact (contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) x).continuousOn y hy.1
        |>.preimage_mem_nhdsWithin
        (hs.mem_nhds hy.2)
    have hV : V ∈ 𝓝[range I] y := inter_mem ht hp
    have hd : ContDiffWithinAt ℝ 1 (f ∘ c.symm) (range I) y :=
      ((hfc y hy).of_le (by simp)).mono_of_mem_nhdsWithin hV
    obtain ⟨L, U, hU, hLip⟩ := hd.exists_lipschitzOnWith I.convex_range
    exact ⟨L, U, nhdsWithin_mono y hVsub hU, hLip⟩
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        rwa [c.left_inv hyc]
      · exact congrArg f (c.left_inv hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact hdim.trans ((dimH_mono (subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

/-- Smooth images of Lindelöf manifolds, with or without corners, obey the dimension bound. -/
theorem dimH_image_manifold_le [LindelofSpace X] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) :
    dimH (f '' s) ≤ finrank ℝ E := by
  let U : X → Set X := fun x => (extChartAt I x).source
  have hU : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_source x
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x => iSup_le (fun _ => dimH_image_chart_le hs hf x))

/-- The complement of a lower-dimensional smooth image is dense in the ambient vector space. -/
theorem dense_compl_manifold_image [LindelofSpace X] [FiniteDimensional ℝ F]
    {f : X → F} {s : Set X} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : finrank ℝ E < finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

end Wikipedia.SmoothSixDPoincare.GeneralPosition

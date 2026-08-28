import Wikipedia.NoExoticSixSphere.ModelInteriorCoordinates
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Changing a boundaryless atlas to a model with boundary

Compose each original chart with one smooth full-source model embedding.
The topology is unchanged. The identity maps between the old and new models
are smooth, so this changes the model used for charts, not the manifold's
smooth structure. The embedding may be chosen inside the model's interior.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.ChangedModelAtlas

variable {K B H M : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace K M]
  [IsManifold 𝓘(ℝ, K) ∞ M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, K) I K H ∞)

noncomputable def chartDiffeomorph (x : M) : PartialDiffeomorph 𝓘(ℝ, K) I M H ∞ :=
  (modelChartPartialDiffeomorph (I := 𝓘(ℝ, K)) x).trans Φ

noncomputable def chart (x : M) : OpenPartialHomeomorph M H :=
  (chartDiffeomorph Φ x).toOpenPartialHomeomorph

variable (hsource : Φ.source = univ)

include hsource in
theorem mem_chart_source (x : M) : x ∈ (chart Φ x).source := by
  refine ⟨mem_extChartAt_source x, ?_⟩
  change (modelChartPartialDiffeomorph (I := 𝓘(ℝ, K)) x) x ∈ Φ.source
  rw [hsource]
  trivial

@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace H M where
  atlas := range (chart Φ)
  chartAt := chart Φ
  mem_chart_source := mem_chart_source Φ hsource
  chart_mem_atlas x := ⟨x, rfl⟩

theorem isManifold : letI := chartedSpace (M := M) Φ hsource; IsManifold I ∞ M := by
  let := chartedSpace (M := M) Φ hsource
  apply isManifold_of_contDiffOn I ∞ M
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  let Ψ := (chartDiffeomorph Φ x).symm.trans (chartDiffeomorph Φ y)
  change ContDiffOn ℝ ∞ (I ∘ Ψ ∘ I.symm) (I.symm ⁻¹' Ψ.source ∩ range I)
  exact (I.contMDiff.comp_contMDiffOn
    (Ψ.contMDiffOn_toFun.comp (I.contMDiffOn_symm.mono inter_subset_right)
      (fun _ hz ↦ hz.1))).contDiffOn

theorem contMDiff_toOriginal : letI := chartedSpace (M := M) Φ hsource;
    ContMDiff I 𝓘(ℝ, K) ∞ (id : M → M) := by
  let := chartedSpace (M := M) Φ hsource
  let := isManifold (M := M) Φ hsource
  intro x
  rw [contMDiffAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, B) 𝓘(ℝ, K) ∞
    ((chartDiffeomorph Φ x).symm ∘ I.symm) (range I) (I (chartDiffeomorph Φ x x))
  have hx := (chartDiffeomorph Φ x).map_source' (mem_chart_source Φ hsource x)
  have hc := (chartDiffeomorph Φ x).contMDiffOn_invFun.contMDiffAt
    ((chartDiffeomorph Φ x).open_target.mem_nhds hx)
  exact hc.comp_contMDiffWithinAt_of_eq (I.contMDiffOn_symm _ (mem_range_self _)) (I.left_inv _)

theorem contMDiff_fromOriginal : letI := chartedSpace (M := M) Φ hsource;
    ContMDiff 𝓘(ℝ, K) I ∞ (id : M → M) := by
  let := chartedSpace (M := M) Φ hsource
  let := isManifold (M := M) Φ hsource
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨continuousAt_id, ?_⟩
  change ContMDiffAt 𝓘(ℝ, K) 𝓘(ℝ, B) ∞ (I ∘ chartDiffeomorph Φ x) x
  exact I.contMDiff.contMDiffAt.comp x
    ((chartDiffeomorph Φ x).contMDiffOn_toFun.contMDiffAt
      ((chartDiffeomorph Φ x).open_source.mem_nhds (mem_chart_source Φ hsource x)))

noncomputable def diffeomorph : letI := chartedSpace (M := M) Φ hsource;
    M ≃ₘ⟮I, 𝓘(ℝ, K)⟯ M := by
  let := chartedSpace (M := M) Φ hsource
  exact
    { toEquiv := Equiv.refl M
      contMDiff_toFun := contMDiff_toOriginal Φ hsource
      contMDiff_invFun := contMDiff_fromOriginal Φ hsource }

theorem isInteriorPoint (hinterior : ∀ y ∈ Φ.target, I y ∈ interior (range I)) (x : M) :
    letI := chartedSpace (M := M) Φ hsource;
    I.IsInteriorPoint x := by
  let := chartedSpace (M := M) Φ hsource
  change I (Φ ((modelChartPartialDiffeomorph (I := 𝓘(ℝ, K)) x) x)) ∈ interior (range I)
  apply hinterior
  apply Φ.map_source'
  rw [hsource]
  trivial

end NoExoticSixSphere.ChangedModelAtlas

import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Change a boundaryless native atlas through a full-source model chart

The topology and every underlying point remain unchanged. Both identity
maps are proved smooth with their respective native atlases. Unlike a
self-model-only atlas change, this construction also applies directly to
the native product model of the new surgery patch.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.BoundarylessModelChange

variable {E H F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E K ∞)

def chartPartial (x : M) : PartialDiffeomorph I J M K ∞ :=
  (NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x).trans Φ

def chart (x : M) : OpenPartialHomeomorph M K :=
  (chartPartial (I := I) Φ x).toOpenPartialHomeomorph

variable (hsource : Φ.source = univ)

include hsource in
theorem mem_chart_source (x : M) : x ∈ (chart (I := I) Φ x).source := by
  refine ⟨mem_extChartAt_source x, ?_⟩
  change (NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x) x ∈ Φ.source
  rw [hsource]
  trivial

@[instance_reducible]
def chartedSpace : ChartedSpace K M where
  atlas := range (chart (I := I) Φ)
  chartAt := chart (I := I) Φ
  mem_chart_source := mem_chart_source (I := I) Φ hsource
  chart_mem_atlas x := ⟨x, rfl⟩

theorem isManifold : letI := chartedSpace (I := I) (M := M) Φ hsource; IsManifold J ∞ M := by
  let _ := chartedSpace (I := I) (M := M) Φ hsource
  apply isManifold_of_contDiffOn J ∞ M
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  let Ψ := (chartPartial (I := I) Φ x).symm.trans (chartPartial (I := I) Φ y)
  change ContDiffOn ℝ ∞ (J ∘ Ψ ∘ J.symm) (J.symm ⁻¹' Ψ.source ∩ range J)
  exact (J.contMDiff.comp_contMDiffOn
    (Ψ.contMDiffOn.comp (J.contMDiffOn_symm.mono inter_subset_right)
      (fun _ hz => hz.1))).contDiffOn

theorem contMDiff_toOriginal :
    letI := chartedSpace (I := I) (M := M) Φ hsource
    ContMDiff J I ∞ (id : M → M) := by
  let _ := chartedSpace (I := I) (M := M) Φ hsource
  let _ := isManifold (I := I) (M := M) Φ hsource
  intro x
  rw [contMDiffAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, F) I ∞
    ((chartPartial (I := I) Φ x).symm ∘ J.symm) (range J) (J (chartPartial (I := I) Φ x x))
  have hx := (chartPartial (I := I) Φ x).map_source (mem_chart_source (I := I) Φ hsource x)
  have hc := (chartPartial (I := I) Φ x).contMDiffOn_invFun.contMDiffAt
    ((chartPartial (I := I) Φ x).open_target.mem_nhds hx)
  exact hc.comp_contMDiffWithinAt_of_eq (J.contMDiffOn_symm _ (mem_range_self _)) (J.left_inv _)

theorem contMDiff_fromOriginal :
    letI := chartedSpace (I := I) (M := M) Φ hsource
    ContMDiff I J ∞ (id : M → M) := by
  let _ := chartedSpace (I := I) (M := M) Φ hsource
  let _ := isManifold (I := I) (M := M) Φ hsource
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨continuousAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, F) ∞ (J ∘ chartPartial (I := I) Φ x) x
  exact J.contMDiff.contMDiffAt.comp x
    ((chartPartial (I := I) Φ x).contMDiffOn.contMDiffAt
      ((chartPartial (I := I) Φ x).open_source.mem_nhds
        (mem_chart_source (I := I) Φ hsource x)))

def diffeomorph :
    letI := chartedSpace (I := I) (M := M) Φ hsource
    Diffeomorph J I M M ∞ := by
  let _ := chartedSpace (I := I) (M := M) Φ hsource
  exact {
    toEquiv := Equiv.refl M
    contMDiff_toFun := contMDiff_toOriginal (I := I) Φ hsource
    contMDiff_invFun := contMDiff_fromOriginal (I := I) Φ hsource }

theorem diffeomorph_apply (x : M) :
    letI := chartedSpace (I := I) (M := M) Φ hsource
    diffeomorph (I := I) Φ hsource x = x := rfl

end Wikipedia.SmoothSixDPoincare.BoundarylessModelChange

import Wikipedia.NoExoticSixSphere.ManifoldAffineChartDomain
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# A constructed finite cover by genuine smooth manifold charts

Compactness selects finitely many of the original extended charts, packaged
as partial diffeomorphisms. The cover does not replace the manifold atlas.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization

theorem exists_finite_chart_cover (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M] [CompactSpace M] :
    ∃ C : Set (TargetChart n M), C.Finite ∧ ∀ x : M, ∃ c ∈ C, x ∈ c.source := by
  let chart : M → TargetChart n M := fun x ↦ modelChartPartialDiffeomorph (I := 𝓡 n) x
  have hcover : (univ : Set M) ⊆ ⋃ x : M, (chart x).source := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (chart x).source) (fun x ↦ (chart x).open_source) hcover
  refine ⟨chart '' (t : Set M), t.finite_toSet.image chart, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  exact ⟨chart y, mem_image_of_mem chart hy, hxy⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily

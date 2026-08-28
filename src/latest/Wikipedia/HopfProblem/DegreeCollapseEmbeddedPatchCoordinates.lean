import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Coordinates inside a compact embedded branch of an immersion

The original map need only be embedded on the specified source patch.
Its native coordinate restriction is embedded, and an actual open target
window identifies the full patch image with the parametrized image.
No global embedding of the original source map is asserted.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

variable {E G H N M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N] [TopologicalSpace M]
  {F : N → M} {K : Set N}

theorem isEmbedding_patch_coordinates
    (hF : IsEmbedding (fun x : K => F x))
    (c : PartialDiffeomorph 𝓘(ℝ, E) I E N ∞) (hcK : c.target ⊆ K) :
    IsEmbedding (fun x : c.source => F (c x)) := by
  have hc : IsEmbedding (fun x : c.source => c x) :=
    c.toOpenPartialHomeomorph.isEmbedding_restrict
  exact hF.comp (hc.codRestrict K (fun x => hcK (c.map_source' x.property)))

theorem exists_patch_coordinate_window
    (hF : IsEmbedding (fun x : K => F x))
    (c : PartialDiffeomorph 𝓘(ℝ, E) I E N ∞) (hcK : c.target ⊆ K) :
    ∃ A : Set M, IsOpen A ∧ MapsTo (F ∘ c) c.source A ∧
      ∀ y ∈ A, y ∈ F '' K ↔ y ∈ (F ∘ c) '' c.source := by
  have hT : IsOpen {x : K | (x : N) ∈ c.target} :=
    c.open_target.preimage continuous_subtype_val
  obtain ⟨A, hA, hpre⟩ := hF.isInducing.isOpen_iff.mp hT
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx
    have hxT : c x ∈ c.target := c.map_source' hx
    have hmem : (⟨c x, hcK hxT⟩ : K) ∈ {x : K | (x : N) ∈ c.target} := hxT
    rw [← hpre] at hmem
    exact hmem
  · intro y hy
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hmem : (⟨x, hx⟩ : K) ∈ (fun x : K => F x) ⁻¹' A := by
        change F x ∈ A
        rwa [hxy]
      rw [hpre] at hmem
      have hxT : x ∈ c.target := hmem
      exact ⟨c.invFun x, c.map_target' hxT,
        (congrArg F (c.right_inv' hxT)).trans hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨c x, hcK (c.map_source' hx), hxy⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

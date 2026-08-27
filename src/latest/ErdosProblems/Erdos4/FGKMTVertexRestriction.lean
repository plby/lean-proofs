import ErdosProblems.Erdos4.FGKMTInitialEdgeGeometry

/-! Restrict edge laws to a chosen vertex subset without changing its vertex or pair incidences. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def restrictedVertexEdge (W e : Finset V) : Finset W :=
  Finset.univ.filter (fun v : W => v.val ∈ e)

theorem mem_restrictedVertexEdge (W e : Finset V) (v : W) :
    v ∈ restrictedVertexEdge W e ↔ v.val ∈ e := by
  simp only [restrictedVertexEdge, Finset.mem_filter, Finset.mem_univ, true_and]

theorem restrictedVertexEdge_card_le (W e : Finset V) :
    (restrictedVertexEdge W e).card ≤ e.card := by
  have hsub : (restrictedVertexEdge W e).image Subtype.val ⊆ e := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_restrictedVertexEdge W e w).mp hw
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

namespace FiniteLaw

noncomputable def restrictVertices (μ : FiniteLaw (Finset V)) (W : Finset V) :
    FiniteLaw (Finset W) := μ.map (restrictedVertexEdge W)

theorem restrictVertices_vertex (μ : FiniteLaw (Finset V)) (W : Finset V) (v : W) :
    (μ.restrictVertices W).prob (fun e => v ∈ e) = μ.prob (fun e => v.val ∈ e) := by
  rw [restrictVertices, prob_map]
  exact μ.prob_congr_iff _ _ (fun e => mem_restrictedVertexEdge W e v)

theorem restrictVertices_pair (μ : FiniteLaw (Finset V)) (W : Finset V) (v w : W) :
    (μ.restrictVertices W).prob (fun e => v ∈ e ∧ w ∈ e) =
      μ.prob (fun e => v.val ∈ e ∧ w.val ∈ e) := by
  rw [restrictVertices, prob_map]
  apply μ.prob_congr_iff
  intro e
  simp only [mem_restrictedVertexEdge]

theorem restrictVertices_support (μ : FiniteLaw (Finset V)) (W : Finset V) (f : Finset W)
    (hf : 0 < (μ.restrictVertices W).weight f) :
    ∃ e, 0 < μ.weight e ∧ restrictedVertexEdge W e = f :=
  map_support μ (restrictedVertexEdge W) f hf

theorem restrictVertices_card_le (μ : FiniteLaw (Finset V)) (W : Finset V) {r : ℕ}
    (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r) (f : Finset W)
    (hf : 0 < (μ.restrictVertices W).weight f) : f.card ≤ r := by
  obtain ⟨e, he, hfe⟩ := restrictVertices_support μ W f hf
  rw [← hfe]
  exact (restrictedVertexEdge_card_le W e).trans (hsize e he)

end FiniteLaw

end Erdos4.FGKMT

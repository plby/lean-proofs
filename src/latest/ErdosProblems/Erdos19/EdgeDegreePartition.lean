import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Exact degree accounting across a subhypergraph and its complement -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem sum_edge_weight_add_sdiff (H J : SetHypergraph V) (hJH : J ⊆ H)
    (weight : Set V → ℕ) :
    (∑ e : J, weight e.1) + (∑ e : ↥(H \ J), weight e.1) = ∑ e : H, weight e.1 := by
  classical
  let left : {e : H // e.1 ∈ J} ≃ J :=
    { toFun := fun e ↦ ⟨e.1.1, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, hJH e.2⟩, e.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let right : {e : H // e.1 ∉ J} ≃ ↥(H \ J) :=
    { toFun := fun e ↦ ⟨e.1.1, e.1.2, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← left.sum_comp (fun e ↦ weight e.1), ← right.sum_comp (fun e ↦ weight e.1)]
  exact Fintype.sum_subtype_add_sum_subtype (fun e : H ↦ e.1 ∈ J) (fun e ↦ weight e.1)

theorem incident_degree_eq_sum (H : SetHypergraph V) (v : V) :
    (H.incidentEdges v).ncard = ∑ e : H, if v ∈ e.1 then 1 else 0 :=
  ncard_eq_sum_indicator (H.incidentEdges v)

theorem incident_degree_add_sdiff (H J : SetHypergraph V) (hJH : J ⊆ H) (v : V) :
    (J.incidentEdges v).ncard + ((H \ J).incidentEdges v).ncard =
      (H.incidentEdges v).ncard := by
  simp only [incident_degree_eq_sum]
  exact H.sum_edge_weight_add_sdiff J hJH (fun e ↦ if v ∈ e then 1 else 0)

#print axioms incident_degree_add_sdiff

end Erdos19.SetHypergraph

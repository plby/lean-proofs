import ErdosProblems.Erdos19.GraphPairs
import ErdosProblems.Erdos19.PairStarRemainder

/-! # Degree accounting before and after coloring outside the reservoir -/

namespace Erdos19.SetHypergraph

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def outsideReservoir (H J : SetHypergraph V) (R : _root_.SimpleGraph V) : SetHypergraph V :=
  H \ (J ∪ graphPairs R)

theorem incident_degree_reservoir_partition (H J : SetHypergraph V) (hJH : J ⊆ H)
    (R : _root_.SimpleGraph V) (v : V) :
    (J.incidentEdges v).ncard + ((H.outsideReservoir J R).incidentEdges v).ncard +
      (((H \ J).twoGraph ⊓ R).neighborSet v).ncard = (H.incidentEdges v).ncard := by
  let K := H \ J
  let P := K ∩ graphPairs R
  have hsplit := H.incident_degree_add_sdiff J hJH v
  have hsplit' := K.incident_degree_add_sdiff P Set.inter_subset_left v
  have hrest : K \ P = H.outsideReservoir J R := by
    ext e
    change ((e ∈ H ∧ e ∉ J) ∧ ¬((e ∈ H ∧ e ∉ J) ∧ e ∈ graphPairs R)) ↔
      (e ∈ H ∧ ¬(e ∈ J ∨ e ∈ graphPairs R))
    tauto
  rw [hrest] at hsplit'
  have hpair := K.graph_pair_inter_incident_degree R v
  change (P.incidentEdges v).ncard = _ at hpair
  rw [hpair] at hsplit'
  dsimp only [K, P] at hsplit'
  omega

theorem reservoir_degree_split (H J : SetHypergraph V) (R : _root_.SimpleGraph V)
    (hR : R ≤ H.twoGraph) (v : V) :
    (((H \ J).twoGraph ⊓ R).neighborSet v).ncard +
      ((J.twoGraph ⊓ R).neighborSet v).ncard = (R.neighborSet v).ncard := by
  have hrest : ((H \ J).twoGraph ⊓ R).neighborSet v = R.neighborSet v \ J.twoGraph.neighborSet v := by
    ext w
    constructor
    · rintro ⟨hH, hR⟩
      exact ⟨hR, fun hJ ↦ hH.2.2 hJ.2⟩
    · rintro ⟨hRv, hJ⟩
      have hH := hR hRv
      exact ⟨⟨hH.1, hH.2, fun heJ ↦ hJ ⟨hH.1, heJ⟩⟩, hRv⟩
  rw [hrest, neighborSet_inf]
  have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (R.neighborSet v) (J.twoGraph.neighborSet v)
  rw [Set.inter_comm] at h
  omega

theorem outsideReservoir_degree_budget (H J : SetHypergraph V) (hJH : J ⊆ H)
    (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (R : _root_.SimpleGraph V) (hR : R ≤ H.twoGraph) (v : V) (load : ℕ)
    (hload : ((J.twoGraph ⊓ R).neighborSet v).ncard ≤ load) :
    2 * (((H.outsideReservoir J R).incidentEdges v).ncard + (J.incidentEdges v).ncard +
      (R.neighborSet v).ncard) ≤ Fintype.card V - 1 + (H.twoGraph.neighborSet v).ncard + 2 * load := by
  have hsplit := H.incident_degree_reservoir_partition J hJH R v
  have hres := H.reservoir_degree_split J R hR v
  have hbudget := H.twice_incident_degree_le_card_add_pair_degree hlinear hmin v
  omega

theorem remaining_after_outsideReservoir_subset_pairs (H J : SetHypergraph V)
    (R : _root_.SimpleGraph V) : H \ (J ∪ H.outsideReservoir J R) ⊆ graphPairs R := by
  intro e he
  by_contra heR
  have heJ : e ∉ J := fun h ↦ he.2 (Or.inl h)
  exact he.2 (Or.inr ⟨he.1, fun h ↦ h.elim heJ heR⟩)

theorem remaining_after_outsideReservoir_graph (H J : SetHypergraph V)
    (R : _root_.SimpleGraph V) (hR : R ≤ H.twoGraph) :
    (H \ (J ∪ H.outsideReservoir J R)).twoGraph = R \ J.twoGraph := by
  ext x y
  constructor
  · intro h
    have hpair := H.remaining_after_outsideReservoir_subset_pairs J R h.2
    exact ⟨(graphPairs_pair_iff R x y).mp hpair,
      fun hJ ↦ h.2.2 (Or.inl hJ.2)⟩
  · rintro ⟨hRv, hJ⟩
    have hH := hR hRv
    refine ⟨hH.1, hH.2, ?_⟩
    rintro (heJ | heK)
    · exact hJ ⟨hH.1, heJ⟩
    · exact heK.2 (Or.inr ((graphPairs_pair_iff R x y).mpr hRv))

#print axioms outsideReservoir_degree_budget
#print axioms remaining_after_outsideReservoir_graph

end Erdos19.SetHypergraph

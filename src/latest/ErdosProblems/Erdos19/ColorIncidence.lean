import ErdosProblems.Erdos19.PairCompletion

/-! # Color incidence and the spare degree for parity corrections -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I]

def colorCovered (H : SetHypergraph V) (c : H.EdgeColoring I) (i : I) : Set V :=
  {v | ∃ e : H, c.color e = i ∧ v ∈ e.1}

def vertexSupport (H : SetHypergraph V) : Set V := {v | ∃ e : H, v ∈ e.1}

theorem colorCovered_count (H : SetHypergraph V) (c : H.EdgeColoring I) (v : V) :
    (∑ i : I, if v ∈ H.colorCovered c i then 1 else 0) = (H.incidentEdges v).ncard := by
  classical
  let f : H.incidentEdges v → {i : I // v ∈ H.colorCovered c i} :=
    fun e ↦ ⟨c.color e.1, e.1, rfl, e.2⟩
  have hf : Function.Injective f := by
    intro e g heq
    apply Subtype.ext
    by_contra hne
    have hcolor : c.color e.1 = c.color g.1 := congrArg Subtype.val heq
    exact c.valid hne ⟨v, e.2, g.2⟩ hcolor
  have hs : Function.Surjective f := by
    rintro ⟨i, e, hei, hv⟩
    exact ⟨⟨e, hv⟩, Subtype.ext hei⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)
  calc
    (∑ i : I, if v ∈ H.colorCovered c i then 1 else 0) =
        Fintype.card {i : I // v ∈ H.colorCovered c i} := by simp [Fintype.card_subtype]
    _ = Fintype.card (H.incidentEdges v) := hcard.symm
    _ = (H.incidentEdges v).ncard := Set.fintypeCard_eq_ncard _

def largePart (H : SetHypergraph V) : SetHypergraph V := {e | e ∈ H ∧ 3 ≤ e.ncard}

theorem largePart_incident_ncard (H : SetHypergraph V) (v : V) :
    (H.largePart.incidentEdges v).ncard = H.largeDegree v := by
  let e : H.largePart.incidentEdges v ≃ {e : H.incidentEdges v // 3 ≤ e.1.1.ncard} :=
    { toFun := fun e ↦ ⟨⟨⟨e.1.1, e.1.2.1⟩, e.2⟩, e.1.2.2⟩
      invFun := fun e ↦ ⟨⟨e.1.1.1, e.1.1.2, e.2⟩, e.1.2⟩
      left_inv := fun e ↦ rfl
      right_inv := fun e ↦ rfl }
  have hcard := Fintype.card_congr e
  simpa only [largeDegree, Set.fintypeCard_eq_ncard] using hcard

theorem largePart_support_degree_pos (H : SetHypergraph V) {v : V}
    (hv : v ∈ H.largePart.vertexSupport) : 0 < H.largeDegree v := by
  obtain ⟨e, he⟩ := hv
  rw [← H.largePart_incident_ncard v]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨e, he⟩

theorem large_coloring_parity_degree_budget (H : SetHypergraph V)
    (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (c : H.largePart.EdgeColoring I) (v : V) :
    (H.twoGraph.neighborSet v).ncard +
      (∑ i : I, if v ∈ H.largePart.colorCovered c i then 1 else 0) +
      (if v ∈ H.largePart.vertexSupport then 1 else 0) ≤ Fintype.card V - 1 := by
  rw [colorCovered_count, H.largePart_incident_ncard]
  have hsplit := H.twoGraph_degree_add_largeDegree hsize v
  have hbudget := H.incident_degree_add_excess hlinear hcomplete hsize v
  have hexcess := H.largeDegree_le_incidentExcess v
  by_cases hv : v ∈ H.largePart.vertexSupport
  · rw [if_pos hv]
    have hpos := H.largePart_support_degree_pos hv
    omega
  · rw [if_neg hv]
    omega

#print axioms colorCovered_count
#print axioms large_coloring_parity_degree_budget

end Erdos19.SetHypergraph

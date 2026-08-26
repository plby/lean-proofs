import ErdosProblems.Erdos73.Menger
import ErdosProblems.Erdos73.PackingCopy

/-! The order-two Menger consequences of connectivity after one vertex deletion. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem two_paths_of_delete_preconnected
    (hconn : ∀ X : Finset V, X.card < 2 → (G.induce (X : Set V)ᶜ).Preconnected)
    (A B : Finset V) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    HasDisjointSTPaths G A B 2 := by
  rcases Menger.finite_vertex_menger_sharp G A B 2 with hp | ⟨X, hX, hsep⟩
  · exact hp
  · have ha : ∃ a ∈ A, a ∉ X := by
      by_contra hn
      push Not at hn
      have hh := card_le_card (show A ⊆ X from hn)
      omega
    have hb : ∃ b ∈ B, b ∉ X := by
      by_contra hn
      push Not at hn
      have hh := card_le_card (show B ⊆ X from hn)
      omega
    obtain ⟨a, haA, haX⟩ := ha
    obtain ⟨b, hbB, hbX⟩ := hb
    let a' : ↥((X : Set V)ᶜ) := ⟨a, haX⟩
    let b' : ↥((X : Set V)ᶜ) := ⟨b, hbX⟩
    obtain ⟨w⟩ := hconn X hX a' b'
    let P : GraphPath (G.induce (X : Set V)ᶜ) := ⟨a', b', w.toPath, w.toPath.property⟩
    let Q := P.mapCopy (Embedding.induce (X : Set V)ᶜ).toCopy
    obtain ⟨v, hv, hvX⟩ := hsep Q (Or.inl ⟨haA, hbB⟩)
    obtain ⟨z, _, rfl⟩ := (P.mem_mapCopy_vertexSet _ v).mp hv
    exact (z.property hvX).elim

theorem two_clean_tails_of_pair_packing (a b : V) (hab : a ≠ b) (T : Finset V)
    (hp : HasDisjointSTPaths G {a, b} T 2) :
    ∃ P Q : GraphPath G, P.EndpointClean {a, b} T ∧ Q.EndpointClean {a, b} T ∧
      P.source = a ∧ Q.source = b ∧ Disjoint P.vertexSet Q.vertexSet := by
  obtain ⟨R, hR⟩ := hp
  let C := R.toEndpointClean
  have hcard : ({a, b} : Finset V).card ≤ C.sourceSet.card := by
    rw [C.sourceSet_card]
    change ({a, b} : Finset V).card ≤ R.card
    simpa only [card_pair hab] using hR
  have heq : C.sourceSet = {a, b} := eq_of_subset_of_card_le C.sourceSet_subset_left hcard
  obtain ⟨i, hi⟩ := C.exists_index_source_eq_of_mem_sourceSet (heq ▸ (by simp : a ∈ ({a, b} : Finset V)))
  obtain ⟨j, hj⟩ := C.exists_index_source_eq_of_mem_sourceSet (heq ▸ (by simp : b ∈ ({a, b} : Finset V)))
  have hij : i ≠ j := by
    intro hij
    exact hab (hi.symm.trans ((congrArg (fun t => (C.path t).source) hij).trans hj))
  exact ⟨C.path i, C.path j, C.endpoint_clean i, C.endpoint_clean j, hi, hj, C.node_disjoint hij⟩

end
end Erdos73

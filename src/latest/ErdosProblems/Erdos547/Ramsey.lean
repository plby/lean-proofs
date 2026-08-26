import ErdosProblems.Erdos547.Embedding

/-!
# Ramsey notation and exact counting for Erdős problem 547

A red/blue colouring is represented by a simple graph and its complement.
Containment is ordinary subgraph containment. The ultimate statement quantifies
over all sufficiently large tree orders; it does not assert the false order-one
instance.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*}

/-- The ordinary two-colour Ramsey property at a specified host order. -/
def RamseyAt (T : SimpleGraph U) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), T ⊑ G ∨ T ⊑ Gᶜ

/-- Restricting a colouring proves monotonicity in the host order. -/
theorem RamseyAt.mono {T : SimpleGraph U} {N M : ℕ}
    (hNM : N ≤ M) (hT : RamseyAt T N) : RamseyAt T M := by
  let e : Fin N ↪ Fin M := ⟨Fin.castLE hNM, Fin.castLE_injective hNM⟩
  intro G
  have hcompl : (G.comap e)ᶜ = Gᶜ.comap e := by
    ext x y
    simp [e.injective.eq_iff]
  rcases hT (G.comap e) with hr | hb
  · exact Or.inl (hr.trans (SimpleGraph.Embedding.comap e G).isContained)
  · rw [hcompl] at hb
    exact Or.inr (hb.trans (SimpleGraph.Embedding.comap e Gᶜ).isContained)

/-- A Ramsey property is independent of the chosen finite host vertex type. -/
theorem RamseyAt.of_card [Fintype V] {T : SimpleGraph U} {N : ℕ}
    (hT : RamseyAt T N) (hV : Fintype.card V = N) (G : SimpleGraph V) :
    T ⊑ G ∨ T ⊑ Gᶜ := by
  let e : Fin N ↪ V := (Fintype.equivFinOfCardEq hV).symm.toEmbedding
  have hcompl : (G.comap e)ᶜ = Gᶜ.comap e := by
    ext x y
    simp [e.injective.eq_iff]
  rcases hT (G.comap e) with hr | hb
  · exact Or.inl (hr.trans (SimpleGraph.Embedding.comap e G).isContained)
  · rw [hcompl] at hb
    exact Or.inr (hb.trans (SimpleGraph.Embedding.comap e Gᶜ).isContained)

/-- The literal order-one bound would require a vertex in the empty host. -/
theorem not_ramseyAt_one_zero : ¬ RamseyAt (⊥ : SimpleGraph (Fin 1)) 0 := by
  intro h
  rcases h (⊥ : SimpleGraph (Fin 0)) with hr | hb
  · obtain ⟨f⟩ := hr
    exact (f 0).elim0
  · obtain ⟨f⟩ := hb
    exact (f 0).elim0

/-- The obstruction above uses a genuine one-vertex tree. -/
theorem singleton_isTree : (⊥ : SimpleGraph (Fin 1)).IsTree :=
  SimpleGraph.IsTree.of_subsingleton

/-- The two colour degrees partition the other vertices exactly. -/
theorem degree_add_compl [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] (v : V) :
    G.degree v + Gᶜ.degree v = Fintype.card V - 1 := by
  rw [G.degree_compl]
  have hlt := G.degree_lt_card_verts v
  omega

/-- At order `2*m`, exactly one colour has degree at least `m` at each vertex. -/
theorem high_degree_partition {m : ℕ} (G : SimpleGraph (Fin (2 * m)))
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] (v : Fin (2 * m)) :
    m ≤ G.degree v ↔ ¬ m ≤ Gᶜ.degree v := by
  have hsum := degree_add_compl G v
  simp only [Fintype.card_fin] at hsum
  have hpos : 0 < m := by have := v.isLt; omega
  omega

/-- Red and blue edge counts sum to the complete-graph edge count. -/
theorem edge_count_add_compl [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  calc
    G.edgeFinset.card + Gᶜ.edgeFinset.card =
        (G.edgeFinset ∪ Gᶜ.edgeFinset).card := by
      exact (Finset.card_union_of_disjoint
        (SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right)).symm
    _ = (G ⊔ Gᶜ).edgeFinset.card := by rw [SimpleGraph.edgeFinset_sup]
    _ = (Fintype.card V).choose 2 := by
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        sup_compl_eq_top]
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V))

/-- One colour has at least half of the available edges, without rounding loss. -/
theorem majority_edge_count [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    (Fintype.card V).choose 2 ≤ 2 * G.edgeFinset.card ∨
      (Fintype.card V).choose 2 ≤ 2 * Gᶜ.edgeFinset.card := by
  have hsum := edge_count_add_compl G
  omega

end Erdos547

#print axioms Erdos547.high_degree_partition
#print axioms Erdos547.majority_edge_count

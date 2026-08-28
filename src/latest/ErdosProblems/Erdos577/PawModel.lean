import ErdosProblems.Erdos577.UnattachedModel

/-! Finite paw--quadrilateral graphs, retaining the actual old diagonal mask. -/

namespace Erdos577.PawModel

open Finset

def graph (diagonal : Fin 4) (m : ℕ) : SimpleGraph (Fin 8) :=
  Unattached.graph diagonal m ⊔ SimpleGraph.edge 0 1

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (graph diagonal m).Adj := fun a b ↦
  decidable_of_iff
    ((Unattached.graph diagonal m).Adj a b ∨ ((a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) ∧ a ≠ b))
    (by rw [graph, SimpleGraph.sup_adj, SimpleGraph.edge_adj])

lemma graph_mono (diagonal : Fin 4) {small large : ℕ} (h : large &&& small = small) :
    graph diagonal small ≤ graph diagonal large :=
  sup_le_sup (Unattached.graph_mono diagonal h) le_rfl

lemma factor_mono {diagonal : Fin 4} {small large : ℕ}
    (hs : LocalFactor (graph diagonal small) univ) (h : large &&& small = small) :
    LocalFactor (graph diagonal large) univ := by
  let f := SimpleGraph.Copy.ofLE (graph diagonal small) (graph diagonal large)
    (graph_mono diagonal h)
  simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

lemma graph_zero_le (diagonal : Fin 4) (m : ℕ) : graph 0 m ≤ graph diagonal m := by
  have hb : Unattached.basePairs 0 ⊆ Unattached.basePairs diagonal := by
    fin_cases diagonal <;> decide +kernel
  have hr {a b : Fin 8} (h : Unattached.relation 0 m a b) :
      Unattached.relation diagonal m a b := by
    rcases h with h | h
    · exact Or.inl (hb h)
    · exact Or.inr h
  apply sup_le_sup _ le_rfl
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

end Erdos577.PawModel

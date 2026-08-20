import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

-- [TABLET NODE: ConnectedGraphVertexIncidentDart]
lemma ConnectedGraphVertexIncidentDart {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] :
    G.Connected → 0 < G.edgeFinset.card →
      ∀ v : V, ∃ d : G.Dart, d.toProd.2 = v := by
-- BODY
  intro hconn hedge v
  have hEdgeNonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp hedge
  rcases hEdgeNonempty with ⟨e, he⟩
  have heSet : e ∈ G.edgeSet := by
    simpa using (SimpleGraph.mem_edgeFinset.mp he)
  have hAdjPair : ∃ a b : V, G.Adj a b := by
    revert heSet
    refine Sym2.ind ?_ e
    intro a b habSet
    exact ⟨a, b, (SimpleGraph.mem_edgeSet G).mp habSet⟩
  rcases hAdjPair with ⟨a, b, hab⟩
  by_cases hv : v = a
  · subst a
    exact ⟨⟨(b, v), hab.symm⟩, rfl⟩
  · have hreach : G.Reachable v a := hconn v a
    rcases hreach.nonempty_neighborSet_left hv with ⟨w, hw⟩
    exact ⟨⟨(w, v), hw.symm⟩, rfl⟩

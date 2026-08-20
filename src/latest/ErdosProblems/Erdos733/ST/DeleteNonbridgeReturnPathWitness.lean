import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: DeleteNonbridgeReturnPathWitness]
lemma DeleteNonbridgeReturnPathWitness {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (e : G.edgeFinset)
    (he : ¬ G.IsBridge e.1) :
    ∃ d : G.Dart, d.edge = e.1 ∧
      ∃ p : (G.deleteEdges {s(d.snd, d.fst)}).Walk d.snd d.fst, p.IsPath := by
-- BODY
  classical
  rcases e with ⟨edge, hedge⟩
  revert hedge he
  refine Sym2.inductionOn edge ?_
  intro u v huv_mem he
  have huv_edgeSet : s(u, v) ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp huv_mem
  have huv : G.Adj u v := (SimpleGraph.mem_edgeSet (G := G)).mp huv_edgeSet
  let d : G.Dart := ⟨(u, v), huv⟩
  refine ⟨d, by simp [d, SimpleGraph.Dart.edge], ?_⟩
  have hreachUV : (G.deleteEdges {s(u, v)}).Reachable u v := by
    simpa [SimpleGraph.isBridge_iff] using he
  have hreach : (G.deleteEdges {s(v, u)}).Reachable v u := by
    simpa [Sym2.eq_swap, SimpleGraph.reachable_comm] using hreachUV
  rcases hreach.exists_isPath with ⟨p, hp⟩
  exact ⟨p, hp⟩

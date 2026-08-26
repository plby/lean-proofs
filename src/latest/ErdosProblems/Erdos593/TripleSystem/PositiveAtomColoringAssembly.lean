import ErdosProblems.Erdos593.TripleSystem.HighPairAtomBridge
import ErdosProblems.Erdos593.TripleSystem.HighPairEdgeColoring
import ErdosProblems.Erdos593.TripleSystem.LowCodegreeLayering
import ErdosProblems.Erdos593.TripleSystem.LowCrossingColoring
import ErdosProblems.Erdos593.TripleSystem.LowEdgeRankClassification
import ErdosProblems.Erdos593.TripleSystem.SameRankColoring

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of the positive-atom colouring argument

At the quadratic Hall threshold, the host edges split into three families:
those containing a high pair, those contained in one low-codegree closure
rank fibre, and the remaining low edges, which contain an edge of the low
crossing graph.  Each family has a countable colouring, and the standard
natural-number pairing operation combines the three colourings.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Every edge of a host with a low-pair closure layering is either a
high-pair edge, an edge internal to one rank fibre, or contains an edge of
the corresponding low crossing graph. -/
theorem highPairEdge_or_sameRankEdge_or_lowCrossingEdge
    {W : Type u} {D : Type u} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {e : D}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I) :
    H.highPairEdge t e \/ sameRankEdge H L.rank e \/
      H.EdgeContainsGraphEdge (lowCrossingGraph H L.rank t) e := by
  rcases H.highPairEdge_or_lowPairEdge t e with hhigh | hlow
  · exact Or.inl hhigh
  · obtain ⟨x, y, z, hxy, hxz, hyz, hedge, hshape⟩ :=
      exists_lowPair_rank_shape_or_lowCrossingAdj L hlow
    rcases hshape with hall | hadj | hadj | hadj
    · refine Or.inr (Or.inl ⟨L.rank x, ?_⟩)
      intro w hw
      change w ∈ H.edgeSet e at hw
      rw [hedge] at hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · rfl
      · exact hall.1.symm
      · exact (hall.1.trans hall.2).symm
    · refine Or.inr (Or.inr ⟨x, y, ?_, ?_, hadj⟩)
      · change x ∈ H.edgeSet e
        rw [hedge]
        simp
      · change y ∈ H.edgeSet e
        rw [hedge]
        simp
    · refine Or.inr (Or.inr ⟨x, z, ?_, ?_, hadj⟩)
      · change x ∈ H.edgeSet e
        rw [hedge]
        simp
      · change z ∈ H.edgeSet e
        rw [hedge]
        simp
    · refine Or.inr (Or.inr ⟨y, z, ?_, ?_, hadj⟩)
      · change y ∈ H.edgeSet e
        rw [hedge]
        simp
      · change z ∈ H.edgeSet e
        rw [hedge]
        simp

/-- The three countable colourings furnished by the high-pair, same-rank,
and low-crossing arguments combine to a countable proper colouring of the
whole host. -/
theorem exists_natProperColoring_of_atomFree_of_lowPairClosureLayering
    {W : Type u} {D : Type u} {I : Type u}
    [DecidableEq W] [LinearOrder I]
    {H : TripleSystem W D} {n : Nat}
    (hn : 0 < n)
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H)
    (L : FiniteClosureLayering 2
      (lowPairClosureFinset H (2 * n + n * n)) I)
    (hlocal : H.LocallyCountablyChromaticBelow) :
    ∃ c : W → Nat, H.IsProperColoring c := by
  have ht : 0 < 2 * n + n * n := by
    omega
  have hhigh : H.CountablyColorableOn (H.highPairEdge (2 * n + n * n)) :=
    H.countablyColorableOn_highPairEdge
      (countablyColorable_highPairGraph_of_atomFree hn hatomFree)
  have hsame : H.CountablyColorableOn (sameRankEdge H L.rank) :=
    countablyColorableOn_sameRankEdge_of_finiteClosureLayering H L hlocal
  have hcrossGraph : Erdos593.SimpleGraph.CountablyColorable
      (lowCrossingGraph H L.rank (2 * n + n * n)) :=
    countablyColorable_lowCrossingGraph_of_atomFree
      (rank := L.rank) hn ht hatomFree
  have hcross : H.CountablyColorableOn
      (H.EdgeContainsGraphEdge (lowCrossingGraph H L.rank (2 * n + n * n))) :=
    H.countablyColorableOn_edgeContainsGraphEdge hcrossGraph
  have hrest : H.CountablyColorableOn
      (fun e => sameRankEdge H L.rank e \/
        H.EdgeContainsGraphEdge (lowCrossingGraph H L.rank (2 * n + n * n)) e) :=
    CountablyColorableOn.union H hsame hcross
  have hparts : H.CountablyColorableOn
      (fun e => H.highPairEdge (2 * n + n * n) e \/
        sameRankEdge H L.rank e \/
          H.EdgeContainsGraphEdge
            (lowCrossingGraph H L.rank (2 * n + n * n)) e) :=
    CountablyColorableOn.union H hhigh hrest
  rcases hparts with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro e
  exact hc e (highPairEdge_or_sameRankEdge_or_lowCrossingEdge L)

end TripleSystem

end Erdos593

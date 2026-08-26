import ErdosProblems.Erdos593.Graph.MinimalBadCore
import ErdosProblems.Erdos593.Graph.RainbowPositiveSize
import ErdosProblems.Erdos593.TripleSystem.LowCrossingAtomBridge

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Countable colouring of the low crossing graph

For a positive expansion size and positive codegree threshold, the rainbow
extraction supplies a positive finite balanced biclique size.  Atom-freeness
then rules out a copy of that biclique in the low crossing graph, so the
finite forbidden-biclique graph theorem gives a colouring by natural numbers.

The host edge type is deliberately in the vertex universe: this is the
universe restriction of the public `Appears` interface for the expansion atom.
-/

namespace Erdos593

universe u w

namespace TripleSystem

open _root_.SimpleGraph

/-- An atom-free host has a countable proper colouring of its low crossing
graph.  The finite forbidden biclique size is chosen by the positive-size
rainbow extraction theorem, which is exactly what makes the graph-colouring
theorem applicable. -/
theorem countablyColorable_lowCrossingGraph_of_atomFree
    {W : Type u} {D : Type u} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W -> I} {n t : Nat}
    (hn : 0 < n) (ht : 0 < t)
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H) :
    Erdos593.SimpleGraph.CountablyColorable (lowCrossingGraph H rank t) := by
  obtain ⟨q, hqpos, hqrainbow⟩ :=
    RainbowBipartite.exists_pos_rainbow_bipartite_submatrix n t hn ht
  apply Erdos593.SimpleGraph.countablyColorable_of_no_completeBipartiteNNCopy
    (lowCrossingGraph H rank t) hqpos
  exact isEmpty_completeBipartiteNNCopy_lowCrossingGraph_of_atomFree
    (n := n) ht hqrainbow hatomFree

end TripleSystem

end Erdos593

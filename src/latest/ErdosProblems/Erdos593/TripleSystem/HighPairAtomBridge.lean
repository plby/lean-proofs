import ErdosProblems.Erdos593.Graph.MinimalBadCore
import ErdosProblems.Erdos593.TripleSystem.HighPairMatrix
import ErdosProblems.Erdos593.TripleSystem.ObligatoryAtoms
import Mathlib.Combinatorics.SimpleGraph.Copy

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The high-pair graph / positive-atom bridge

A complete bipartite copy in the high-pair graph is a finite grid of
large-codegree pairs.  At the quadratic Hall threshold, the third vertices of
that grid can be selected globally injectively, so the grid directly embeds
the corresponding private-vertex-expansion atom.  Consequently, a host
avoiding that atom has a countably colorable high-pair graph.
-/

namespace Erdos593

universe u v

namespace TripleSystem

open _root_.SimpleGraph

/-- A non-induced `K_{n,n}` copy in a high-pair graph supplies its two
injected sides as a complete grid of high pairs. -/
theorem highPairGrid_of_completeBipartiteNNCopy
    {W : Type u} {D : Type v} {H : TripleSystem W D} {n t : Nat}
    (f : Copy (completeBipartiteNN.{u} n) (highPairGraph H t)) :
    ∃ left right : Fin n ↪ W,
      (∀ i j, left i ≠ right j) ∧
        ∀ i j, HighPair H t (left i) (right j) := by
  let left : Fin n ↪ W :=
    { toFun := fun i => f (Sum.inl (ULift.up i))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using! h }
  let right : Fin n ↪ W :=
    { toFun := fun j => f (Sum.inr (ULift.up j))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using! h }
  refine ⟨left, right, ?_, ?_⟩
  · intro i j h
    have hsrc : (completeBipartiteNN.{u} n).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [completeBipartiteNN]
    have htgt : (highPairGraph H t).Adj (left i) (right j) := by
      simpa [left, right] using! f.toHom.map_adj hsrc
    exact (highPairGraph_adj H t (left i) (right j)).mp htgt |>.1 h
  · intro i j
    have hsrc : (completeBipartiteNN.{u} n).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [completeBipartiteNN]
    have htgt : (highPairGraph H t).Adj (left i) (right j) := by
      simpa [left, right] using! f.toHom.map_adj hsrc
    exact (highPairGraph_adj H t (left i) (right j)).mp htgt

/-- One complete quadratic high-pair grid has a globally rainbow apex map,
and therefore embeds the matching positive balanced expansion atom. -/
theorem nonempty_completeBipartiteExpansionEmbedding_of_quadratic_highPair
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hhigh : ∀ i j,
      HighPair H (2 * n + n * n) (left i) (right j)) :
    Nonempty ((completeBipartiteExpansionAtom.{u} n).Embedding H) := by
  obtain ⟨M, _, _, hapex_inj⟩ :=
    exists_injectiveWitnessedBipartiteMatrix_of_quadratic_highPair
      left right hhigh
  let row : Fin n ↪ Fin n := Function.Embedding.refl _
  let column : Fin n ↪ Fin n := Function.Embedding.refl _
  have hrainbow : RainbowBipartite.IsRainbow M.apex row column := by
    intro ij kl h
    apply hapex_inj
    simpa [row, column] using! h
  exact ⟨M.rainbowEmbedding row column hrainbow⟩

/-- Avoiding the positive `K_{n,n}` expansion rules out a non-induced
`K_{n,n}` copy in the high-pair graph at the quadratic Hall threshold. -/
theorem isEmpty_completeBipartiteNNCopy_highPairGraph_of_atomFree
    {W : Type u} {D : Type u} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H) :
    IsEmpty (Copy (completeBipartiteNN.{u} n)
      (highPairGraph H (2 * n + n * n))) := by
  refine ⟨?_⟩
  intro f
  obtain ⟨left, right, _, hhigh⟩ :=
    highPairGrid_of_completeBipartiteNNCopy f
  exact hatomFree ⟨
    (nonempty_completeBipartiteExpansionEmbedding_of_quadratic_highPair
      left right hhigh).some⟩

/-- In an atom-free host, the corresponding quadratic high-pair graph is
countably colorable.  This combines the finite Hall bridge above with the
singular-cardinal-safe graph coloring theorem. -/
theorem countablyColorable_highPairGraph_of_atomFree
    {W : Type u} {D : Type u} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat} (hn : 0 < n)
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H) :
    Erdos593.SimpleGraph.CountablyColorable
      (highPairGraph H (2 * n + n * n)) :=
  Erdos593.SimpleGraph.countablyColorable_of_no_completeBipartiteNNCopy
    (highPairGraph H (2 * n + n * n)) hn
    (isEmpty_completeBipartiteNNCopy_highPairGraph_of_atomFree hatomFree)

end TripleSystem

end Erdos593

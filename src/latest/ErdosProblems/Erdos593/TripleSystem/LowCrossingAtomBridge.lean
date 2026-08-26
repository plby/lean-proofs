import ErdosProblems.Erdos593.Graph.CompleteBipartiteCopy
import ErdosProblems.Erdos593.TripleSystem.HighPairEdgeColoring
import ErdosProblems.Erdos593.TripleSystem.ObligatoryAtoms
import ErdosProblems.Erdos593.TripleSystem.RainbowLocalBound
import Mathlib.Combinatorics.SimpleGraph.Copy

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The low-codegree crossing graph / positive-atom bridge

For a rank map on the vertices, the low crossing graph joins two vertices on
the same rank when they have a common lower-ranked completion whose host edge
contains no high pair at the selected threshold.  A complete bipartite copy
in this graph gives a finite grid of low edges.  The lower-rank condition
keeps all selected completion vertices away from both core sides, while the
low-edge condition supplies the local rainbow bound.
-/

namespace Erdos593

universe u v w

namespace TripleSystem

open _root_.SimpleGraph

/-- The same-rank, lower-completion graph for the low-pair part of a triple
system.  An adjacency records its completion witness and the fact that its
host edge contains no threshold-`t` high pair. -/
def lowCrossingGraph {W : Type u} {D : Type v} {I : Type w}
    [LinearOrder I] (H : TripleSystem W D) (rank : W → I) (t : Nat) :
    _root_.SimpleGraph W where
  Adj x y :=
    ∃ z : W, rank z < rank x ∧ rank x = rank y ∧
      ∃ p : ThirdVertexWitness H x y z, H.lowPairEdge t p.edge
  symm := ⟨by
    rintro x y ⟨z, hzx, hxy, p, hlow⟩
    refine ⟨z, ?_, hxy.symm, p.swap, hlow⟩
    simpa [hxy] using! hzx⟩
  loopless := ⟨by
    intro x hx
    rcases hx with ⟨z, _, _, p, _⟩
    exact p.left_ne_right rfl⟩

@[simp]
theorem lowCrossingGraph_adj {W : Type u} {D : Type v} {I : Type w}
    [LinearOrder I] (H : TripleSystem W D) (rank : W → I) (t : Nat)
    (x y : W) :
    (lowCrossingGraph H rank t).Adj x y ↔
      ∃ z : W, rank z < rank x ∧ rank x = rank y ∧
        ∃ p : ThirdVertexWitness H x y z, H.lowPairEdge t p.edge :=
  Iff.rfl

/-- A `K_{q,q}` copy in the low crossing graph embeds the positive balanced
expansion whenever `q` has the finite rainbow-extraction property for the
threshold `t`.  The rank inequality is used only to prove that every chosen
apex is disjoint from the two core sides. -/
theorem nonempty_completeBipartiteExpansionEmbedding_of_lowCrossingCopy
    {W : Type u} {D : Type v} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n q t : Nat}
    (ht : 0 < t)
    (hq : ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      RainbowBipartite.LocallyBounded t color →
        ∃ row column : Fin n ↪ Fin q,
          RainbowBipartite.IsRainbow color row column)
    (f : Copy (completeBipartiteNN.{u} q) (lowCrossingGraph H rank t)) :
    Nonempty ((completeBipartiteExpansionAtom.{u} n).Embedding H) := by
  classical
  obtain ⟨left, right, hcore, hadj⟩ :=
    Erdos593.SimpleGraph.exists_finEmbeddings_of_completeBipartiteNNCopy
      (lowCrossingGraph H rank t) f
  have hdata : ∀ i j : Fin q,
      ∃ z : W, rank z < rank (left i) ∧ rank (left i) = rank (right j) ∧
        ∃ p : ThirdVertexWitness H (left i) (right j) z,
          H.lowPairEdge t p.edge := by
    intro i j
    exact (lowCrossingGraph_adj H rank t (left i) (right j)).mp (hadj i j)
  let apex : Fin q → Fin q → W :=
    fun i j => Classical.choose (hdata i j)
  have hapex_lt : ∀ i j, rank (apex i j) < rank (left i) := by
    intro i j
    simpa [apex] using! (Classical.choose_spec (hdata i j)).1
  have hsame : ∀ i j, rank (left i) = rank (right j) := by
    intro i j
    simpa [apex] using! (Classical.choose_spec (hdata i j)).2.1
  let cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j) :=
    fun i j => Classical.choose ((Classical.choose_spec (hdata i j)).2.2)
  have hlow : ∀ i j, H.lowPairEdge t (cell i j).edge := by
    intro i j
    exact Classical.choose_spec ((Classical.choose_spec (hdata i j)).2.2)
  have hleft_inc : ∀ i j, H.Inc (left i) (cell i j).edge := by
    intro i j
    change left i ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hright_inc : ∀ i j, H.Inc (right j) (cell i j).edge := by
    intro i j
    change right j ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hapex_inc : ∀ i j, H.Inc (apex i j) (cell i j).edge := by
    intro i j
    change apex i j ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hnot_high_left : ∀ i j, ¬ HighPair H t (left i) (apex i j) := by
    intro i j
    exact H.not_highPair_of_lowPairEdge (hlow i j)
      (hleft_inc i j) (hapex_inc i j)
  have hnot_high_right : ∀ i j, ¬ HighPair H t (right j) (apex i j) := by
    intro i j
    exact H.not_highPair_of_lowPairEdge (hlow i j)
      (hright_inc i j) (hapex_inc i j)
  have hapex_ne_left : ∀ i j k, apex i j ≠ left k := by
    intro i j k h
    have hrank : rank (left k) = rank (left i) :=
      (hsame k j).trans (hsame i j).symm
    have hlt := hapex_lt i j
    rw [h, hrank] at hlt
    exact (lt_irrefl _ hlt)
  have hapex_ne_right : ∀ i j k, apex i j ≠ right k := by
    intro i j k h
    have hrank : rank (right k) = rank (left i) :=
      (hsame i k).symm
    have hlt := hapex_lt i j
    rw [h, hrank] at hlt
    exact (lt_irrefl _ hlt)
  let M : WitnessedBipartiteMatrix H q t :=
    WitnessedBipartiteMatrix.ofThirdVertexWitnesses left right apex cell hcore
      hapex_ne_left hapex_ne_right
      (locallyBounded_of_not_highPair_on_cells ht left right apex cell
        hnot_high_left hnot_high_right)
  obtain ⟨row, column, hrainbow⟩ := hq W M.apex M.locallyBounded
  exact ⟨M.rainbowEmbedding row column hrainbow⟩

/-- If every finite balanced complete bipartite graph occurs in the low
crossing graph, the corresponding positive balanced expansion atom occurs in
the host. -/
theorem nonempty_completeBipartiteExpansionEmbedding_of_lowCrossingCopies
    {W : Type u} {D : Type v} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n t : Nat}
    (hn : 0 < n) (ht : 0 < t)
    (hcopy : ∀ q : Nat,
      Nonempty (Copy (completeBipartiteNN.{u} q) (lowCrossingGraph H rank t))) :
    Nonempty ((completeBipartiteExpansionAtom.{u} n).Embedding H) := by
  obtain ⟨q, hq⟩ :=
    RainbowBipartite.exists_rainbow_bipartite_submatrix n t hn ht
  obtain ⟨f⟩ := hcopy q
  exact nonempty_completeBipartiteExpansionEmbedding_of_lowCrossingCopy
    ht hq f

/-- At any size carrying the finite rainbow-extraction property, an atom-free
host has no complete bipartite copy in its low crossing graph. -/
theorem isEmpty_completeBipartiteNNCopy_lowCrossingGraph_of_atomFree
    {W : Type u} {D : Type u} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n q t : Nat}
    (ht : 0 < t)
    (hq : ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      RainbowBipartite.LocallyBounded t color →
        ∃ row column : Fin n ↪ Fin q,
          RainbowBipartite.IsRainbow color row column)
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H) :
    IsEmpty (Copy (completeBipartiteNN.{u} q) (lowCrossingGraph H rank t)) := by
  refine ⟨?_⟩
  intro f
  exact hatomFree ⟨
    (nonempty_completeBipartiteExpansionEmbedding_of_lowCrossingCopy
      (n := n) ht hq f).some⟩

/-- The rainbow lemma supplies a finite complete-bipartite size excluded from
the low crossing graph of every atom-free host. -/
theorem exists_isEmpty_completeBipartiteNNCopy_lowCrossingGraph_of_atomFree
    {W : Type u} {D : Type u} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n t : Nat}
    (hn : 0 < n) (ht : 0 < t)
    (hatomFree : ¬ (completeBipartiteExpansionAtom.{u} n).Appears H) :
    ∃ q : Nat,
      IsEmpty (Copy (completeBipartiteNN.{u} q) (lowCrossingGraph H rank t)) := by
  obtain ⟨q, hq⟩ :=
    RainbowBipartite.exists_rainbow_bipartite_submatrix n t hn ht
  exact ⟨q,
    isEmpty_completeBipartiteNNCopy_lowCrossingGraph_of_atomFree
      (n := n) ht hq hatomFree⟩

end TripleSystem

end Erdos593

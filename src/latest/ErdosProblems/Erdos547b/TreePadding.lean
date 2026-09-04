import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.TreePadding

open SimpleGraph

universe u v

/-- Mapping an acyclic graph along a type embedding merely adds isolated
vertices, so it remains acyclic. -/
theorem isAcyclic_map {α : Type u} {β : Type v} {G : SimpleGraph α}
    (hG : G.IsAcyclic) (f : α ↪ β) : (G.map f).IsAcyclic := by
  let e : G ↪g G.map f := SimpleGraph.Embedding.map f G
  have hind : ((G.map f).induce (Set.range f)).IsAcyclic :=
    e.isoInduceRange.isAcyclic_iff.mp hG
  intro x c hc
  have hs : ∀ y ∈ c.support, y ∈ Set.range f := by
    intro y hy
    have hy' : y ∈ (G.map f).support :=
      mem_support_of_mem_walk_support c hc.not_nil hy
    rw [support_map] at hy'
    exact hy'.imp fun z hz => hz.2
  let c' := c.induce (Set.range f) hs
  apply hind c'
  apply SimpleGraph.Walk.IsCycle.of_map
  rw [show c'.map (SimpleGraph.Embedding.induce (G := G.map f) (Set.range f)).toHom = c from by
    exact SimpleGraph.Walk.map_induce (s := Set.range f) c hs]
  exact hc

/-- Every finite tree with at most `n + 1` vertices is contained in a tree
whose vertex type is exactly `Fin (n + 1)`.

The proof embeds the given tree into the complete graph on `n + 1` vertices
and extends that acyclic subgraph to a spanning tree. -/
theorem exists_fin_tree_extension {α : Type u} [Fintype α]
    (T : SimpleGraph α) (n : ℕ) (hcard : Fintype.card α ≤ n + 1)
    (hT : T.IsTree) :
    ∃ T' : SimpleGraph (Fin (n + 1)), T'.IsTree ∧ T ⊑ T' := by
  let f : α ↪ Fin (n + 1) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (α := α) (β := Fin (n + 1)) (by simpa using hcard))
  let H : SimpleGraph (Fin (n + 1)) := T.map f
  have hHacyclic : H.IsAcyclic := isAcyclic_map hT.isAcyclic f
  have hHle : H ≤ (completeGraph (Fin (n + 1))) := le_top
  obtain ⟨T', hHT', -, hT'tree⟩ :=
    (connected_top : (completeGraph (Fin (n + 1))).Connected).exists_isTree_le_of_le_of_isAcyclic
      hHle hHacyclic
  refine ⟨T', hT'tree, ?_⟩
  exact SimpleGraph.IsContained.trans
    (⟨(SimpleGraph.Embedding.map f T).toCopy⟩ : T ⊑ H)
    (SimpleGraph.IsContained.of_le hHT')

/-- Transitive padding corollary: a host containing every tree of order
exactly `n + 1` also contains every tree of order at most `n + 1`. -/
theorem isContained_of_forall_fin_tree {α : Type u} {β : Type v}
    [Fintype α] (T : SimpleGraph α) (G : SimpleGraph β) (n : ℕ)
    (hcard : Fintype.card α ≤ n + 1) (hT : T.IsTree)
    (hlarge : ∀ T' : SimpleGraph (Fin (n + 1)), T'.IsTree → T' ⊑ G) :
    T ⊑ G := by
  obtain ⟨T', hT'tree, hTT'⟩ := exists_fin_tree_extension T n hcard hT
  exact SimpleGraph.IsContained.trans hTT' (hlarge T' hT'tree)

/-- Edge-count form of the padding lemma.  For a finite tree, at most `n`
edges is equivalent to at most `n + 1` vertices. -/
theorem isContained_of_forall_fin_tree_of_edgeSet_card_le
    {α : Type u} {β : Type v} [Fintype α]
    (T : SimpleGraph α) (G : SimpleGraph β) (n : ℕ)
    (hedges : Nat.card T.edgeSet ≤ n) (hT : T.IsTree)
    (hlarge : ∀ T' : SimpleGraph (Fin (n + 1)), T'.IsTree → T' ⊑ G) :
    T ⊑ G := by
  classical
  let : Fintype T.edgeSet := Fintype.ofFinite T.edgeSet
  have hcardEq : Nat.card T.edgeSet + 1 = Fintype.card α := by
    rw [Nat.card_eq_fintype_card, ← T.edgeFinset_card]
    exact hT.card_edgeFinset
  apply isContained_of_forall_fin_tree T G n _ hT hlarge
  omega

#print axioms isAcyclic_map
#print axioms exists_fin_tree_extension
#print axioms isContained_of_forall_fin_tree
#print axioms isContained_of_forall_fin_tree_of_edgeSet_card_le

end Erdos547b.TreePadding

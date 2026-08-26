import Mathlib
import ErdosProblems.Erdos550.TauFineIndexedBounds
import ErdosProblems.Erdos550.ReducedGraphTreeEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooting the indexed τ-fine components

Each deleted component is itself a finite tree.  This file proves that fact and
applies the project's rooted-edge-structure theorem componentwise.  It therefore
supplies the parent/rank data required by the routed forest embedding engine,
while retaining the canonical inclusion of every component vertex into the
original tree.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma seedDeleted_le (T : SimpleGraph α) (S : Finset α) :
    seedDeleted T S ≤ T := by
  intro v w hvw;
  grind +suggestions

omit [Fintype α] [DecidableEq α] in
lemma seedDeleted_isAcyclic
    (T : SimpleGraph α) (hT : T.IsTree) (S : Finset α) :
    (seedDeleted T S).IsAcyclic := by
  convert! hT.2.anti ( seedDeleted_le T S ) using 1

omit [Fintype α] [DecidableEq α] in
lemma seedDeleted_component_isTree
    (T : SimpleGraph α) (hT : T.IsTree) (S : Finset α)
    (c : (seedDeleted T S).ConnectedComponent) :
    c.toSimpleGraph.IsTree := by
  convert! seedDeleted_isAcyclic T hT S |> fun h => h.isTree_connectedComponent c

lemma nonseedComponent_isTree
    (T : SimpleGraph α) (hT : T.IsTree) (S : Finset α)
    (c : NonseedComponent T S) :
    c.1.toSimpleGraph.IsTree := by
  convert! seedDeleted_component_isTree T hT S c.1

lemma component_toSimpleGraph_adj_original
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) {v w : c.1.supp} :
    c.1.toSimpleGraph.Adj v w → T.Adj v.1 w.1 := by
  intro h;
  convert! seedDeleted_le T S _;
  convert! h

/-
Every indexed shrub component admits parent/rank data whose links are
actual original-tree edges and which classify every component edge.
-/
theorem exists_nonseedComponent_rooted_structure
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (S : Finset α) (c : NonseedComponent T S) :
    ∃ (parent : c.1.supp → Option c.1.supp) (rank : c.1.supp → ℕ),
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a.1 b.1) ∧
      (∀ a b, c.1.toSimpleGraph.Adj a b →
        parent a = some b ∨ parent b = some a) := by
  obtain ⟨ parent, rank, hparent, hrank ⟩ := IsTree.exists_rooted_edge_structure c.1.toSimpleGraph ( nonseedComponent_isTree T hT S c );
  refine' ⟨ parent, rank, hparent, _, hrank.2 ⟩;
  exact fun a b hab => component_toSimpleGraph_adj_original T S c ( hrank.1 a b hab )

/-
Componentwise proper two-colouring, compatible with the rooted structure.
-/
theorem exists_nonseedComponent_rooted_two_colouring
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (S : Finset α) (c : NonseedComponent T S) :
    ∃ (parent : c.1.supp → Option c.1.supp)
      (rank : c.1.supp → ℕ) (col : c.1.supp → Bool),
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a.1 b.1) ∧
      (∀ a b, c.1.toSimpleGraph.Adj a b →
        parent a = some b ∨ parent b = some a) ∧
      (∀ a b, parent a = some b → col a ≠ col b) := by
  have := IsTree.exists_rooted_edge_structure (c.1.toSimpleGraph) (nonseedComponent_isTree T hT S c);
  obtain ⟨ parent, rank, h₁, h₂, h₃ ⟩ := this; use parent, rank; simp_all +decide [ SimpleGraph.adj_comm ] ;
  refine' ⟨ _, _ ⟩;
  · intro a ha b hb hab; specialize h₂ a ha b hb hab; exact (by
    convert! component_toSimpleGraph_adj_original T S c h₂ using 1);
  · have h_colorable : ∃ (color : c.1.supp → Bool), ∀ a b, c.1.toSimpleGraph.Adj a b → color a ≠ color b := by
      have h_colorable : (c.1.toSimpleGraph).Colorable 2 := by
        convert! IsTree.colorable_two ( c.1.toSimpleGraph ) ( nonseedComponent_isTree T hT S c ) using 1;
      obtain ⟨ color, hcolor ⟩ := h_colorable;
      exact ⟨ fun x => color x = 1, fun a b hab => by have := hcolor hab; have := Fin.exists_fin_two.mp ⟨ color a, rfl ⟩ ; have := Fin.exists_fin_two.mp ⟨ color b, rfl ⟩ ; aesop ⟩;
    exact ⟨ h_colorable.choose, fun a ha b hb hab => h_colorable.choose_spec _ _ ( h₂ _ _ _ _ hab ) ⟩

end Erdos550

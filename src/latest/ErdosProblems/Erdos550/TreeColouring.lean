import Mathlib
import ErdosProblems.Erdos550.ReducedGraphTreeEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Proper two-colouring of a tree (bipartition)

A finite tree is bipartite: it admits a proper `Bool`-colouring `col` with
`col a ≠ col b` for every edge `a–b`.  This supplies the `col`/`hcol` data
consumed by the stateful matching embedding (there the colour is only
required to flip along `parent` links, which are a subset of the tree edges).

The colour is the parity of the distance from a fixed root: in a tree adjacent
vertices are at distances differing by exactly one, so the parity flips along
every edge.
-/

open SimpleGraph Finset

namespace Erdos550

/-
In a tree, the distance from a fixed root to two adjacent vertices differs by
exactly one.
-/
lemma IsTree.dist_root_adj_succ {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hT : T.IsTree) (r a b : α) (hab : T.Adj a b) :
    T.dist r a = T.dist r b + 1 ∨ T.dist r b = T.dist r a + 1 := by
  cases' hT with h₁ h₂;
  obtain ⟨ p, hp ⟩ := h₁ r a;
  · simp +decide [ SimpleGraph.dist_self, hab ];
  · have h_dist : T.dist r a ≤ T.dist r b + 1 ∧ T.dist r b ≤ T.dist r a + 1 := by
      grind +suggestions;
    have h_dist_ne : T.dist a r ≠ T.dist b r := by
      apply tree_adj_dist_ne T (by
      constructor <;> assumption) hab;
    simp_all +decide [ SimpleGraph.dist_comm ];
    omega

/-
**A finite tree admits a proper two-colouring.**  There is `col : α → Bool`
with `col a ≠ col b` for every edge `a–b`.
-/
lemma IsTree.exists_two_colouring {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hT : T.IsTree) :
    ∃ col : α → Bool, ∀ a b, T.Adj a b → col a ≠ col b := by
  obtain ⟨r, hr⟩ : ∃ r : α, True := by
    cases isEmpty_or_nonempty α <;> simp_all +decide only [IsEmpty.exists_iff];
    exact hT.1.nonempty.elim ( fun x => ‹IsEmpty α›.elim x );
  use fun v => decide (Odd (T.dist r v));
  intro a b hab;
  cases' Erdos550.IsTree.dist_root_adj_succ T hT r a b hab with h h <;> simp_all +decide; all_goals grind

/-- Rooted-structure form: a proper two-colouring flipping along every `parent`
link produced by `IsTree.exists_rooted_edge_structure`. -/
lemma IsTree.exists_rooted_two_colouring {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (parent : α → Option α)
    (hpar_edge : ∀ a b, parent a = some b → T.Adj a b) :
    ∃ col : α → Bool, ∀ a b, parent a = some b → col a ≠ col b := by
  obtain ⟨col, hcol⟩ := IsTree.exists_two_colouring T hT
  exact ⟨col, fun a b hab => hcol a b (hpar_edge a b hab)⟩

end Erdos550

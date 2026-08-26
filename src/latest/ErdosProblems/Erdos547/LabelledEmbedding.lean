import ErdosProblems.Erdos547.BipartiteEmbedding

/-!
# Greedy tree embeddings into disjoint labelled pools

The capacity needed at a boundary edge is the size of the target label class,
not the total order of the tree.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V I : Type*} [Fintype U]

open scoped Classical in
theorem exists_copy_of_labelled_degree
    (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (label : U → I) (pool : I → Finset V)
    (hdis : ∀ i j, i ≠ j → Disjoint (pool i) (pool j))
    (hdegree : ∀ u v, T.Adj u v → ∀ z ∈ pool (label u),
      ((Finset.univ : Finset U).filter fun x ↦ label x = label v).card ≤
        degreeIn G (pool (label v)) z)
    (r : U) (z : V) (hz : z ∈ pool (label r)) :
    ∃ f : T.Copy G, f r = z ∧ ∀ u, f u ∈ pool (label u) := by
  classical
  let S : Finset U := {r}
  have hrx (x : (S : Set U)) : x.val = r := by simpa [S] using x.property
  let e : (T.induce (S : Set U)).Copy G := {
    toHom := {
      toFun := fun _ ↦ z
      map_rel' := fun {x y} h ↦ by
        have hxy : T.Adj x.val y.val := h
        have h' : T.Adj r r := by simpa only [hrx x, hrx y] using hxy
        exact (T.loopless.irrefl r h').elim }
    injective' := fun x y _ ↦ Subtype.ext ((hrx x).trans (hrx y).symm) }
  have hS : (T.induce (S : Set U)).Connected := by
    let : Nonempty ({r} : Set U) := ⟨⟨r, rfl⟩⟩
    have hco : (S : Set U) = {r} := by ext x; simp [S]
    rw [hco]
    exact SimpleGraph.IsTree.of_subsingleton.connected
  have he : ∀ x : (S : Set U), e x ∈ pool (label x.val) := by
    intro x
    change z ∈ pool (label x.val)
    rw [hrx x]
    exact hz
  obtain ⟨f, hfe, hf⟩ := extend_connected_copy hT S hS e
    (fun x w ↦ w ∈ pool (label x)) he (by
      intro Q hSQ hconn f hfe hf _ p v hv hpv
      let Y := (Finset.univ : Finset U).filter fun x ↦ label x = label v
      let B := pool (label v)
      let used : Finset V := Finset.univ.image f
      have hpre : ∀ x : (Q : Set U), f x ∈ B → x.val ∈ Y := by
        intro x hxB
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra h
        exact Finset.disjoint_left.mp (hdis (label x.val) (label v) h) (hf x) hxB
      have hvY : v ∈ Y := by simp [Y]
      have hcount := used_part_card_lt Q Y B f f.injective hpre v hvY hv
      have hcount' : (used ∩ B).card < degreeIn G B (f p) :=
        hcount.trans_le (hdegree p.val v hpv (f p) (hf p))
      obtain ⟨w, hwB, hw, hwu⟩ := exists_unused_neighbor_into G B used (f p) hcount'
      refine ⟨w, hw, ?_, hwB⟩
      intro x hx
      exact hwu (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩))
  exact ⟨f, hfe ⟨r, by simp [S]⟩, hf⟩

end Erdos547

#print axioms Erdos547.exists_copy_of_labelled_degree

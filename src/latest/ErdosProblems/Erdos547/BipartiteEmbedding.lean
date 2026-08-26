import ErdosProblems.Erdos547.PartialEmbedding
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Greedy tree embedding with a prescribed bipartition
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*}

open scoped Classical in
/-- If the preimages of used vertices in `B` lie in `Y`, a still unused
vertex of `Y` leaves the used part of `B` strictly smaller than `Y`. -/
theorem used_part_card_lt (S Y : Finset U) (B : Finset V)
    (f : ↑(S : Set U) → V) (hinj : Function.Injective f)
    (hpre : ∀ x : (S : Set U), f x ∈ B → x.val ∈ Y)
    (v : U) (hvY : v ∈ Y) (hvS : v ∉ S) :
    ((Finset.univ.image f) ∩ B).card < Y.card := by
  classical
  let P := (Finset.univ : Finset (S : Set U)).filter fun x ↦ f x ∈ B
  have himage : (Finset.univ.image f) ∩ B = P.image f := by
    ext w
    simp only [P, Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, hx⟩, hw⟩
      exact ⟨x, hx.symm ▸ hw, hx⟩
    · rintro ⟨x, hxB, hx⟩
      exact ⟨⟨x, hx⟩, hx ▸ hxB⟩
  have hsub : P.image (fun x : (S : Set U) ↦ x.val) ⊆ Y.erase v := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    have hxB : f x ∈ B := (Finset.mem_filter.mp hx).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, hxy ▸ hpre x hxB⟩
    intro hy
    exact hvS (hy ▸ hxy ▸ x.property)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.coe_injective] at hcard
  have herase := Finset.card_erase_add_one hvY
  rw [himage, Finset.card_image_of_injective _ hinj]
  omega

open scoped Classical in
/-- Strictly more neighbours in a set than used vertices in that set ensures
an unused neighbour, whether or not the parent lies in the set. -/
theorem exists_unused_neighbor_into (G : SimpleGraph V) [DecidableRel G.Adj]
    (B used : Finset V) (z : V) (hcount : (used ∩ B).card < degreeIn G B z) :
    ∃ w ∈ B, G.Adj z w ∧ w ∉ used := by
  classical
  have hnot : ¬ B.filter (G.Adj z) ⊆ used ∩ B := by
    intro h
    have hcard := Finset.card_le_card h
    change degreeIn G B z ≤ (used ∩ B).card at hcard
    omega
  obtain ⟨w, hw, hwu⟩ := Finset.not_subset.mp hnot
  obtain ⟨hwB, hzw⟩ := Finset.mem_filter.mp hw
  exact ⟨w, hwB, hzw, fun h ↦ hwu (Finset.mem_inter.mpr ⟨h, hwB⟩)⟩

open scoped Classical in
/-- A bipartite host whose cross degrees dominate the sizes of the opposite
tree classes contains the tree with the prescribed class assignment. -/
theorem isContained_of_bipartite_cross_degree [Finite U]
    (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (X Y : Finset U)
    (hpart : T.IsBipartiteWith (X : Set U) (Y : Set U)) (hX : X.Nonempty)
    (A B : Finset V) (hdis : Disjoint A B) (hA : A.Nonempty)
    (hdegA : ∀ a ∈ A, Y.card ≤ degreeIn G B a)
    (hdegB : ∀ b ∈ B, X.card ≤ degreeIn G A b) : T ⊑ G := by
  classical
  let := Fintype.ofFinite U
  obtain ⟨r, hr⟩ := hX
  obtain ⟨z, hz⟩ := hA
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
  let allowed := fun x w ↦ (x ∈ X ∧ w ∈ A) ∨ (x ∈ Y ∧ w ∈ B)
  have he : ∀ x : (S : Set U), allowed x.val (e x) := by
    intro x
    exact Or.inl ⟨(hrx x).symm ▸ hr, hz⟩
  obtain ⟨f, _, _⟩ := extend_connected_copy hT S hS e allowed he (by
    intro Q hSQ hconn f hfe hf _ p v hv hpv
    let used : Finset V := Finset.univ.image f
    rcases hf p with ⟨hpX, hpA⟩ | ⟨hpY, hpB⟩
    · have hvY : v ∈ Y := hpart.mem_of_mem_adj hpX hpv
      have hpre : ∀ x : (Q : Set U), f x ∈ B → x.val ∈ Y := by
        intro x hxB
        rcases hf x with ⟨_, hxA⟩ | ⟨hxY, _⟩
        · exact (Finset.disjoint_left.mp hdis hxA hxB).elim
        · exact hxY
      have hcount := used_part_card_lt Q Y B f f.injective hpre v hvY hv
      have hcount' : (used ∩ B).card < degreeIn G B (f p) :=
        hcount.trans_le (hdegA (f p) hpA)
      obtain ⟨w, hwB, hw, hwu⟩ := exists_unused_neighbor_into G B used (f p) hcount'
      refine ⟨w, hw, ?_, Or.inr ⟨hvY, hwB⟩⟩
      intro x hx
      exact hwu (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
    · have hvX : v ∈ X := hpart.symm.mem_of_mem_adj hpY hpv
      have hpre : ∀ x : (Q : Set U), f x ∈ A → x.val ∈ X := by
        intro x hxA
        rcases hf x with ⟨hxX, _⟩ | ⟨_, hxB⟩
        · exact hxX
        · exact (Finset.disjoint_left.mp hdis hxA hxB).elim
      have hcount := used_part_card_lt Q X A f f.injective hpre v hvX hv
      have hcount' : (used ∩ A).card < degreeIn G A (f p) :=
        hcount.trans_le (hdegB (f p) hpB)
      obtain ⟨w, hwA, hw, hwu⟩ := exists_unused_neighbor_into G A used (f p) hcount'
      refine ⟨w, hw, ?_, Or.inl ⟨hvX, hwA⟩⟩
      intro x hx
      exact hwu (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩))
  exact ⟨f⟩

end Erdos547

#print axioms Erdos547.isContained_of_bipartite_cross_degree

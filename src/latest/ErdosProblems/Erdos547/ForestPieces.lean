import ErdosProblems.Erdos547.BoundedPiece

/-!
# Bounded pendant pieces in forests

The tree lemma applies inside a connected component.  The resulting piece
remains closed away from its root in the whole forest.
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

theorem connected_subset_of_meets_rooted_piece {S B : Set U} {r : U}
    (hS : IsRootedPiece T S r) (hB : (T.induce B).Preconnected)
    (hr : r ∉ B) (hmeet : (B ∩ S).Nonempty) : B ⊆ S := by
  obtain ⟨a, haB, haS⟩ := hmeet
  intro b hb
  obtain ⟨p⟩ := hB ⟨a, haB⟩ ⟨b, hb⟩
  apply mem_of_walk_of_closed (T.induce B) {u | u.val ∈ S} _ p haS
  intro u hu v huv
  exact hS.closed_off_root u.val hu (fun he ↦ hr (he ▸ u.property)) v.val huv

open scoped Classical in
theorem exists_bounded_forest_piece [Fintype U] (hT : T.IsAcyclic) (q : ℕ)
    (hq : 1 ≤ q) (B : Finset U) (hB : (T.induce (B : Set U)).Connected)
    (hsize : q ≤ B.card) :
    ∃ S : Finset U, ∃ r, q ≤ S.card ∧ S.card ≤ 2 * q - 1 ∧
      IsRootedPiece T (S : Set U) r := by
  classical
  obtain ⟨b⟩ := hB.nonempty
  let C := T.connectedComponentMk b.val
  have hBC (u : (B : Set U)) : u.val ∈ C.supp := by
    apply ConnectedComponent.sound
    exact (hB u b).map (SimpleGraph.Embedding.induce (B : Set U)).toHom
  let f : ↥(B : Set U) → C := fun u ↦ ⟨u.val, hBC u⟩
  have hfinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : C ↦ z.val) h)
  have hcard : B.card ≤ Fintype.card C := by
    simpa using Fintype.card_le_of_injective f hfinj
  have htree : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph, hT.induce C.supp⟩
  obtain ⟨P, r, hlow, hhigh, hP⟩ := exists_bounded_rooted_piece C.toSimpleGraph
    htree q hq (hsize.trans hcard)
  let S : Finset U := P.image Subtype.val
  have hScard : S.card = P.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hrS : r.val ∈ S := Finset.mem_image.mpr ⟨r, hP.root_mem, rfl⟩
  have hconn : (T.induce (S : Set U)).Connected := by
    let g : (C.toSimpleGraph.induce (P : Set C)) →g (T.induce (S : Set U)) := {
      toFun := fun u ↦ ⟨u.val.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
      map_rel' := fun h ↦ h }
    have hsurj : Function.Surjective g := by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp hu
      exact ⟨⟨v, hv⟩, Subtype.ext hval⟩
    exact hP.connected.map g hsurj
  refine ⟨S, r.val, hScard ▸ hlow, hScard ▸ hhigh, hrS, hconn, ?_⟩
  intro u hu hur v huv
  obtain ⟨u', huP, hval⟩ := Finset.mem_image.mp hu
  have huC : u ∈ C.supp := hval ▸ u'.property
  have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp huC huv
  have hu'r : u' ≠ r := by intro h; exact hur (hval.symm.trans (congrArg Subtype.val h))
  have hvP : (⟨v, hvC⟩ : C) ∈ P :=
    hP.closed_off_root u' huP hu'r ⟨v, hvC⟩ (by change T.Adj u'.val v; rwa [hval])
  exact Finset.mem_image.mpr ⟨⟨v, hvC⟩, hvP, rfl⟩

end Erdos547

#print axioms Erdos547.exists_bounded_forest_piece

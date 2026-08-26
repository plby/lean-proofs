import ErdosProblems.Erdos556.InducedDeletion
import ErdosProblems.Erdos556.DeletionOddCycles

/-!
# Isomorphisms and vertex-deletion properties

Deletion budgets are invariant under relabelling. This allows nested induced
cores to be replaced by their images in the original graph.
-/

namespace Erdos556

open SimpleGraph Finset

noncomputable def isoInduceCompl {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (S : Finset V) :
    G.induce (S : Set V)ᶜ ≃g H.induce (S.map e.toEquiv.toEmbedding : Set W)ᶜ where
  toEquiv :=
    { toFun := fun x => ⟨e x.val, by
        intro hx
        obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
        exact x.property (e.injective hyx ▸ hy)⟩
      invFun := fun y => ⟨e.symm y.val, by
        intro hy
        exact y.property (mem_map.mpr ⟨e.symm y.val, hy, e.apply_symm_apply y.val⟩)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  map_rel_iff' := by intro x y; exact e.map_adj_iff

theorem ConnectedAfterDeleting.iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {b : ℕ}
    (hG : ConnectedAfterDeleting G b) (e : G ≃g H) : ConnectedAfterDeleting H b := by
  intro S hS
  have h := hG (S.map e.symm.toEquiv.toEmbedding) (by simpa only [card_map] using hS)
  exact (isoInduceCompl e.symm S).preconnected_iff.mpr h

theorem NonbipartiteAfterDeleting.iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {b : ℕ}
    (hG : NonbipartiteAfterDeleting G b) (e : G ≃g H) : NonbipartiteAfterDeleting H b := by
  intro S hS hc
  apply hG (S.map e.symm.toEquiv.toEmbedding) (by simpa only [card_map] using hS)
  exact hc.of_hom (isoInduceCompl e.symm S).symm.toHom

#print axioms ConnectedAfterDeleting.iso
#print axioms NonbipartiteAfterDeleting.iso

end Erdos556

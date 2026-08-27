import Arxiv.Arxiv2411_18291.DisjointFamilyPermutation

/-!
# Gluing prescribed bijections on disjoint pieces

The union of a finite disjoint family is equivalent to its indexed pieces.
Consequently prescribed bijections on the individual pieces glue to an
embedding of the whole union. In frame applications the base bijection is
prescribed, while the private-piece bijections may be chosen freely.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [DecidableEq W] [DecidableEq V]

omit [DecidableEq V] in
def disjointUnionEquiv (S : I → Finset W)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) : (Σ i, S i) ≃ univ.biUnion S :=
  Equiv.ofBijective (fun x => ⟨x.2.val, mem_biUnion.mpr ⟨x.1, mem_univ _, x.2.property⟩⟩) (by
    constructor
    · intro x y hxy
      exact disjoint_family_val_injective S hS (congrArg Subtype.val hxy)
    · rintro ⟨x, hx⟩
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
      exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩)

def disjointUnionCongr (S : I → Finset W) (T : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hT : Pairwise fun i j => Disjoint (T i) (T j)) (e : ∀ i, S i ≃ T i) :
    (univ.biUnion S) ≃ (univ.biUnion T) :=
  (disjointUnionEquiv S hS).symm.trans
    ((Equiv.sigmaCongrRight e).trans (disjointUnionEquiv T hT))

theorem disjointUnionCongr_on_piece (S : I → Finset W) (T : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hT : Pairwise fun i j => Disjoint (T i) (T j)) (e : ∀ i, S i ≃ T i)
    (i : I) (x : S i) :
    (disjointUnionCongr S T hS hT e
      ⟨x.val, mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩⟩).val = (e i x).val := by
  have hx : (disjointUnionEquiv S hS) ⟨i, x⟩ =
      ⟨x.val, mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩⟩ := rfl
  rw [← hx]
  simp only [disjointUnionCongr, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

omit [DecidableEq V] in
theorem exists_embedding_of_disjoint_pieces (S : I → Finset W) (T : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hT : Pairwise fun i j => Disjoint (T i) (T j)) (e : ∀ i, S i ≃ T i) :
    ∃ f : (univ.biUnion S) ↪ V, ∀ i (x : S i),
      f ⟨x.val, mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩⟩ = (e i x).val := by
  classical
  let f := (disjointUnionCongr S T hS hT e).toEmbedding.trans
    (Function.Embedding.subtype (· ∈ univ.biUnion T))
  exact ⟨f, disjointUnionCongr_on_piece S T hS hT e⟩

end Arxiv2411_18291

import Arxiv.Arxiv2411_18291.ExchangeFrameStructure
import Arxiv.Arxiv2411_18291.FrameEmbeddings
import Arxiv.Arxiv2411_18291.CliqueRootInputs

/-!
# Indexing the actual near frame by a fixed finite type

The enumeration transports the near-frame geometry to `Fin (choose q r)`.
Its root images are determined by the base map, so every root coordinate of
a near clique lies in the corresponding prescribed image edge.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q r} {A : Finset (Block W q)}

omit [DecidableEq V] in
def IsExchangeFamily.nearEnumeration (hA : IsExchangeFamily S A) (hr : 0 < r) :
    Fin (q.choose r) ≃ S.nearCliques :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hA.near_card hr])).symm

omit [DecidableEq V] in
def IsExchangeFamily.nearPattern (hA : IsExchangeFamily S A) (hr : 0 < r) :
    Fin (q.choose r) → Block W q := fun i => (hA.nearEnumeration hr i).val

omit [DecidableEq V] in
theorem IsExchangeFamily.nearPattern_private_pairwise (hA : IsExchangeFamily S A) (hr : 0 < r) :
    Pairwise fun i j => Disjoint ((hA.nearPattern hr i).val \ S.base.val)
      ((hA.nearPattern hr j).val \ S.base.val) := by
  intro i j hij
  exact hA.private_pairwise hr (hA.nearEnumeration hr i).property
    (hA.nearEnumeration hr j).property
      (fun he => hij ((hA.nearEnumeration hr).injective (Subtype.ext he)))

omit [DecidableEq V] in
theorem IsExchangeFamily.nearPattern_private_card (hA : IsExchangeFamily S A) (hr : 0 < r)
    (i : Fin (q.choose r)) : ((hA.nearPattern hr i).val \ S.base.val).card = q - r :=
  hA.private_card hr (hA.nearEnumeration hr i).property

omit [DecidableEq V] in
theorem IsExchangeFamily.nearPattern_frameDomain (hA : IsExchangeFamily S A) (hr : 0 < r) :
    frameDomain S.base.val (hA.nearPattern hr) = S.frameVertices := by
  have hu : univ.biUnion (fun i => (hA.nearPattern hr i).val) =
      S.nearCliques.biUnion Subtype.val := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨_, (hA.nearEnumeration hr i).property, hi⟩
    · rintro ⟨P, hP, hx⟩
      refine ⟨(hA.nearEnumeration hr).symm ⟨P, hP⟩, ?_⟩
      simpa only [nearPattern, Equiv.apply_symm_apply] using hx
  exact congrArg (fun U => S.base.val ∪ U) hu

def IsExchangeFamily.nearRootImage (hA : IsExchangeFamily S A) (hr : 0 < r)
    (φ : S.base.val ↪ V) (i : Fin (q.choose r)) : Block V r :=
  rootImage φ (hA.nearRoot hr (hA.nearEnumeration hr i))
    ((mem_cliqueEdges _ _).mp (hA.nearRoot_mem hr (hA.nearEnumeration hr i)))

omit [DecidableEq V] in
theorem IsExchangeFamily.nearRootImage_subset (hA : IsExchangeFamily S A) (hr : 0 < r)
    (φ : S.base.val ↪ V) (i : Fin (q.choose r)) :
    (hA.nearRootImage hr φ i).val ⊆ usedVertices φ := rootImage_subset_usedVertices _ _ _

omit [DecidableEq V] in
theorem IsExchangeFamily.nearRootImage_contains (hA : IsExchangeFamily S A) (hr : 0 < r)
    (φ : S.base.val ↪ V) (i : Fin (q.choose r)) (x : S.base.val)
    (hx : x.val ∈ (hA.nearPattern hr i).val) : φ x ∈ (hA.nearRootImage hr φ i).val := by
  apply mem_map.mpr
  refine ⟨x, ?_, rfl⟩
  apply mem_subtype.mpr
  exact mem_inter.mpr ⟨hx, x.property⟩

end Arxiv2411_18291

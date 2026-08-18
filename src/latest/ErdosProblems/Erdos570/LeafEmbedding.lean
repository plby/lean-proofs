/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.LeafExtension
import ErdosProblems.Erdos570.EndpointGrowth

/-!
# Re-embedding a target with many deleted leaves

The retained core is placed in a clique `K`.  If `K` lies in a larger set
`U` and all edges from `K` to the unused part of `U` are present, then enough
room in `U` permits all deleted leaves to be attached injectively.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Embed a graph by putting its non-leaves into `K` and its selected leaves
into fresh vertices of `U`. -/
theorem isContained_of_leaf_core_clique_cross
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1)
    (C : SimpleGraph W) (U K : Finset W)
    (hKU : K ⊆ U)
    (hK : C.IsClique (K : Set W))
    (hcross : ∀ x ∈ K, ∀ y ∈ U, x ≠ y → C.Adj x y)
    (hUcard : H.vertexCount ≤ U.card)
    (hKcard : H.vertexCount - L.card ≤ K.card) :
    H.graph ⊑ C := by
  classical
  let core := H.graph.induce
    ((Finset.univ \ L : Finset (Fin H.vertexCount)) : Set _)
  have hKinduce : (C.induce (K : Set W)).IsClique
      ((Finset.univ : Finset K) : Set K) := by
    intro x _ y _ hxy
    exact hK x.2 y.2 (fun h ↦ hxy (Subtype.ext h))
  have hcoreCard : Fintype.card (LeafCoreType H L) =
      H.vertexCount - L.card := by
    simp [LeafCoreType]
  have hcoreSetCard : Fintype.card
      ↥((Finset.univ \ L : Finset (Fin H.vertexCount)) :
        Set (Fin H.vertexCount)) = H.vertexCount - L.card := by
    let e : ↥((Finset.univ \ L : Finset (Fin H.vertexCount)) :
        Set (Fin H.vertexCount)) ≃ LeafCoreType H L :=
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := fun x ↦ by rfl
        right_inv := fun x ↦ by rfl }
    rw [Fintype.card_congr e, hcoreCard]
  have hcoreInK : core ⊑ C.induce (K : Set W) := by
    apply isContained_of_isClique_card
      (U := (Finset.univ : Finset K)) hKinduce
    rw [hcoreSetCard]
    simpa using hKcard
  obtain ⟨copyK⟩ := hcoreInK
  let copy : SimpleGraph.Copy core C :=
    (SimpleGraph.Embedding.induce (G := C) (K : Set W)).toCopy.comp copyK
  let coreRange : Finset W := Finset.univ.image copy
  have hcoreRangeCard : coreRange.card = H.vertexCount - L.card := by
    dsimp only [coreRange]
    have hi : Set.InjOn (fun d : LeafCoreType H L ↦ copy d)
        (Finset.univ : Finset (LeafCoreType H L)) :=
      fun ⦃x⦄ _ ⦃y⦄ _ hxy ↦ copy.injective hxy
    rw [Finset.card_image_of_injOn hi]
    simpa using hcoreCard
  have hcoreRangeK : coreRange ⊆ K := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, _, rfl⟩ := hx
    exact (copyK d).2
  have hcoreRangeU : coreRange ⊆ U := hcoreRangeK.trans hKU
  let available : Finset W := U \ coreRange
  have havailableCard : L.card ≤ available.card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hcoreRangeU
    have hLcard : L.card ≤ H.vertexCount := by
      simpa using Finset.card_le_card (Finset.subset_univ L)
    rw [hcoreRangeCard] at hcard
    dsimp only [available]
    omega
  obtain ⟨R, hRavailable, hRcard⟩ :=
    Finset.exists_subset_card_eq havailableCard
  let e : LeafType H L ≃ R :=
    Fintype.equivOfCardEq (by simpa [hRcard])
  let a : LeafAssignment H hconn hn L hL C copy Finset.univ :=
    { toFun := fun j ↦ (e j.1).1
      injective := by
        intro i j hij
        apply Subtype.ext
        apply e.injective
        apply Subtype.ext
        exact hij
      fresh_core := by
        intro j d heq
        have heR : (e j.1).1 ∈ R := (e j.1).2
        have heAvail : (e j.1).1 ∈ available := hRavailable heR
        have hnotRange := (Finset.mem_sdiff.mp heAvail).2
        apply hnotRange
        rw [Finset.mem_image]
        exact ⟨d, Finset.mem_univ _, heq.symm⟩
      adjacent_parent := by
        intro j
        let d := selectedLeafParent H hconn hn L hL j.1
        have hdK : copy d ∈ K := hcoreRangeK (by
          apply Finset.mem_image.mpr
          exact ⟨d, Finset.mem_univ _, rfl⟩)
        have heR : (e j.1).1 ∈ R := (e j.1).2
        have heAvail : (e j.1).1 ∈ available := hRavailable heR
        have heU : (e j.1).1 ∈ U := (Finset.mem_sdiff.mp heAvail).1
        apply hcross (copy d) hdK (e j.1).1 heU
        intro heq
        exact (Finset.mem_sdiff.mp heAvail).2 (by
          rw [Finset.mem_image]
          exact ⟨d, Finset.mem_univ _, heq⟩) }
  exact isContained_of_full_leafAssignment H hconn hn L hL C copy a

end Erdos570

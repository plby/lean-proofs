import ErdosProblems.Erdos19.ReservoirPartialCompletion
import ErdosProblems.Erdos19.ReservoirDegreePartition

/-! # Combining a buffered coloring with the reservoir completion -/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V]

theorem edgeColorable_of_buffered_outside_reservoir (H J : SetHypergraph V)
    (hJH : J ⊆ H) (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (m D : ℕ) (hD : 0 < D) (hvertices : Fintype.card V = m + D)
    (color : J.EdgeColoring (Fin m)) (palette : Finset (Fin m)) (bad : Fin m)
    (U Y Z : Set V) (hUY : Disjoint U Y) (z : V → I)
    (cK : (H.outsideReservoir J (insideBlocks H.twoGraph z)).EdgeColoring palette)
    (hcross : ∀ e : H.outsideReservoir J (insideBlocks H.twoGraph z), ∀ f : J,
      (e.1 ∩ f.1).Nonempty → (cK e).1 ≠ color f)
    (A missing load requests : ℕ)
    (hold : ∀ a ∈ palette, (J.coveredVertices {e | color e = a}).ncard ≤ A)
    (hmissing : ∀ v ∈ U, (H.twoGraph.neighborSet v)ᶜ.ncard ≤ missing)
    (hload : ∀ v ∈ U,
      ((J.twoGraph ⊓ insideBlocks H.twoGraph z).neighborSet v).ncard ≤ load)
    (hrequestDegree : ∀ v ∈ U,
      m + ((insideBlocks H.twoGraph z).neighborSet v).ncard ≤
        (H.twoGraph.neighborSet v).ncard + requests)
    (hbuffer : ∀ j a, A + missing + load + requests ≤
      ((Y ∩ {v | z v = j}) \
        (H.outsideReservoir J (insideBlocks H.twoGraph z)).coveredVertices {e | cK e = a}).ncard)
    (hinactive : ∀ a, a ∉ palette → ∀ v ∈ U,
      v ∉ Z ∨ a ≠ bad → v ∈ J.coveredVertices {e | color e = a})
    (houtside : ∀ v, v ∉ U → ((insideBlocks H.twoGraph z).neighborSet v).ncard < D)
    (hindependent : ∀ x ∈ Z, ∀ y ∈ Z, ¬H.twoGraph.Adj x y) :
    H.EdgeColorable (m + D) := by
  classical
  let R := insideBlocks H.twoGraph z
  let K := H.outsideReservoir J R
  let cK' : K.EdgeColoring (Fin m) := cK.mapEmbedding ⟨Subtype.val, Subtype.val_injective⟩
  have hcross' : ∀ e : J, ∀ f : K, (e.1 ∩ f.1).Nonempty → color e ≠ cK' f := by
    intro e f hinter heq
    exact hcross f e (by simpa only [Set.inter_comm] using hinter) heq.symm
  let J₁ := J ∪ K
  let c₁ := J.unionColoring K color cK' hcross'
  have hJK : Disjoint J K := Set.disjoint_left.mpr
    (fun _ heJ heK ↦ heK.2 (Or.inl heJ))
  have hJ₁H : J₁ ⊆ H := Set.union_subset hJH (fun _ h ↦ h.1)
  have hcover (a : Fin m) : J₁.coveredVertices {e | c₁ e = a} =
      J.coveredVertices {e | color e = a} ∪ K.coveredVertices {e | cK' e = a} :=
    J.unionColoring_covered_eq_of_disjoint K color cK' hJK hcross' a
  let equiv : palette ≃ Fin palette.card := Fintype.equivFinOfCardEq (by simp)
  let index : Fin palette.card ↪ Fin m :=
    ⟨fun i ↦ (equiv.symm i).1, fun _ _ h ↦ equiv.symm.injective (Subtype.ext h)⟩
  have hrange (a : Fin m) : a ∈ Set.range index ↔ a ∈ palette := by
    constructor
    · rintro ⟨i, rfl⟩
      exact (equiv.symm i).2
    · intro ha
      refine ⟨equiv ⟨a, ha⟩, ?_⟩
      change (equiv.symm (equiv ⟨a, ha⟩)).1 = a
      rw [equiv.symm_apply_apply]
  have hKcover (i : Fin palette.card) :
      K.coveredVertices {e | cK' e = index i} = K.coveredVertices {e | cK e = equiv.symm i} := by
    congr 1
    ext e
    exact Subtype.val_injective.eq_iff
  let B : Fin palette.card → I → Set V := fun i j ↦
    (Y ∩ {v | z v = j}) \ J₁.coveredVertices {e | c₁ e = index i}
  have hBsize (i : Fin palette.card) (j : I) :
      missing + load + requests ≤ (B i j).ncard := by
    have hnew := hbuffer j (equiv.symm i)
    have hold' := hold (index i) ((hrange _).mp ⟨i, rfl⟩)
    let T := (Y ∩ {v | z v = j}) \ K.coveredVertices {e | cK e = equiv.symm i}
    have hcount := Set.ncard_le_ncard_sdiff_add_ncard T
      (J.coveredVertices {e | color e = index i})
    have hB : T \ J.coveredVertices {e | color e = index i} = B i j := by
      dsimp only [B, T]
      rw [hcover, hKcover]
      ext v
      simp only [Set.mem_sdiff, Set.mem_union]
      tauto
    rw [hB] at hcount
    change A + missing + load + requests ≤ T.ncard at hnew
    omega
  apply H.edgeColorable_of_block_reservoir_coloring J₁ hJ₁H hlinear hmin
    (fun e he hnot ↦ graphPairs_size R
      ⟨e, H.remaining_after_outsideReservoir_subset_pairs J R ⟨he, hnot⟩⟩)
    m D hD hvertices c₁ palette.card index bad U Y Z hUY z J.twoGraph
    (H.remaining_after_outsideReservoir_graph J R (insideBlocks_le _ _))
    missing load requests hmissing ?_ hrequestDegree B
    (fun _ _ _ h ↦ h.1.1) (fun _ _ _ h ↦ h.1.2)
    (fun _ _ ↦ Set.disjoint_left.mpr (fun _ h h' ↦ h.2 h')) hBsize ?_ houtside hindependent
  · intro v hv
    simpa only [inf_comm] using hload v hv
  · intro a ha v hv hbad
    rw [hcover]
    exact Or.inl (hinactive a (fun h ↦ ha ((hrange a).mpr h)) v hv hbad)

#print axioms edgeColorable_of_buffered_outside_reservoir

end Erdos19.SetHypergraph

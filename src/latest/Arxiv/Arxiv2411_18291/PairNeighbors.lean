import Arxiv.Arxiv2411_18291.PairPackingAugmentation

/-! # Neighbor counts for a family of pairs -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V]

theorem pair_eq_of_mem {Q : Block V 2} {u v : V} (huv : u ≠ v)
    (hu : u ∈ Q.val) (hv : v ∈ Q.val) : Q.val = {u, v} := by
  apply (eq_of_subset_of_card_le (insert_subset hu (singleton_subset_iff.mpr hv)) ?_).symm
  simp only [Q.property, card_pair huv]
  rfl

theorem PairAdjacent.ne {H : Finset (Block V 2)} {u v : V} (h : PairAdjacent H u v) :
    u ≠ v := by
  obtain ⟨Q, _, hQ⟩ := h
  intro huv
  have hc := Q.property
  rw [hQ, huv, pair_eq_singleton, card_singleton] at hc
  omega

def pairNeighbors (H : Finset (Block V 2)) (u : V) : Finset V :=
  (H.filter fun Q => u ∈ Q.val).biUnion fun Q => Q.val.erase u

theorem mem_pairNeighbors (H : Finset (Block V 2)) (u v : V) :
    v ∈ pairNeighbors H u ↔ PairAdjacent H u v := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hv⟩ := mem_biUnion.mp h
    obtain ⟨hQH, huQ⟩ := mem_filter.mp hQ
    obtain ⟨hvu, hvQ⟩ := mem_erase.mp hv
    exact ⟨Q, hQH, pair_eq_of_mem hvu.symm huQ hvQ⟩
  · intro h
    obtain ⟨Q, hQH, hQ⟩ := h
    refine mem_biUnion.mpr ⟨Q, mem_filter.mpr ⟨hQH, ?_⟩, ?_⟩
    · simp only [hQ, mem_insert, mem_singleton, true_or]
    · exact mem_erase.mpr ⟨(PairAdjacent.ne ⟨Q, hQH, hQ⟩).symm, by simp [hQ]⟩

theorem card_pairNeighbors (H : Finset (Block V 2)) (u : V) :
    (pairNeighbors H u).card = (H.filter fun Q => u ∈ Q.val).card := by
  have hdis : ((H.filter fun Q => u ∈ Q.val) : Set (Block V 2)).PairwiseDisjoint
      (fun Q => Q.val.erase u) := by
    intro Q hQ R hR hQR
    apply disjoint_left.mpr
    intro v hvQ hvR
    obtain ⟨hvu, hvQ⟩ := mem_erase.mp hvQ
    have hvR := (mem_erase.mp hvR).2
    exact hQR (Subtype.ext ((pair_eq_of_mem hvu.symm (mem_filter.mp hQ).2 hvQ).trans
      (pair_eq_of_mem hvu.symm (mem_filter.mp hR).2 hvR).symm))
  rw [pairNeighbors, card_biUnion hdis]
  calc
    ∑ Q ∈ H.filter (fun Q => u ∈ Q.val), (Q.val.erase u).card =
        ∑ _Q ∈ H.filter (fun Q => u ∈ Q.val), 1 := by
      apply sum_congr rfl
      intro Q hQ
      rw [card_erase_of_mem (mem_filter.mp hQ).2, Q.property]
    _ = _ := by simp

theorem IsMaximumVertexPacking.neighbors_subset_support {H D : Finset (Block V 2)}
    (hD : IsMaximumVertexPacking H D) {u : V} (hu : u ∉ vertexSupport D) :
    pairNeighbors H u ⊆ vertexSupport D := by
  intro v hv
  obtain ⟨Q, hQH, hQ⟩ := (mem_pairNeighbors H u v).mp hv
  by_contra hvD
  apply hD.not_disjoint (by decide) hQH
  apply disjoint_left.mpr
  intro x hx hxD
  rw [hQ] at hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hu hxD
  · exact hvD ((mem_singleton.mp hx) ▸ hxD)

theorem IsVertexPacking.card_eq_sum_inter {D : Finset (Block V 2)}
    (hD : IsVertexPacking D) {S : Finset V} (hS : S ⊆ vertexSupport D) :
    S.card = ∑ P ∈ D, (P.val ∩ S).card := by
  have heq : D.biUnion (fun P => P.val ∩ S) = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨P, _, hP⟩ := mem_biUnion.mp hv
      exact (mem_inter.mp hP).2
    · intro hv
      obtain ⟨P, hP, hvP⟩ := mem_biUnion.mp (hS hv)
      exact mem_biUnion.mpr ⟨P, hP, mem_inter.mpr ⟨hvP, hv⟩⟩
  have hd : (D : Set (Block V 2)).PairwiseDisjoint (fun P => P.val ∩ S) := by
    intro P hP Q hQ hPQ
    exact (hD hP hQ hPQ).mono inter_subset_left inter_subset_left
  calc
    S.card = (D.biUnion fun P => P.val ∩ S).card := congrArg Finset.card heq.symm
    _ = _ := card_biUnion hd

end Arxiv2411_18291

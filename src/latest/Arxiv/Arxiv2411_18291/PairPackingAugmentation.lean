import Arxiv.Arxiv2411_18291.MaximumVertexPacking

/-! # Two-edge augmentations of a maximum matching -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q : ℕ}

@[simp] theorem vertexSupport_insert (Q : Block V q) (D : Finset (Block V q)) :
    vertexSupport (insert Q D) = Q.val ∪ vertexSupport D := by
  simp only [vertexSupport, biUnion_insert]

theorem IsMaximumVertexPacking.no_two_replacements {H D : Finset (Block V q)}
    (hD : IsMaximumVertexPacking H D) (hq : 0 < q) {P Q R : Block V q}
    (hP : P ∈ D) (hQH : Q ∈ H) (hRH : R ∈ H) (hQR : Disjoint Q.val R.val)
    (hQ : Disjoint Q.val (vertexSupport (D.erase P)))
    (hR : Disjoint R.val (vertexSupport (D.erase P))) : False := by
  have hQ' : Disjoint Q.val (vertexSupport (insert R (D.erase P))) := by
    rw [vertexSupport_insert]
    exact disjoint_union_right.mpr ⟨hQR, hQ⟩
  have hpack := ((hD.packing.mono (erase_subset P D)).insert hR).insert hQ'
  have hmax := hD.maximum (insert Q (insert R (D.erase P)))
    (insert_subset hQH (insert_subset hRH ((erase_subset P D).trans hD.subset))) hpack
  rw [card_insert_of_notMem (notMem_of_disjoint_vertexSupport hq hQ'),
    card_insert_of_notMem (notMem_of_disjoint_vertexSupport hq hR), card_erase_of_mem hP] at hmax
  have hpos := card_pos.mpr ⟨P, hP⟩
  omega

theorem IsVertexPacking.disjoint_erase_support {D : Finset (Block V q)}
    (hD : IsVertexPacking D) {P Q : Block V q} (hP : P ∈ D) {U : Finset V}
    (hU : Disjoint U (vertexSupport D)) (hQ : Q.val ⊆ U ∪ P.val) :
    Disjoint Q.val (vertexSupport (D.erase P)) := by
  apply disjoint_left.mpr
  intro x hxQ hxD
  obtain ⟨R, hR, hxR⟩ := mem_biUnion.mp hxD
  obtain ⟨hRP, hRD⟩ := mem_erase.mp hR
  rcases mem_union.mp (hQ hxQ) with hxU | hxP
  · exact disjoint_left.mp hU hxU (subset_vertexSupport hRD hxR)
  · exact disjoint_left.mp (hD hP hRD hRP.symm) hxP hxR

def PairAdjacent (H : Finset (Block V 2)) (u v : V) : Prop :=
  ∃ Q ∈ H, Q.val = {u, v}

theorem PairAdjacent.symm {H : Finset (Block V 2)} {u v : V}
    (h : PairAdjacent H u v) : PairAdjacent H v u := by
  obtain ⟨Q, hQ, heq⟩ := h
  exact ⟨Q, hQ, heq.trans (pair_comm _ _)⟩

theorem IsMaximumVertexPacking.no_cross {H D : Finset (Block V 2)}
    (hD : IsMaximumVertexPacking H D) {P : Block V 2} (hP : P ∈ D)
    {u v a b : V} (hu : u ∉ vertexSupport D) (hv : v ∉ vertexSupport D)
    (huv : u ≠ v) (ha : a ∈ P.val) (hb : b ∈ P.val) (hab : a ≠ b)
    (hua : PairAdjacent H u a) (hvb : PairAdjacent H v b) : False := by
  obtain ⟨Q, hQH, hQ⟩ := hua
  obtain ⟨R, hRH, hR⟩ := hvb
  have hub : u ≠ b := fun h => hu (h ▸ subset_vertexSupport hP hb)
  have hav : a ≠ v := fun h => hv (h ▸ subset_vertexSupport hP ha)
  have hQR : Disjoint Q.val R.val := by simp [hQ, hR, huv.symm, hub.symm, hav.symm, hab.symm]
  have hQsub : Q.val ⊆ {u} ∪ P.val := by simp [hQ, insert_subset_iff, ha]
  have hRsub : R.val ⊆ {v} ∪ P.val := by simp [hR, insert_subset_iff, hb]
  exact hD.no_two_replacements (by decide) hP hQH hRH hQR
    (hD.packing.disjoint_erase_support hP (by simpa using hu) hQsub)
    (hD.packing.disjoint_erase_support hP (by simpa using hv) hRsub)

end Arxiv2411_18291

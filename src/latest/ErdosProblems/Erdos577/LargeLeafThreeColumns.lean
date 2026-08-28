import ErdosProblems.Erdos577.LargeLeafThreeNoDense

/-! The missing leaf column has no noncentral neighbor; the other three columns are occupied. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_last_noncentral {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3) :
    ¬G.Adj (p.vertices 2) (q 3) ∧ ¬G.Adj (p.vertices 3) (q 3) := by
  have hm : q 3 ∈ s := hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩
  have hFS : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hcol := JointClaims.triangle_column_le_one hc hcard hn p hp hs (by omega) (q 3) hm
  have hmiss : ¬G.Adj (q 3) p.leaf := fun hh ↦ (hrow 3).mp hh.symm rfl
  have hF : degreeIn G (q 3) p.support ≤ 1 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle,
      if_neg hmiss, zero_add]
    exact hcol
  have hd13 := FullRow.last_diagonal hc p hp hs q hq (fun i hi ↦ (hrow i).mpr hi)
  have hQ : degreeIn G (q 3) s = 3 := by
    rw [← hq, q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 3
    rw [if_pos hd13.symm]
  have hrep := FullRow.first_replacement hc p hp hs q hq (fun i hi ↦ (hrow i).mpr hi)
  rw [hq] at hrep
  have hno : ¬(G.Adj (q 3) (p.vertices 2) ∨ G.Adj (q 3) (p.vertices 3)) := by
    intro hh
    have hbound := three_occupied_inside_ge_five hc hcard hdeg hn p hp hs hthree hnon
      (q 3) hm hh hrep.1 hrep.2
    rw [degreeIn_union G (q 3) hFS] at hbound
    omega
  exact ⟨fun hh ↦ hno (Or.inl hh.symm), fun hh ↦ hno (Or.inr hh.symm)⟩

theorem three_noncentral_sum {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s = 3 := by
  have hh := TwoExposed.large_leaf_weighted_le_six hc hcard hdeg hn p hp hs (by omega)
  omega

theorem three_union_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3) :
    ∀ i : Fin 4, (G.Adj (p.vertices 2) (q i) ∨ G.Adj (p.vertices 3) (q i)) ↔ i ≠ 3 := by
  have hnot := three_last_noncentral hc hcard hdeg hn p hp hs hthree hnon q hq hrow
  have hsum := three_noncentral_sum hc hcard hdeg hn p hp hs hthree hnon
  have hdis := JointClaims.triangle_rows_disjoint hc hcard hn p hp hs (by omega)
    (p.vertices 2) (p.vertices 3) (by simp [Paw.triangle]) (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3))
  let occupied := s.filter (G.Adj (p.vertices 2)) ∪ s.filter (G.Adj (p.vertices 3))
  have hcardOcc : occupied.card = 3 := by
    rw [card_union_of_disjoint hdis]
    exact hsum
  have hsub : occupied ⊆ s.erase (q 3) := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨hv, hadj⟩ := mem_filter.mp hv
      exact mem_erase.mpr ⟨fun he ↦ hnot.1 (he ▸ hadj), hv⟩
    · obtain ⟨hv, hadj⟩ := mem_filter.mp hv
      exact mem_erase.mpr ⟨fun he ↦ hnot.2 (he ▸ hadj), hv⟩
  have hm (i : Fin 4) : q i ∈ s := hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩
  have heq : occupied = s.erase (q 3) := eq_of_subset_of_card_le hsub (by
    rw [card_erase_of_mem (hm 3), (c.property.blocks_quad s hs).card, hcardOcc])
  intro i
  constructor
  · intro hh hi
    subst i
    exact hh.elim hnot.1 hnot.2
  · intro hi
    have hin : q i ∈ occupied := heq.symm ▸ mem_erase.mpr ⟨q.injective.ne hi, hm i⟩
    rcases mem_union.mp hin with hh | hh
    · exact Or.inl (mem_filter.mp hh).2
    · exact Or.inr (mem_filter.mp hh).2

end Erdos577.LargeLeaf

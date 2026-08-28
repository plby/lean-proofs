import ErdosProblems.Erdos577.LargeLeafFullTwoExcluded

/-! The complete full-leaf half of TeX9.70.
The universal bound is applied to an actual changed-center chain. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_center_zero_of_neighbor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (u : V) (hu : u ∈ s) (hbu : G.Adj (p.vertices 2) u) :
    degreeIn G p.center s = 0 := by
  have hdis : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have huout : u ∉ p.support := fun hh ↦ disjoint_left.mp hdis hh hu
  let p' := JointClaims.secondPaw p u huout hbu
  obtain ⟨d, hd, ht, hT, _, _, hblocks⟩ := FullRow.exists_full_leaf_swap hc p hp hs hfull u hu
  have hp' : p'.support = d.remainder := by
    rw [JointClaims.secondPaw_support]
    change insert u p.triangle = insert d.terminal d.triangle
    rw [ht, hT]
  have hnew : insert p.leaf (s.erase u) ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have hcl := FullRow.full_leaf_clique hc p hp hs hfull
  have hxout : p.leaf ∉ s := (c.presentPaw p hp).terminal_not_mem_block hs
  have hxe : p.leaf ∉ s.erase u := fun hh ↦ hxout (mem_erase.mp hh).2
  have hxu := (degreeIn_eq_card_iff p.leaf s).mp (hfull.trans hcl.card_eq.symm) u hu
  have hinside := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hinside
  have hfull' : degreeIn G p'.leaf (insert p.leaf (s.erase u)) = 4 := by
    change degreeIn G u (insert p.leaf (s.erase u)) = 4
    rw [degreeIn_insert G u p.leaf hxe, if_pos hxu.symm, degreeIn_erase_self G u hu, hinside]
  have hsmall := full_second_le_one hd hcard hdeg hn p' hp' hnew hfull'
  change degreeIn G p.center (insert p.leaf (s.erase u)) ≤ 1 at hsmall
  have hrows := JointClaims.triangle_rows_disjoint hc hcard hn p hp hs (by omega)
    p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hrnot : ¬G.Adj p.center u := fun hh ↦
    disjoint_left.mp hrows (mem_filter.mpr ⟨hu, hh⟩) (mem_filter.mpr ⟨hu, hbu⟩)
  have herase := degreeIn_erase_add G p.center u hu
  rw [if_neg hrnot] at herase
  rw [degreeIn_insert G p.center p.leaf hxe,
    if_pos (show G.Adj p.center p.leaf from p.pendant.symm)] at hsmall
  omega

theorem full_preparation {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4)
    (hpositive : 1 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    degreeIn G p.center s = 0 ∧ degreeIn G (p.vertices 2) s ≤ 1 ∧
      degreeIn G (p.vertices 3) s ≤ 1 ∧
      ∃ a ∈ c.blocks, a ≠ s ∧ 11 ≤ contacts G p.triangle a := by
  obtain ⟨z, hz, hadj⟩ : ∃ z ∈ s, G.Adj z (p.vertices 2) ∨ G.Adj z (p.vertices 3) := by
    by_cases hb : 0 < degreeIn G (p.vertices 2) s
    · obtain ⟨z, hz⟩ := card_pos.mp hb
      exact ⟨z, (mem_filter.mp hz).1, Or.inl (mem_filter.mp hz).2.symm⟩
    · have hpos : 0 < degreeIn G (p.vertices 3) s := by omega
      obtain ⟨z, hz⟩ := card_pos.mp hpos
      exact ⟨z, (mem_filter.mp hz).1, Or.inr (mem_filter.mp hz).2.symm⟩
  have hr : degreeIn G p.center s = 0 := by
    rcases hadj with hh | hh
    · exact full_center_zero_of_neighbor hc hcard hdeg hn p hp hs hfull z hz hh.symm
    · have hswap := full_center_zero_of_neighbor hc hcard hdeg hn p.swapNoncentral
        (by rw [Paw.swapNoncentral_support, hp]) hs
        (by simpa only [Paw.swapNoncentral_leaf] using hfull) z hz
        (by rw [Paw.swapNoncentral_apply, Equiv.swap_apply_left]; exact hh.symm)
      simpa only [Paw.swapNoncentral_center] using hswap
  have hb := full_noncentral_le_one hc hcard hdeg hn p hp hs hfull
  exact ⟨hr, hb.1, hb.2, full_dense_from_noncentral hc hcard hdeg hn p hp hs hfull hr z hz hadj⟩

end Erdos577.LargeLeaf

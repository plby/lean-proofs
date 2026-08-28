import ErdosProblems.Erdos577.JointLeafCommon

/-! With a small third row, neither exposed leaf can have three contacts on a heavy block. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_third_high_leaf_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q ∨ CaseTwo p q)
    (hweight : 13 ≤ sixWeight p q a) (hsmall : degreeIn G (p.vertices 3) a ≤ 2)
    (hhigh : 3 ≤ degreeIn G p.leaf a ∨ 3 ≤ degreeIn G (q 3) a) : False := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hout (i : Fin 4) : p.vertices i ∉ a :=
    fun hh ↦ disjoint_left.mp hFA ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) hh
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ hcase
  let p' := exposedPaw p q hFQ hcase
  have had := hkeep a ha has
  have htri' : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ hcase
  have hcol (u : V) (hu : u ∈ a) : degreeIn G u p.triangle ≤ 1 := by
    rcases hhigh with hx | ht
    · exact triangle_column_le_one hc hcard hn p hp ha hx u hu
    · have hh := triangle_column_le_one hd.toFeasible hcard hn p' hp' had ht u hu
      rwa [htri'] at hh
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  have hT : contacts G p.triangle a ≤ 4 := by
    rw [contacts_comm]
    calc
      _ ≤ ∑ _ ∈ a, 1 := sum_le_sum hcol
      _ = 4 := by simp [hacard]
  rw [p.contacts_triangle] at hT
  change degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) ≤ 4 at hT
  have hbound (z : V) : degreeIn G z a ≤ 4 := (degreeIn_le_card G z a).trans_eq hacard
  have hxbound := hbound p.leaf
  have htbound := hbound (q 3)
  rw [sixWeight_eq_rows] at hweight
  have hsum : 7 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a := by omega
  have hxthree : 3 ≤ degreeIn G p.leaf a := by omega
  have htthree : 3 ≤ degreeIn G (q 3) a := by omega
  have hcl : G.IsNClique 4 a := by
    by_cases hxfull : degreeIn G p.leaf a = 4
    · exact (hc.presentPaw_feasible p hp).clique_of_terminal_degree_four ha hxfull
    · have htfull : degreeIn G (q 3) a = 4 := by omega
      exact (hd.toFeasible.presentPaw_feasible p' hp').clique_of_terminal_degree_four had htfull
  have htuniv (u : V) (hu : u ∈ a) : QuadOn G (insert (q 3) (a.erase u)) :=
    (hd.toFeasible.presentPaw_feasible p' hp').terminal_universal_replace had htthree hu
  have hxc : 5 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 3) a := by omega
  have hcommon := common_replacement_of_five hacard p.leaf (p.vertices 3) (q 3) hxc htuniv
  have hI := case_one_of_failed_replacement hc p hp hs q hq hcase
    (fun hrep ↦ common_third_first_factor hcard hn p hp hs ha has q hq hcommon hrep)
  by_cases htwo : degreeIn G (p.vertices 3) a = 2
  · have hh := clique_common_replacement_of_seven hcl p.leaf (q 3) (p.vertices 3)
      (hout 3) hsum (by omega)
    exact case_one_common_factor hcard hn p hp hs ha has q hq hI hh
  have hxfull : degreeIn G p.leaf a = 4 := by omega
  have htfull : degreeIn G (q 3) a = 4 := by omega
  have hcone : degreeIn G (p.vertices 3) a = 1 := by omega
  have hrb : degreeIn G p.center a + degreeIn G (p.vertices 2) a = 3 := by omega
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < degreeIn G (p.vertices 3) a by rw [hcone]; decide)
  obtain ⟨hva, hcv⟩ := mem_filter.mp hv
  obtain ⟨hrv, hbv⟩ := third_neighbor_noncontacts p v (hcol v hva) hcv
  have hxv := (degreeIn_eq_card_iff p.leaf a).mp (hxfull.trans hacard.symm) v hva
  have htv := (degreeIn_eq_card_iff (q 3) a).mp (htfull.trans hacard.symm) v hva
  by_cases hbtwo : 2 ≤ degreeIn G (p.vertices 2) a
  · exact third_common_false hcard hn p hp ha
      ⟨v, hva, hxv, hcv, clique_replace_nonadjacent hcl (p.vertices 2) v (hout 2) hva hbtwo hbv⟩
  · apply third_common_false hcard hn p' hp' had
    change CommonReplacement G (q 3) (p.vertices 3) p.center a
    exact ⟨v, hva, htv, hcv, clique_replace_nonadjacent hcl p.center v
      (hout 1) hva (by omega) hrv⟩

end Erdos577.JointClaims

import ErdosProblems.Erdos577.CoreCliqueEquality
import ErdosProblems.Erdos577.CoreCliqueOffcenterFactor
import ErdosProblems.Erdos577.CoreCliqueCenterFactor

/-! The complete-core equality case gives an actual factor
in either location of the unique neighbor. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem complete_core_low_contact_false (c : TriangleChain G)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hclique : G.IsNClique 7 (c.triangle ∪ b))
    (center : V) (hcenter : center ∈ c.triangle) (hcx : G.Adj center c.terminal)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ c.triangle ∪ b) (hz₂ : z₂ ∈ c.triangle ∪ b)
    (hz12 : z₁ ≠ z₂) (hz1c : z₁ ≠ center) (hz2c : z₂ ≠ center)
    (hz10 : G.Adj z₁ (q 0)) (hz11 : G.Adj z₁ (q 1)) (hz12q : G.Adj z₁ (q 2))
    (hz20 : G.Adj z₂ (q 0)) (hz22 : G.Adj z₂ (q 2))
    (hhigh : G.Adj c.terminal (q 0)) (hlow : degreeIn G c.terminal {q 1, q 3} = 1)
    (h1 : degreeIn G (q 1) (c.triangle ∪ b) = 1)
    (h3 : degreeIn G (q 3) (c.triangle ∪ b) = 1) : False := by
  have hd : Disjoint (c.triangle ∪ b) q.support := disjoint_union_left.mpr
    ⟨c.triangle_disjoint_block hq, c.property.blocks_disjoint hb hq hbq⟩
  have hx : c.terminal ∉ (c.triangle ∪ b) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_union.mp hh).elim c.property.terminal_not_mem (c.terminal_not_mem_block hb)
    · exact c.terminal_not_mem_block hq hh
  have hcenterK : center ∈ c.triangle ∪ b := mem_union_left _ hcenter
  have hno : ¬Nonempty (BlockPartition G (insert c.terminal ((c.triangle ∪ b) ∪ q.support))) := by
    rintro ⟨p⟩
    have hsel : ({b, q.support} : Finset (Finset V)) ⊆ c.blocks := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hb, hq⟩
    have he : insert c.terminal ((c.triangle ∪ b) ∪ q.support) =
        c.remainder ∪ ({b, q.support} : Finset (Finset V)).biUnion id := by
      change _ = insert c.terminal c.triangle ∪ _
      simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, union_assoc]
    exact hn (c.complementPartition.hasPacking_of_selected_factor
      hcard {b, q.support} hsel (he ▸ p))
  have hpos : 0 < degreeIn G c.terminal {q 1, q 3} := by omega
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hwm, hxw⟩ := mem_filter.mp hw
  obtain ⟨i, hi, hxi⟩ : ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ G.Adj c.terminal (q i) := by
    rcases mem_insert.mp hwm with he | he
    · exact ⟨1, Or.inl rfl, he ▸ hxw⟩
    · exact ⟨3, Or.inr rfl, (mem_singleton.mp he) ▸ hxw⟩
  have hirow : degreeIn G (q i) (c.triangle ∪ b) = 1 := by
    rcases hi with rfl | rfl
    · exact h1
    · exact h3
  obtain ⟨h, hh⟩ := card_pos.mp (show 0 < degreeIn G (q i) (c.triangle ∪ b) by omega)
  obtain ⟨hhK, hih⟩ := mem_filter.mp hh
  have huniq (v : V) (hv : v ∈ c.triangle ∪ b) (hiv : G.Adj (q i) v) : v = h := by
    apply card_le_one.mp (show ((c.triangle ∪ b).filter (G.Adj (q i))).card ≤ 1 from hirow.le)
    · exact mem_filter.mpr ⟨hv, hiv⟩
    · exact mem_filter.mpr ⟨hhK, hih⟩
  by_cases hhc : h = center
  · have hi3 : i = 3 := by
      rcases hi with he | he
      · exact False.elim (hz1c ((huniq z₁ hz₁ (by rw [he]; exact hz11.symm)).trans hhc))
      · exact he
    have h3c : G.Adj (q 3) center := by simpa only [hi3, hhc] using hih
    exact hno (core_center_factor q hclique hd c.terminal center z₁ z₂ hx
      hcenterK hz₁ hz₂ hz1c.symm hz2c.symm hz12 hcx hhigh h3c hz11 hz22)
  · obtain ⟨z, hz, hzc, hzh, hz0, hz2⟩ : ∃ z ∈ c.triangle ∪ b,
        z ≠ center ∧ z ≠ h ∧ G.Adj z (q 0) ∧ G.Adj z (q 2) := by
      by_cases h1h : z₁ = h
      · exact ⟨z₂, hz₂, hz2c, fun he ↦ hz12 (h1h.trans he.symm), hz20, hz22⟩
      · exact ⟨z₁, hz₁, hz1c, h1h, hz10, hz12q⟩
    exact hno (core_offcenter_factor q hclique hd c.terminal center h z hx
      hcenterK hhK hz (Ne.symm hhc) hzc.symm hzh.symm hcx i hi hxi hih hz0 hz2)

theorem core_contact_sum_le_fourteen {c : TriangleChain G} (hc : c.Strong)
    {q : Quadrilateral G} {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (hfactor : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    (center : V) (hcenter : center ∈ c.triangle) (hcx : G.Adj center c.terminal)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ c.triangle ∪ b) (hz₂ : z₂ ∈ c.triangle ∪ b)
    (hz12 : z₁ ≠ z₂) (hz1c : z₁ ≠ center) (hz2c : z₂ ≠ center)
    (hz10 : G.Adj z₁ (q 0)) (hz11 : G.Adj z₁ (q 1)) (hz12q : G.Adj z₁ (q 2))
    (hz20 : G.Adj z₂ (q 0)) (hz22 : G.Adj z₂ (q 2)) :
    contacts G c.remainder b + contacts G {q 1, q 3} (c.remainder ∪ b) ≤ 14 := by
  by_contra! hh
  have hq := r.blocks_subset r.contains_cycle
  have hqb : q.support ≠ b := fun he ↦ hnb (he ▸ r.contains_cycle)
  have hrow := hc.toFeasible.terminal_degree_le_two_of_core_factor hcard hn hq hb hqb
    ((q.mem_support _).mpr ⟨2, rfl⟩) hfactor
  have hlow := terminal_low_degree_le_one q c.terminal r.high_contact hrow
  have h1 := r.low_core_degree_le_one hcard hn hb hnb hcore 1 (Or.inl rfl)
  have h3 := r.low_core_degree_le_one hcard hn hb hnb hcore 3 (Or.inr rfl)
  have hid := low_contacts_remainder_block c q hb
  have hB := hc.block_contacts_le_twelve hcard hdeg hn hb
  have h12 : contacts G c.remainder b = 12 := by omega
  have hclique := hc.complete_core_of_twelve hcard hdeg hn hb h12
  exact complete_core_low_contact_false c q hq hcard hn hb hqb.symm hclique
    center hcenter hcx z₁ z₂ hz₁ hz₂ hz12 hz1c hz2c hz10 hz11 hz12q hz20 hz22
    r.high_contact (by omega) (by omega) (by omega)

end Erdos577.CoreTransfer

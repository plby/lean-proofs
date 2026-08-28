import ErdosProblems.Erdos577.CoreObstructionCounts

/-! Paw bounds in a bridge and the preliminary fifteen-contact bound on its core. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma QuadOn.replacement_degree_ge_two {s : Finset V} {x u : V} (hx : x ∉ s)
    (h : QuadOn G (insert x (s.erase u))) : 2 ≤ degreeIn G x s := by
  have hxe : x ∉ s.erase u := fun hh ↦ hx (mem_erase.mp hh).2
  have hh := h.two_le_degreeIn (mem_insert_self x (s.erase u))
  rw [degreeIn_insert G x x hxe] at hh
  simp only [SimpleGraph.irrefl, if_false, zero_add] at hh
  exact hh.trans (degreeIn_mono G x (erase_subset u s))

namespace CoreTransfer

variable [Fintype V]

theorem bridge_paw_cycle_bound {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hhigh : G.Adj c.terminal (q 0)) {d : Finset V} (hd : d ∈ c.blocks) (hdq : d ≠ q.support)
    (y : V) (hy : y ∈ d) (hrep : QuadOn G (insert c.terminal (d.erase y)))
    (hrow : 2 ≤ degreeIn G y q.support) : contacts G c.remainder q.support ≤ 8 := by
  by_contra! hh
  obtain ⟨p, hx, ht, hp⟩ := hc.exists_paw
  have hpos : 0 < degreeIn G p.leaf q.support := by
    rw [hx]
    exact card_pos.mpr ⟨q 0, mem_filter.mpr ⟨(q.mem_support _).mpr ⟨0, rfl⟩, hhigh⟩⟩
  have hclass := hc.toFeasible.first_paw_final hcard hdeg hn p hp hq q rfl
    (by rw [hp]; omega) hpos
  have hout : y ∉ p.support ∪ q.support := by
    intro hmem
    rcases mem_union.mp hmem with hmem | hmem
    · rw [hp] at hmem
      exact (mem_sdiff.mp (c.complementPartition.block_subset hd hy)).2 hmem
    · exact disjoint_left.mp (c.property.blocks_disjoint hd hq hdq) hy hmem
  have hf := hclass.2.2.1 y hout hrow
  rw [ht] at hf
  exact hn (c.hasPacking_of_core_replacement hcard hd hq hdq hy hf hrep)

theorem core_contact_sum_le_fifteen {c : TriangleChain G} (hc : c.Strong)
    {q : Quadrilateral G} {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (hfactor : LocalFactor G (insert (q 2) (c.triangle ∪ b))) :
    contacts G c.remainder b + contacts G {q 1, q 3} (c.remainder ∪ b) ≤ 15 := by
  have hq := r.blocks_subset r.contains_cycle
  have hqb : q.support ≠ b := fun he ↦ hnb (he ▸ r.contains_cycle)
  have hrow := hc.toFeasible.terminal_degree_le_two_of_core_factor hcard hn hq hb hqb
    ((q.mem_support _).mpr ⟨2, rfl⟩) hfactor
  have hlow := terminal_low_degree_le_one q c.terminal r.high_contact hrow
  have h1 := r.low_core_degree_le_one hcard hn hb hnb hcore 1 (Or.inl rfl)
  have h3 := r.low_core_degree_le_one hcard hn hb hnb hcore 3 (Or.inr rfl)
  have hid := low_contacts_remainder_block c q hb
  have hB := hc.block_contacts_le_twelve hcard hdeg hn hb
  omega

end CoreTransfer

end Erdos577

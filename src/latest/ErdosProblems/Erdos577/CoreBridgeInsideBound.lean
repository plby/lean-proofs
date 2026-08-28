import ErdosProblems.Erdos577.CoreCliqueEqualityExcluded

/-! The bridge inside upper bound is 46 after the complete-core equality is excluded. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem bridge_inside_upper {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3)) {d : Finset V} (hd : d ∈ c.blocks) (hdq : d ≠ q.support)
    (y : V) (hy : y ∈ d) (hrep : QuadOn G (insert c.terminal (d.erase y)))
    (hrow : 2 ≤ degreeIn G y q.support) (r : Route c q {q.support, d})
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ ({q.support, d} : Finset (Finset V)))
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (hfactor : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    (center : V) (hcenter : center ∈ c.triangle) (hcx : G.Adj center c.terminal)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ c.triangle ∪ b) (hz₂ : z₂ ∈ c.triangle ∪ b)
    (hz12 : z₁ ≠ z₂) (hz1c : z₁ ≠ center) (hz2c : z₂ ≠ center)
    (hz10 : G.Adj z₁ (q 0)) (hz11 : G.Adj z₁ (q 1)) (hz12q : G.Adj z₁ (q 2))
    (hz20 : G.Adj z₂ (q 0)) (hz22 : G.Adj z₂ (q 2))
    (hlowd : contacts G {q 1, q 3} d ≤ 4) :
    contacts G (rows c q) (c.remainder ∪ (b ∪ (q.support ∪ d))) ≤ 46 := by
  have hbq : b ≠ q.support := fun he ↦ hnb (mem_insert.mpr (Or.inl he))
  have hbd : b ≠ d := fun he ↦ hnb (mem_insert_of_mem (mem_singleton.mpr he))
  have h14 := core_contact_sum_le_fourteen hc r hcard hdeg hn hb hnb hcore hfactor
    center hcenter hcx z₁ z₂ hz₁ hz₂ hz12 hz1c hz2c hz10 hz11 hz12q hz20 hz22
  have hself := hc.remainder_self_contacts hcard hn
  have hC := bridge_paw_cycle_bound hc q hq hcard hdeg hn r.high_contact hd hdq y hy hrep hrow
  have hD := hc.block_contacts_le_eight_of_terminal_two hcard hdeg hn hd
    (hrep.replacement_degree_ge_two (c.terminal_not_mem_block hd))
  have htwo := rows_inside_two_blocks c q hq hb hbq hdiag
  have hrowsD : contacts G (rows c q) d = contacts G c.remainder d + contacts G {q 1, q 3} d := by
    rw [rows, contacts_union_left G (remainder_disjoint_lows c q hq)]
  have hdis : Disjoint (c.remainder ∪ (b ∪ q.support)) d := by
    apply disjoint_left.mpr
    intro v hv hvd
    rcases mem_union.mp hv with hv | hv
    · exact (mem_sdiff.mp (c.complementPartition.block_subset hd hvd)).2 hv
    · rcases mem_union.mp hv with hv | hv
      · exact disjoint_left.mp (c.property.blocks_disjoint hb hd hbd) hv hvd
      · exact disjoint_left.mp (c.property.blocks_disjoint hq hd hdq.symm) hv hvd
  have he : c.remainder ∪ (b ∪ (q.support ∪ d)) = (c.remainder ∪ (b ∪ q.support)) ∪ d := by
    simp only [union_assoc]
  rw [he, contacts_union_right G _ hdis]
  omega

end Erdos577.CoreTransfer

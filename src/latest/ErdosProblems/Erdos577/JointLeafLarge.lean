import ErdosProblems.Erdos577.JointLeafCommon
import ErdosProblems.Erdos577.JointLeafWeighted
import ErdosProblems.Erdos577.JointLeafDenseCounts
import ErdosProblems.Erdos577.FullRowObstruction

/-! The large-third-degree case closes through a three-cycle factor or the full-row obstruction. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem large_third_positive_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q ∨ CaseTwo p q)
    (hweight : 13 ≤ sixWeight p q a) (hlarge : 3 ≤ degreeIn G (p.vertices 3) a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a) : False := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hQA : Disjoint q.support a := by rw [hq]; exact c.property.blocks_disjoint hs ha has.symm
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ hcase
  let p' := exposedPaw p q hFQ hcase
  have had := hkeep a ha has
  have htri' : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ hcase
  have htout : q 3 ∉ p.support ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hFQ hh ((q.mem_support _).mpr ⟨3, rfl⟩)
    · exact disjoint_left.mp hQA ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  obtain ⟨hold8, hnew8⟩ := paired_contacts_le_eight hc hd.toFeasible hcard hdeg hn
    p p' hp hp' htri' ha had hlarge hlarge hpos
  have hold := p.contacts_support a
  have hnew : contacts G p'.support a = degreeIn G (q 3) a + contacts G p.triangle a := by
    rw [p'.contacts_support, htri']
    rfl
  have hw := hweight
  unfold sixWeight at hw
  rw [sixWeight_eq_rows] at hweight
  have hxc : 5 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 3) a := by omega
  have htc : 5 ≤ degreeIn G (q 3) a + degreeIn G (p.vertices 3) a := by omega
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  have hxbound := degreeIn_le_card G p.leaf a
  have hcbound := degreeIn_le_card G (p.vertices 3) a
  rw [hacard] at hxbound hcbound
  by_cases hnewheavy : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a +
      degreeIn G (p.vertices 3) a
  · obtain ⟨ht3, _, hcuniv, _⟩ := weighted_third_pair hd.toFeasible hcard hdeg hn p' hp' had
      hnewheavy htc
    have htuniv (u : V) (hu : u ∈ a) : QuadOn G (insert (q 3) (a.erase u)) :=
      (hd.toFeasible.presentPaw_feasible p' hp').terminal_universal_replace had ht3 hu
    have hcommon := common_replacement_of_five hacard p.leaf (p.vertices 3) (q 3) hxc htuniv
    have hI := case_one_of_failed_replacement hc p hp hs q hq hcase
      (fun hrep ↦ common_third_first_factor hcard hn p hp hs ha has q hq hcommon hrep)
    have hT : contacts G p.triangle a ≤ 4 := by
      have hh := triangle_contacts_le_four hd.toFeasible hcard hn p' hp' had ht3
      rwa [htri'] at hh
    have hxt : 5 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a := by omega
    exact case_one_common_factor hcard hn p hp hs ha has q hq hI
      (common_replacement_of_five hacard p.leaf (q 3) (p.vertices 3) hxt hcuniv)
  have holdheavy : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a := by omega
  obtain ⟨hx3, _, hcuniv, hcommon⟩ := weighted_third_pair hc hcard hdeg hn p hp ha holdheavy hxc
  have hT := triangle_contacts_le_four hc hcard hn p hp ha hx3
  have hxt : 5 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a := by omega
  have hnotI : ¬CaseOne p q := fun hI ↦ case_one_common_factor hcard hn p hp hs ha has q hq hI
    (common_replacement_of_five hacard p.leaf (q 3) (p.vertices 3) hxt hcuniv)
  have hII : CaseTwo p q := hcase.resolve_left hnotI
  have ht1 : degreeIn G (q 3) a ≤ 1 := by
    by_contra! hh
    exact common_third_first_factor hcard hn p hp hs ha has q hq
      (hcommon (q 3) htout (by omega))
      (case_two_universal hc p hp hs q hq hII (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩))
  have hxfull : degreeIn G p.leaf a = 4 := by omega
  have hcfull : degreeIn G (p.vertices 3) a = 4 := by omega
  have hlast : degreeIn G (q 3) a = 1 := by omega
  exact FullRow.direct_obstruction hc hcard hdeg hn p hp hs q hq
    (first_rows p q hcase).1 hII.1 (first_rows p q hcase).2 ha has hxfull hcfull hlast

end Erdos577.JointClaims

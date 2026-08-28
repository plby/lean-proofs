import ErdosProblems.Erdos577.WeightedTwelveInside

/-! Both actual common-column factors exclude a full first terminal on the heavy block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem no_common_third {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q) :
    ¬CommonReplacement G p.leaf (p.vertices 3) (q 3) a := by
  intro hh
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  exact JointClaims.common_third_first_factor hcard hn p hp hs ha has q hq hh
    (h.universal p q hd (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩))

theorem full_leaf_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q)
    (hweight : 11 ≤ contacts G (five p q) a) (hfull : degreeIn G p.leaf a = 4) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hTsmall := JointClaims.triangle_contacts_le_four hc hcard hn p hp ha (by omega)
  rw [(five_data p q hd).2, p.contacts_support] at hweight
  have hy3 : 3 ≤ degreeIn G (q 3) a := by omega
  obtain ⟨e, he, heY, _, hp', hq', _, _, _, hpat', hkeep⟩ :=
    exists_swap hc hcard hn p hp hs q hq hd h
  let p' := exposedPaw p q hd h
  let q' := exposedQuad p q hd h
  have ha' := hkeep a ha has
  have hYrep (u : V) (hu : u ∈ a) : QuadOn G (insert (q 3) (a.erase u)) := by
    have hh := he.toFeasible.terminal_universal_replace ha'.1 (by rw [heY]; exact hy3) hu
    rwa [heY] at hh
  have hno := no_common_third hcard hn p hp hs ha has q hq h
  have hXall : ∀ u ∈ a, G.Adj p.leaf u :=
    (degreeIn_eq_card_iff p.leaf a).mp (hfull.trans (c.property.blocks_quad a ha).card.symm)
  have hczero : degreeIn G (p.vertices 3) a = 0 := by
    apply (degreeIn_eq_zero_iff (G := G) (p.vertices 3) a).mpr
    intro u hu hcu
    exact hno ⟨u, hu, hXall u hu, hcu, hYrep u hu⟩
  have hbound := (hc.claim_two_four hcard hdeg hn p hp ha).1
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have hyr : 5 ≤ degreeIn G (q 3) a + degreeIn G p.center a := by omega
  have hXrep (u : V) (hu : u ∈ a) : QuadOn G (insert p.leaf (a.erase u)) :=
    (hc.presentPaw_feasible p hp).terminal_universal_replace ha (by
      change 3 ≤ degreeIn G p.leaf a
      omega) hu
  have hcommon := JointClaims.common_replacement_of_five (c.property.blocks_quad a ha).card
    (q 3) p.center p.leaf hyr hXrep
  have hno' := no_common_third hcard hn p' hp' hq' ha'.1 ha'.2 q' rfl hpat'
  change ¬CommonReplacement G (q 3) p.center (q' 3) a at hno'
  have hlast : q' 3 = p.leaf := (exposedQuad_apply p q hd h 3).trans (if_pos rfl)
  rw [hlast] at hno'
  exact hno' hcommon

end Erdos577.WeightedTwelve

import ErdosProblems.Erdos577.WeightedTwelveSmall

/-! Claim2.2 forces both terminal rows to vanish.
The remaining triangle has eleven contacts with a complete block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_block_dense {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q)
    (hweight : 11 ≤ contacts G (five p q) a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G (q 3) a = 0 ∧
      11 ≤ contacts G p.triangle a ∧ G.IsNClique 4 a := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨_, hysmall⟩ := terminal_degrees_le_two hc hcard hdeg hn p hp hs ha has q hq h hweight
  obtain ⟨e, he, heY, heT, hp', _, _, _, _, _, hkeep⟩ :=
    exists_swap hc hcard hn p hp hs q hq hd h
  let p' := exposedPaw p q hd h
  have ha' := (hkeep a ha has).1
  have hw := hweight
  rw [(five_data p q hd).2] at hw
  have hFheavy : 9 ≤ contacts G p.support a := by omega
  have hYout : q 3 ∉ p.support ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hd hh ((q.mem_support _).mpr ⟨3, rfl⟩)
    · exact disjoint_left.mp (c.property.blocks_disjoint hs ha has.symm)
        (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hxzero : degreeIn G p.leaf a = 0 := by
    by_contra hx
    have hpos : 0 < degreeIn G p.leaf a := by omega
    have hcount := (JointClaims.heavy_positive_counts hc hcard hdeg hn p hp ha hFheavy hpos).2.1
    have hy2 : 2 ≤ degreeIn G (q 3) a := by omega
    have hf := JointClaims.heavy_positive_outside_factor hc hcard hdeg hn p hp ha
      hFheavy hpos (q 3) hYout hy2
    apply e.no_local_factor hcard hn ha'
    change LocalFactor G (insert e.terminal e.triangle ∪ a)
    rw [heY, heT, insert_union]
    exact hf
  have hFsum := p.contacts_support a
  have hnewheavy : 11 ≤ contacts G p'.support a := by
    rw [p'.contacts_support, exposedPaw_triangle]
    change 11 ≤ degreeIn G (q 3) a + contacts G p.triangle a
    omega
  have hyzero : degreeIn G (q 3) a = 0 := by
    by_contra hy
    have hbound := JointClaims.positive_contacts_le_nine he.toFeasible hcard hdeg hn p' hp' ha'
      (by change 0 < degreeIn G (q 3) a; omega)
    omega
  have hT : 11 ≤ contacts G p.triangle a := by omega
  exact ⟨hxzero, hyzero, hT,
    ((hc.presentPaw_feasible p hp).all_triangle_universal_replacements ha hT).1⟩

end Erdos577.WeightedTwelve

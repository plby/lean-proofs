import ErdosProblems.Erdos577.WeightedPawLeafTwo
import ErdosProblems.Erdos577.FirstPawLeafTwo
import ErdosProblems.Erdos577.WeightedFourteenModel
import ErdosProblems.Erdos577.RowSaturation

/-! A heavy paw with a two-contact leaf and a small center has the exact pattern-(14) rows. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.paw_leaf_two_center_le_two {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) (hleaf : degreeIn G p.leaf q.support = 2)
    (hcenter : degreeIn G p.center q.support ≤ 2) :
    contacts G p.support q.support = 9 ∧ degreeIn G p.center q.support = 2 ∧
      ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
        ¬G.Adj (q' 1) (q' 3) ∧
        PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) q' ![5, 5, 13, 5] := by
  have hsum := p.contacts_support q.support
  rw [p.contacts_triangle] at hsum
  have hweighted : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support := by
    change degreeIn G (p.vertices 1) q.support ≤ 2 at hcenter
    omega
  have hclass := hc.weighted_paw_classification hcard hdeg hn p hp hb q hq hweighted
    (by omega)
  obtain ⟨swap, q', hq', hpattern⟩ := hclass.leaf_two p q hleaf
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := (FirstPaw.normalizedPaw_support p swap).trans hp
  have hqb : q'.support = b := hq'.trans hq
  have hd : Disjoint p'.support q'.support := by
    rw [hp', hqb]
    apply disjoint_left.mpr
    intro z hz hzb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hzb)).2 hz
  have hnon := WeightedFourteen.center_absent p' q' hd hpattern (by
    rw [hp', hqb]
    exact c.no_local_factor hcard hn hb)
  have hr0 := hpattern.2.1.degree p' q' 0 5
  have hr2 := hpattern.2.2.1.degree p' q' 2 13
  have hr3 := hpattern.2.2.2.degree p' q' 3 5
  have hm5 : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have hm13 : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  rw [hm5] at hr0 hr3
  rw [hm13] at hr2
  have hsum' := p'.contacts_support q'.support
  rw [p'.contacts_triangle] at hsum'
  change degreeIn G p'.leaf q'.support = 2 at hr0
  have hheavy' : 9 ≤ contacts G p'.support q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hheavy
  have hcenter' : degreeIn G p'.center q'.support ≤ 2 := by
    rw [FirstPaw.normalizedPaw_center, hq']
    exact hcenter
  have hr1 : degreeIn G p'.center q'.support = 2 := by
    change degreeIn G (p'.vertices 1) q'.support ≤ 2 at hcenter'
    change degreeIn G (p'.vertices 1) q'.support = 2
    omega
  have htotal : contacts G p'.support q'.support = 9 := by
    change degreeIn G (p'.vertices 1) q'.support = 2 at hr1
    omega
  have hrow1 : WeightedPawBlock.Row p' q' 1 5 := by
    apply q'.row_saturated (p'.vertices 1) 5
    · intro j hj
      fin_cases j
      · decide
      · exact False.elim (hnon.1 hj)
      · decide
      · exact False.elim (hnon.2 hj)
    · change _ ≤ degreeIn G p'.center q'.support
      rw [hm5, hr1]
  have hrows : PawBlock.ExactRows p' q' ![5, 5, 13, 5] := by
    intro i j
    fin_cases i
    · exact hpattern.2.1 j
    · exact hrow1 j
    · exact hpattern.2.2.1 j
    · exact hpattern.2.2.2 j
  have htotal' : contacts G p.support q.support = 9 := by
    rwa [FirstPaw.normalizedPaw_support, hq'] at htotal
  have hr1' : degreeIn G p.center q.support = 2 := by
    rwa [FirstPaw.normalizedPaw_center, hq'] at hr1
  exact ⟨htotal', hr1', swap, q', hq', hpattern.1, hrows⟩

theorem TriangleChain.Feasible.first_pattern5_exact {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) (hleaf : degreeIn G p.leaf q.support = 2)
    (h : PawBlock.Pattern5 p q) :
    contacts G p.support q.support = 9 ∧ degreeIn G p.center q.support = 2 ∧
      ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
        PawBlock.OnlyFirst q' ∧
        PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) q' ![5, 5, 13, 5] := by
  obtain ⟨htotal, hcenter, swap, q', hq', hnon, hrows⟩ :=
    hc.paw_leaf_two_center_le_two hcard hdeg hn p hp hb q hq hheavy hleaf (h.center_le_two p q)
  have hscore : edgeCount G q.support = 5 := by
    rw [q.edgeCount_eq, if_pos h.1.1, if_neg h.1.2]
  have hdiag : G.Adj (q' 0) (q' 2) := by
    have hh := q'.edgeCount_eq
    rw [hq', hscore, if_neg hnon] at hh
    by_contra hnot
    rw [if_neg hnot] at hh
    omega
  exact ⟨htotal, hcenter, swap, q', hq', ⟨hdiag, hnon⟩, hrows⟩

end Erdos577

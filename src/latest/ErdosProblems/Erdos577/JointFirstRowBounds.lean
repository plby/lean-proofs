import ErdosProblems.Erdos577.JointFirstNoFactor
import ErdosProblems.Erdos577.StarRowBounds

/-! The global no-factor hypothesis supplies all four row restrictions for CaseI. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem arms_row_restrictions {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hjs : j ≠ s) (haj : a ≠ j)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (hc1 : G.Adj p.center z1) (hc2 : G.Adj p.center z2)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hr1 : QuadOn G ((p.triangle ∪ a) \ {z1, p.center, p.vertices 2}))
    (hr2 : QuadOn G ((p.triangle ∪ a) \ {z2, p.center, p.vertices 2}))
    (hnine : 9 ≤ contacts G (arms p q z1 z2) j) :
    (∀ x ∈ arms p q z1 z2, ∀ y ∈ arms p q z1 z2, ∀ z ∈ arms p q z1 z2,
      x ≠ y → x ≠ z → y ≠ z → ¬CommonReplacement G x y z j) ∧
    (∀ z ∈ arms p q z1 z2, ¬(∀ u ∈ j, QuadOn G (insert z (j.erase u)))) ∧
    (∀ z ∈ arms p q z1 z2, degreeIn G z j ≤ 3) ∧
    degreeIn G p.leaf j ≤ 2 ∧ degreeIn G (q 1) j ≤ 2 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFJ : Disjoint p.support j := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hQJ : Disjoint q.support j := by rw [hq]; exact c.property.blocks_disjoint hs hj hjs.symm
  have hAJ : Disjoint a j := c.property.blocks_disjoint ha hj haj
  have hfour := arms_card p q hFQ z1 z2
    (fun hh ↦ disjoint_left.mp hFA hh h1) (fun hh ↦ disjoint_left.mp hFA hh h2)
    (fun hh ↦ disjoint_left.mp hAQ h1 hh) (fun hh ↦ disjoint_left.mp hAQ h2 hh) hne
  have hd : Disjoint (arms p q z1 z2) j :=
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hFJ, hQJ⟩, hAJ⟩).mono_left
      (arms_subset p q h1 h2)
  have hrj : p.center ∉ j := fun hh ↦ disjoint_left.mp hFJ
    ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hnoerase := arms_erase_no_factor hc hcard hn p hp hs ha hj has hjs haj q hq hcase
    h1 h2 hne hr hr1 hr2
  have htriples := fun t ht hthree ↦ triple_no_factor_of_erase hfour hnoerase
    (s := t) ht hthree
  have hcommon := fun x hx y hy z hz hxy hxz hyz ↦ no_common_of_star_triples hd hrj
    (arms_center p q hcase.2.1 hc1 hc2) htriples (x := x) (y := y) (z := z)
    hx hy hz hxy hxz hyz
  have hquad := c.property.blocks_quad j hj
  have huniversal := fun z hz ↦ no_universal_of_nine_contacts hfour hquad.card hnine
    hcommon (z := z) hz
  have hx : degreeIn G p.leaf j ≤ 2 := by
    by_contra hh
    have hthree : 3 ≤ degreeIn G p.leaf j := by omega
    exact huniversal p.leaf (by simp [arms]) (fun _ hu ↦
      (hc.presentPaw_feasible p hp).terminal_universal_replace hj hthree hu)
  have hv : degreeIn G (q 1) j ≤ 2 := by
    by_contra hh
    have hthree : 3 ≤ degreeIn G (q 1) j := by omega
    obtain ⟨d, hdf, ht, _, _, _, _, hkeep⟩ := exists_center_terminal hc hcard hn p hp hs q hq hcase
    apply huniversal (q 1) (by simp [arms])
    intro u hu
    have hh := hdf.toFeasible.terminal_universal_replace (hkeep j hj hjs)
      (by rw [ht]; exact hthree) hu
    rwa [ht] at hh
  exact ⟨hcommon, huniversal, row_le_three_of_nine_contacts hfour hquad hd hnine hcommon, hx, hv⟩

end Erdos577.JointFirst

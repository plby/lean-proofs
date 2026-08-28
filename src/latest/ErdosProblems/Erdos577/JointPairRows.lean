import ErdosProblems.Erdos577.JointPairGeometry

/-! The precise asymmetric row hypotheses, derived from the two actual chains. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure PairRows (v : Quadrilateral G) (x y z w : V) : Prop where
  x_out : x ∉ v.support
  y_out : y ∉ v.support
  z_out : z ∉ v.support
  w_out : w ∉ v.support
  x_pos : 1 ≤ degreeIn G x v.support
  x_bound : degreeIn G x v.support ≤ 2
  y_bound : degreeIn G y v.support ≤ 2
  nine : 9 ≤ degreeIn G x v.support + degreeIn G y v.support +
    degreeIn G z v.support + degreeIn G w v.support
  three : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)
  no_xz_w : ¬CommonReplacement G x z w v.support
  no_xw_z : ¬CommonReplacement G x w z v.support
  no_zw_x : ¬CommonReplacement G z w x v.support
  no_xz_y : ¬CommonReplacement G x z y v.support
  no_xw_y : ¬CommonReplacement G x w y v.support
  no_zw_y : ¬CommonReplacement G z w y v.support

lemma PairRows.distinguished_five {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) : 5 ≤ degreeIn G z v.support + degreeIn G w v.support := by
  have hx := h.x_bound
  have hy := h.y_bound
  have hn := h.nine
  omega

lemma PairRows.three_rows_seven {v : Quadrilateral G} {x y z w : V}
    (h : PairRows v x y z w) :
    7 ≤ degreeIn G x v.support + degreeIn G z v.support + degreeIn G w v.support := by
  have hy := h.y_bound
  have hn := h.nine
  omega

variable [Fintype V]

theorem Core.pair_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)) : PairRows v p.leaf (q 3) z w := by
  obtain ⟨_, hx2, hx3, _, _, h23⟩ := JointCore.four_distinct h.arms_card
  have hdata : z ∈ spokes p d ∧ w ∈ spokes p d ∧ p.leaf ≠ z ∧ p.leaf ≠ w ∧ z ≠ w := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [spokes], by simp [spokes], hx2, hx3, h23⟩
    · exact ⟨by simp [spokes], by simp [spokes], hx3, hx2, h23.symm⟩
  have hxS : p.leaf ∈ spokes p d := by simp [spokes]
  have hS := h.spokes_disjoint hj hja
  have hout (u : V) (hu : u ∈ spokes p d) : u ∉ v.support := by
    rw [hv]
    exact fun hh ↦ disjoint_left.mp hS hu hh
  have hyout : q 3 ∉ v.support := by
    rw [hv]
    exact fun hh ↦ disjoint_left.mp (h.arms_disjoint hj hjq hja) (by simp [arms]) hh
  refine ⟨hout _ hxS, hyout, hout _ hdata.1, hout _ hdata.2.1, ?_, ?_, ?_, ?_, hthree,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hv]
  · rw [hv]
    exact h.leaf_degree_le_two hc hcard hdeg hn hj hjq hja hnine
  · rw [hv]
    exact h.last_degree_le_two hc hcard hn hj hjq hja hnine
  · rw [hv]
    rw [h.arms_contacts] at hnine
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · rw [hv]
    exact h.no_leaf_common hcard hn hj hja hxS hdata.1 hdata.2.1
      hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2
  · rw [hv]
    exact h.no_leaf_common hcard hn hj hja hxS hdata.2.1 hdata.1
      hdata.2.2.2.1 hdata.2.2.1 hdata.2.2.2.2.symm
  · rw [hv]
    exact h.no_leaf_common hcard hn hj hja hdata.1 hdata.2.1 hxS
      hdata.2.2.2.2 hdata.2.2.1.symm hdata.2.2.2.1.symm
  · rw [hv]
    exact h.no_exposed_common hc hcard hn hj hjq hja hxS hdata.1 hdata.2.2.1
  · rw [hv]
    exact h.no_exposed_common hc hcard hn hj hjq hja hxS hdata.2.1 hdata.2.2.2.1
  · rw [hv]
    exact h.no_exposed_common hc hcard hn hj hjq hja hdata.1 hdata.2.1 hdata.2.2.2.2

end Erdos577.JointFinal

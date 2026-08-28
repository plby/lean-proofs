import ErdosProblems.Erdos577.JointFinalLastRow

/-! A full old leaf would force the already excluded full-row configuration. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma full_leaf_counts {j : Finset V} (hcl : G.IsNClique 4 j) (x y z w : V)
    (hyout : y ∉ j) (hzout : z ∉ j) (hx : degreeIn G x j = 4)
    (hy : degreeIn G y j ≤ 2) (hz : 2 ≤ degreeIn G z j)
    (hnine : 9 ≤ degreeIn G x j + degreeIn G y j + degreeIn G z j + degreeIn G w j)
    (hdis : ∀ u ∈ j, ¬(G.Adj z u ∧ G.Adj w u))
    (hno : ¬CommonReplacement G x w z j) (hnoY : ¬CommonReplacement G x z y j) :
    degreeIn G z j = 4 ∧ degreeIn G w j = 0 ∧ degreeIn G y j = 1 := by
  have hxall := (degreeIn_eq_card_iff x j).mp (hx.trans hcl.card_eq.symm)
  have hw0 : degreeIn G w j = 0 := by
    apply (degreeIn_eq_zero_iff (G := G) w j).mpr
    intro u hu hwu
    have hzu : ¬G.Adj z u := fun hh ↦ hdis u hu ⟨hh, hwu⟩
    have herase := degreeIn_erase_add G z u hu
    rw [if_neg hzu] at herase
    have hrep := (clique_replace_iff_two_contacts hcl hzout hu).mpr (by omega)
    exact hno ⟨u, hu, hxall u hu, hwu, hrep⟩
  have hz3 : 3 ≤ degreeIn G z j := by omega
  have hy1 : degreeIn G y j ≤ 1 := by
    by_contra hlarge
    obtain ⟨u, hu, hrep⟩ := clique_replace_in_three_candidates hcl y hyout (by omega)
      (j.filter (G.Adj z)) (filter_subset _ _) hz3
    exact hnoY ⟨u, (mem_filter.mp hu).1, hxall u (mem_filter.mp hu).1,
      (mem_filter.mp hu).2, hrep⟩
  have hz4 := degreeIn_le_card G z j
  rw [hcl.card_eq] at hz4
  exact ⟨by omega, hw0, by omega⟩

variable [Fintype V]

theorem Core.full_leaf_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hfull : degreeIn G p.leaf j = 4) : False := by
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hcf := hc.presentPaw_feasible p hp
  have hcl := hcf.clique_of_terminal_degree_four hj hfull
  have hy2 := h.last_degree_le_two hc hcard hn hj hjq hja hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  obtain ⟨_, hx1, hx2, _, _, h12⟩ := JointCore.four_distinct h.arms_card
  have hx : p.leaf ∈ spokes p d := by simp [spokes]
  have h1 : d 2 ∈ spokes p d := by simp [spokes]
  have h2 : d 3 ∈ spokes p d := by simp [spokes]
  have hxrep : ∀ u ∈ j, QuadOn G (insert p.leaf (j.erase u)) := fun _ hu ↦
    hcf.terminal_universal_replace hj (by change 3 ≤ degreeIn G p.leaf j; omega) hu
  have hdis := no_common_of_universal_insertion (d 2) (d 3) p.leaf j
    (h.no_leaf_common hcard hn hj hja h1 h2 hx h12 hx1.symm hx2.symm) hxrep
  have hyout : q 3 ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint hs hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hzout (i : Fin 4) : d i ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint ha hj hja.symm) (h.mem i) hh
  have excluded (z : V) (hz : z ∈ a) (hrz : G.Adj p.center z)
      (hzfull : degreeIn G z j = 4) (hyone : degreeIn G (q 3) j = 1) : False :=
    FullRow.other_obstruction hc hcard hdeg hn p hp hs q rfl
      (JointClaims.first_rows p q (Or.inr hcase)).1 hcase.1
      (JointClaims.first_rows p q (Or.inr hcase)).2 ha has z hz hrz
      (h.third_replacement z hz) h.outside_factor hj hjq hfull hzfull hyone
  by_cases hzlarge : 2 ≤ degreeIn G (d 2) j
  · obtain ⟨hzfull, _, hyone⟩ := full_leaf_counts hcl p.leaf (q 3) (d 2) (d 3)
      hyout (hzout 2) hfull hy2 hzlarge hsum hdis
      (h.no_leaf_common hcard hn hj hja hx h2 h1 hx2 hx1 h12.symm)
      (h.no_exposed_common hc hcard hn hj hjq hja hx h1 hx1)
    exact excluded (d 2) (h.mem 2) h.center_first hzfull hyone
  · have hlarge : 2 ≤ degreeIn G (d 3) j := by omega
    have hsum' : 9 ≤ degreeIn G p.leaf j + degreeIn G (q 3) j +
        degreeIn G (d 3) j + degreeIn G (d 2) j := by omega
    obtain ⟨hzfull, _, hyone⟩ := full_leaf_counts hcl p.leaf (q 3) (d 3) (d 2)
      hyout (hzout 3) hfull hy2 hlarge hsum' (fun u hu hh ↦ hdis u hu hh.symm)
      (h.no_leaf_common hcard hn hj hja hx h1 h2 hx1 hx2 h12)
      (h.no_exposed_common hc hcard hn hj hjq hja hx h2 hx2)
    exact excluded (d 3) (h.mem 3) h.center_second hzfull hyone

end Erdos577.JointFinal

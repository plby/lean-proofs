import ErdosProblems.Erdos577.LargeLeafFullInside

/-! No full leaf has a noncentral row of degree two.
The result is universal over feasible chains. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_two_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hsecond : 2 ≤ degreeIn G (p.vertices 2) s) : False := by
  obtain ⟨hb, _, hr⟩ := ordered_full_two_counts hc hcard hdeg hn p hp hs hfull hsecond
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (s.filter (G.Adj (p.vertices 2))).card by
    change 0 < degreeIn G (p.vertices 2) s
    omega)
  obtain ⟨hu, hbu⟩ := mem_filter.mp hu
  obtain ⟨a, ha, has, hT⟩ := full_dense_from_noncentral hc hcard hdeg hn p hp hs hfull hr
    u hu (Or.inl hbu.symm)
  obtain ⟨hclA, _, _⟩ := dense_core_bounds hc hcard hn p hp hs (by omega) ha has hT
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  obtain ⟨d, hd, hcenter, hprimary, hsecondary⟩ := dense_pair_labels p hclA hFA hT
  have hclS := FullRow.full_leaf_clique hc p hp hs hfull
  obtain ⟨z, hz, hbz⟩ : ∃ z ∈ s, ¬G.Adj (p.vertices 2) z := by
    by_contra! hall
    have hh := (degreeIn_eq_card_iff (p.vertices 2) s).mpr hall
    rw [hb, hclS.card_eq] at hh
    omega
  have hbout : p.vertices 2 ∉ s := fun hh ↦
    disjoint_left.mp ((c.presentPaw p hp).triangle_disjoint_block hs)
      (show p.vertices 2 ∈ p.triangle by simp [Paw.triangle]) hh
  have hrepb : QuadOn G (insert (p.vertices 2) (s.erase z)) := by
    apply (clique_replace_iff_two_contacts hclS hbout hz).mpr
    have hh := degreeIn_erase_add G (p.vertices 2) z hz
    rw [if_neg hbz, hb] at hh
    omega
  have hpair : WeightedTwelve.DensePair p d := by
    have hdis : Disjoint p.support d.support := by rwa [hd]
    refine ⟨hdis, ?_, ?_, hcenter 2 (by decide), hcenter 3 (by decide), ?_⟩
    · rwa [hd]
    · rwa [hd]
    · rw [JointFinal.primary_support_eq p d hdis]
      exact hprimary
  have hxrep := FullRow.full_leaf_replacement hc p hp hs hfull z hz
  have h : DenseObstruction.PairConfig c p d s z :=
    ⟨hp, hs, by rwa [hd], by rwa [hd], hz, hpair, hxrep.1, hxrep.2, hrepb⟩
  have hrev := h.reverse (hcenter 1 (by decide)) hsecondary
  have hfirst := full_pair_inside hc hcard hn h hfull hb
  have hlast := full_pair_inside hc hcard hn hrev hfull hb
  rw [d.reverse_support] at hlast
  exact h.false_of_two_inside_bounds hc hcard hdeg hn (hcenter 1 (by decide)) hsecondary
    hfirst hlast

theorem full_second_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) : degreeIn G (p.vertices 2) s ≤ 1 := by
  by_contra hh
  exact full_two_false hc hcard hdeg hn p hp hs hfull (by omega)

theorem full_noncentral_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) :
    degreeIn G (p.vertices 2) s ≤ 1 ∧ degreeIn G (p.vertices 3) s ≤ 1 := by
  have h2 := full_second_le_one hc hcard hdeg hn p hp hs hfull
  have h3 := full_second_le_one hc hcard hdeg hn p.swapNoncentral
    (by rw [Paw.swapNoncentral_support, hp]) hs
    (by simpa only [Paw.swapNoncentral_leaf] using hfull)
  rw [Paw.swapNoncentral_apply, Equiv.swap_apply_left] at h3
  exact ⟨h2, h3⟩

end Erdos577.LargeLeaf

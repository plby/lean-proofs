import ErdosProblems.Erdos577.WeightedTwelveLastRow

/-! Claim2.4 and the proved insertion prohibitions leave only a small leaf row. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma ten_eleven_false (p : Paw G) (q : Quadrilateral G)
    (hb : degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support ≤ 6)
    (h : WeightedPawBlock.Pattern10 p q ∨ WeightedPawBlock.Pattern11 p q) : False := by
  have h7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h14 : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h15 : (∑ j : Fin 4, ((15 : ℕ).testBit j.val).toNat) = 4 := by decide +kernel
  rcases h with h | h
  · have hx := h.2.2.1.degree p q 0 15
    have hy := q.degree_ge_mask (p.vertices 2) 14 h.2.2.2.2
    rw [h15] at hx
    rw [h14] at hy
    change degreeIn G p.leaf q.support = 4 at hx
    omega
  · have hx := h.2.1.degree p q 0 7
    have hy := h.2.2.1.degree p q 2 15
    rw [h7] at hx
    rw [h15] at hy
    change degreeIn G p.leaf q.support = 3 at hx
    omega

variable [Fintype V]

theorem small_leaf_of_prohibited {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {j : Finset V} (hj : j ∈ c.blocks)
    (z : V) (hz : z ∉ j) (hzsmall : degreeIn G z j ≤ 2)
    (hno2 : ¬CommonReplacement G p.leaf (p.vertices 2) z j)
    (hno3 : ¬CommonReplacement G p.leaf (p.vertices 3) z j)
    (hheavy : 9 ≤ degreeIn G p.leaf j + degreeIn G (p.vertices 2) j +
      degreeIn G (p.vertices 3) j + degreeIn G z j) : degreeIn G p.leaf j ≤ 2 := by
  by_contra hlarge
  have hhigh : 7 ≤ degreeIn G p.leaf j + degreeIn G (p.vertices 2) j +
      degreeIn G (p.vertices 3) j := by omega
  obtain ⟨swap, v, hv, hpat⟩ := JointClaims.large_weighted_patterns hc hcard hdeg hn
    p hp hj (by omega) hhigh
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
  have hbound := (hc.claim_two_four hcard hdeg hn p' hp' hj).1
  rw [← hv] at hbound
  rcases hpat with h10 | h11 | h12
  · exact ten_eleven_false p' v hbound (Or.inl h10)
  · exact ten_eleven_false p' v hbound (Or.inr h11)
  · have hheavy' : 9 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
        degreeIn G (p'.vertices 3) v.support + degreeIn G z v.support := by
      rw [hv]
      cases swap
      · exact hheavy
      · change 9 ≤ degreeIn G p.leaf j + degreeIn G (p.vertices 3) j +
          degreeIn G (p.vertices 2) j + degreeIn G z j
        omega
    obtain ⟨hx, hb, ht⟩ := counts p' v h12
    have hz2 : 2 ≤ degreeIn G z v.support := by omega
    have hcommon := h12.common_replacement p' v z (by rwa [hv]) hz2
    rw [hv] at hcommon
    cases swap
    · exact hno2 hcommon
    · exact hno3 hcommon

theorem Configuration.leaf_degree_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (hnine : 9 ≤ contacts G (JointFinal.arms p q d) j) : degreeIn G p.leaf j ≤ 2 := by
  obtain ⟨e, he, _, _, hp', _, _, _, hkeep⟩ :=
    h.pair.exists_pair_chain hc hcard hn p h.paw d h.core
  obtain ⟨_, hx1, hx2, _, _, _⟩ := JointCore.four_distinct h.arms_card
  have hno1 := h.no_exposed_common hc hcard hn hj hjq hjd
    (u := p.leaf) (v := d 2) (by simp [JointFinal.spokes]) (by simp [JointFinal.spokes]) hx1
  have hno2 := h.no_exposed_common hc hcard hn hj hjq hjd
    (u := p.leaf) (v := d 3) (by simp [JointFinal.spokes]) (by simp [JointFinal.spokes]) hx2
  have hyout : q 3 ∉ j := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint h.first hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hysmall := h.last_degree_le_two hc hcard hn hj hjq hjd hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  exact small_leaf_of_prohibited he.toFeasible hcard hdeg hn h.pair.pairPaw hp'
    (hkeep j hj hjd) (q 3) hyout hysmall hno1 hno2 (by
      change 9 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j +
        degreeIn G (q 3) j
      omega)

end Erdos577.WeightedTwelve

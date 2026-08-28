import ErdosProblems.Erdos577.JointLeafCounts
import ErdosProblems.Erdos577.WeightedPawFinalClassification
import ErdosProblems.Erdos577.WeightedThirteenExcluded
import ErdosProblems.Erdos577.WeightedFourteenExcluded

/-! The weighted classification identifies the original third vertex as the universal high row. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma good_weighted_counts (p : Paw G) (q : Quadrilateral G)
    (h : WeightedPawBlock.Pattern10 p q ∨ WeightedPawBlock.Pattern11 p q ∨
      WeightedPawBlock.Pattern12 p q) :
    3 ≤ degreeIn G p.leaf q.support ∧ 3 ≤ degreeIn G (p.vertices 2) q.support ∧
      degreeIn G p.leaf q.support + degreeIn G (p.vertices 3) q.support ≤ 4 := by
  have h0 : (∑ j : Fin 4, ((0 : ℕ).testBit j.val).toNat) = 0 := by decide +kernel
  have h7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h8 : (∑ j : Fin 4, ((8 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  have h14 : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h15 : (∑ j : Fin 4, ((15 : ℕ).testBit j.val).toNat) = 4 := by decide +kernel
  rcases h with h | h | h
  · have hx := WeightedPawBlock.Row.degree p q 0 15 h.2.2.1
    have hl := WeightedPawBlock.Row.degree p q 3 0 h.2.2.2.1
    have hh := q.degree_ge_mask (p.vertices 2) 14 h.2.2.2.2
    rw [h15] at hx
    rw [h0] at hl
    rw [h14] at hh
    change degreeIn G p.leaf q.support = 4 at hx
    exact ⟨by omega, hh, by omega⟩
  · have hx := WeightedPawBlock.Row.degree p q 0 7 h.2.1
    have hh := WeightedPawBlock.Row.degree p q 2 15 h.2.2.1
    have hl := WeightedPawBlock.Row.degree p q 3 0 h.2.2.2
    rw [h7] at hx
    rw [h15] at hh
    rw [h0] at hl
    change degreeIn G p.leaf q.support = 3 at hx
    exact ⟨by omega, by omega, by omega⟩
  · have hx := WeightedPawBlock.Row.degree p q 0 7 h.2.1
    have hh := WeightedPawBlock.Row.degree p q 2 7 h.2.2.1
    have hl := WeightedPawBlock.Row.degree p q 3 8 h.2.2.2
    rw [h7] at hx hh
    rw [h8] at hl
    change degreeIn G p.leaf q.support = 3 at hx
    exact ⟨by omega, by omega, by omega⟩

variable [Fintype V]

theorem weighted_third_pair {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hheavy : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a)
    (hpair : 5 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 3) a) :
    3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G (p.vertices 3) a ∧
      (∀ u ∈ a, QuadOn G (insert (p.vertices 3) (a.erase u))) ∧
      ∀ z, z ∉ p.support ∪ a → 2 ≤ degreeIn G z a →
        CommonReplacement G p.leaf (p.vertices 3) z a := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  have hbound := degreeIn_le_card G (p.vertices 3) a
  have hacard : a.card = 4 := hq ▸ q.card_support
  rw [hacard] at hbound
  have hx : 0 < degreeIn G p.leaf a := by omega
  obtain ⟨swap, v, hv, hpat⟩ := hc.weighted_paw_classification hcard hdeg hn p hp ha q hq
    (by rw [hq]; exact hheavy) (by rw [hq]; exact hx)
  have hva : v.support = a := hv.trans hq
  have hp' : (FirstPaw.normalizedPaw p swap).support = c.remainder := by
    rw [FirstPaw.normalizedPaw_support, hp]
  have conclude
      (hg : WeightedPawBlock.Pattern10 (FirstPaw.normalizedPaw p swap) v ∨
        WeightedPawBlock.Pattern11 (FirstPaw.normalizedPaw p swap) v ∨
        WeightedPawBlock.Pattern12 (FirstPaw.normalizedPaw p swap) v)
      (hr : WeightedPawBlock.ReplacementClauses (FirstPaw.normalizedPaw p swap) v) :
      3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G (p.vertices 3) a ∧
        (∀ u ∈ a, QuadOn G (insert (p.vertices 3) (a.erase u))) ∧
        ∀ z, z ∉ p.support ∪ a → 2 ≤ degreeIn G z a →
          CommonReplacement G p.leaf (p.vertices 3) z a := by
    obtain ⟨hx3, hh3, hlow⟩ := good_weighted_counts (FirstPaw.normalizedPaw p swap) v hg
    have hs : swap = true := by
      cases swap
      · change degreeIn G p.leaf v.support + degreeIn G (p.vertices 3) v.support ≤ 4 at hlow
        rw [hva] at hlow
        omega
      · rfl
    subst swap
    change 3 ≤ degreeIn G p.leaf v.support at hx3
    change 3 ≤ degreeIn G (p.vertices 3) v.support at hh3
    rw [hva] at hx3 hh3
    refine ⟨hx3, hh3, ?_, ?_⟩
    · intro u hu
      have hh := hr.1 u (hva.symm ▸ hu)
      change QuadOn G (insert (p.vertices 3) (v.support.erase u)) at hh
      rwa [hva] at hh
    · intro z hz hzdegree
      have hz' : z ∉ (FirstPaw.normalizedPaw p true).support ∪ v.support := by
        rw [FirstPaw.normalizedPaw_support, hva]
        exact hz
      have hh := (hr.2 z hz' (by rw [hva]; exact hzdegree)).1
      change CommonReplacement G p.leaf (p.vertices 3) z v.support at hh
      rwa [hva] at hh
  rcases hpat with h9 | ⟨h10, hr⟩ | ⟨h11, hr⟩ | ⟨h12, hr⟩ | h13 | h14
  · have h14 : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
    have htwo := WeightedPawBlock.Row.degree (FirstPaw.normalizedPaw p swap) v 2 14 h9.2.1
    have hthree := WeightedPawBlock.Row.degree (FirstPaw.normalizedPaw p swap) v 3 14 h9.2.2
    rw [h14] at htwo hthree
    have hthird : degreeIn G (p.vertices 3) v.support = 3 := by
      cases swap
      · exact hthree
      · exact htwo
    have hleaf := h9.1
    change degreeIn G (FirstPaw.normalizedPaw p swap).leaf v.support = 1 at hleaf
    rw [FirstPaw.normalizedPaw_leaf, hva] at hleaf
    rw [hva] at hthird
    omega
  · exact conclude (Or.inl h10) hr
  · exact conclude (Or.inr (Or.inl h11)) hr
  · exact conclude (Or.inr (Or.inr h12)) hr
  · exact False.elim (hc.not_weighted_pattern13 hcard hdeg hn _ hp' ha v hva h13)
  · exact False.elim (hc.not_weighted_pattern14 hcard hdeg hn _ hp' ha v hva h14)

end Erdos577.JointClaims

import ErdosProblems.Erdos577.SmallLeafClassification
import ErdosProblems.Erdos577.PathColumnCount

/-! A small noncentral row in the weighted classification gives a common triple
for the other two rows, and a doubled-small-row bound of eight. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.small_noncentral_common_three {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hsmall : degreeIn G (p.vertices 2) q.support ≤ 2)
    (hpos : 0 < degreeIn G p.leaf q.support)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) :
    3 ≤ ((q.support.filter (G.Adj p.leaf)) ∩
      (q.support.filter (G.Adj (p.vertices 3)))).card ∧
    2 * degreeIn G (p.vertices 2) q.support + degreeIn G p.leaf q.support +
      degreeIn G (p.vertices 3) q.support ≤ 8 := by
  obtain ⟨swap, q', hq', hpatt⟩ := hc.weighted_paw_classification hcard hdeg hn
    p hp hb q hq hheavy hpos
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
  have hrow (i : Fin 4) (mask n : ℕ) (hr : WeightedPawBlock.Row p' q' i mask)
      (he : (∑ j : Fin 4, (mask.testBit j.val).toNat) = n) :
      degreeIn G (p'.vertices i) q'.support = n := (hr.degree p' q' i mask).trans he
  have hsolve (hbig : 3 ≤ degreeIn G (p'.vertices 2) q'.support)
      (hcommon : 3 ≤ ((q'.support.filter (G.Adj p'.leaf)) ∩
        (q'.support.filter (G.Adj (p'.vertices 2)))).card)
      (hbound : 2 * degreeIn G (p'.vertices 3) q'.support + degreeIn G p'.leaf q'.support +
        degreeIn G (p'.vertices 2) q'.support ≤ 8) :
      3 ≤ ((q.support.filter (G.Adj p.leaf)) ∩
        (q.support.filter (G.Adj (p.vertices 3)))).card ∧
      2 * degreeIn G (p.vertices 2) q.support + degreeIn G p.leaf q.support +
        degreeIn G (p.vertices 3) q.support ≤ 8 := by
    cases swap
    · change 3 ≤ degreeIn G (p.vertices 2) q'.support at hbig
      rw [hq'] at hbig
      omega
    · change 3 ≤ ((q'.support.filter (G.Adj p.leaf)) ∩
        (q'.support.filter (G.Adj (p.vertices 3)))).card at hcommon
      change 2 * degreeIn G (p.vertices 2) q'.support + degreeIn G p.leaf q'.support +
        degreeIn G (p.vertices 3) q'.support ≤ 8 at hbound
      rw [hq'] at hcommon hbound
      exact ⟨hcommon, hbound⟩
  rcases hpatt with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | h
  · have hb3 := hrow 2 14 3 h.2.1 (by decide +kernel)
    have hc3 := hrow 3 14 3 h.2.2 (by decide +kernel)
    cases swap
    · change degreeIn G (p.vertices 2) q'.support = 3 at hb3
      rw [hq'] at hb3
      omega
    · change degreeIn G (p.vertices 2) q'.support = 3 at hc3
      rw [hq'] at hc3
      omega
  · have hl4 := hrow 0 15 4 h.2.2.1 (by decide +kernel)
    have hs0 := hrow 3 0 0 h.2.2.2.1 (by decide +kernel)
    have hb3 : 3 ≤ degreeIn G (p'.vertices 2) q'.support := by
      have hh := q'.degree_ge_mask (p'.vertices 2) 14 h.2.2.2.2
      have he : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rwa [he] at hh
    have hb4 := degreeIn_le_card G (p'.vertices 2) q'.support
    rw [q'.card_support] at hb4
    apply hsolve hb3
    · apply common_intersection_three q'.support _ _ (filter_subset _ _) (filter_subset _ _)
        q'.card_support
      change 7 ≤ degreeIn G p'.leaf q'.support + degreeIn G (p'.vertices 2) q'.support
      change degreeIn G p'.leaf q'.support = 4 at hl4
      omega
    · change degreeIn G p'.leaf q'.support = 4 at hl4
      omega
  · have hl3 := hrow 0 7 3 h.2.1 (by decide +kernel)
    have hb4 := hrow 2 15 4 h.2.2.1 (by decide +kernel)
    have hs0 := hrow 3 0 0 h.2.2.2 (by decide +kernel)
    change degreeIn G p'.leaf q'.support = 3 at hl3
    apply hsolve (by omega)
    · apply common_intersection_three q'.support _ _ (filter_subset _ _) (filter_subset _ _)
        q'.card_support
      change 7 ≤ degreeIn G p'.leaf q'.support + degreeIn G (p'.vertices 2) q'.support
      omega
    · omega
  · have hl3 := hrow 0 7 3 h.2.1 (by decide +kernel)
    have hb3 := hrow 2 7 3 h.2.2.1 (by decide +kernel)
    have hs1 := hrow 3 8 1 h.2.2.2 (by decide +kernel)
    change degreeIn G p'.leaf q'.support = 3 at hl3
    have he : q'.support.filter (G.Adj p'.leaf) =
        q'.support.filter (G.Adj (p'.vertices 2)) := by
      apply filter_congr
      intro u hu
      obtain ⟨j, rfl⟩ := (q'.mem_support u).mp hu
      exact (h.2.1 j).trans (h.2.2.1 j).symm
    apply hsolve (by omega)
    · rw [he, inter_self]
      change 3 ≤ degreeIn G (p'.vertices 2) q'.support
      omega
    · omega
  · exact False.elim (hc.not_weighted_pattern13 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)
  · exact False.elim (hc.not_weighted_pattern14 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)

end Erdos577

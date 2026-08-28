import ErdosProblems.Erdos577.WeightedFourteenExcluded

/-! A paw leaf of degree at most two has doubled weighted total at most eight, after (14). -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.small_leaf_weight_le_eight {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hsmall : degreeIn G p.leaf q.support ≤ 2) :
    2 * degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support ≤ 8 := by
  have hb4 := degreeIn_le_card G (p.vertices 2) q.support
  have hc4 := degreeIn_le_card G (p.vertices 3) q.support
  rw [q.card_support] at hb4 hc4
  by_cases hz : degreeIn G p.leaf q.support = 0
  · omega
  by_cases hh : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support
  · obtain ⟨swap, q', hq', hpatt⟩ := hc.weighted_paw_classification hcard hdeg hn
      p hp hb q hq hh (by omega)
    let p' := FirstPaw.normalizedPaw p swap
    have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
    have hl : degreeIn G (p'.vertices 0) q'.support = degreeIn G p.leaf q.support := by
      rw [hq']
      cases swap <;> rfl
    have hbc : degreeIn G (p'.vertices 2) q'.support + degreeIn G (p'.vertices 3) q'.support =
        degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support := by
      rw [hq']
      cases swap
      · rfl
      · exact Nat.add_comm _ _
    have hrow (i : Fin 4) (mask : ℕ) (hr : WeightedPawBlock.Row p' q' i mask) :=
      hr.degree p' q' i mask
    rcases hpatt with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | h
    · have hb' := hrow 2 14 h.2.1
      have hc' := hrow 3 14 h.2.2
      have hl' := h.1
      change degreeIn G (p'.vertices 0) q'.support = 1 at hl'
      have he : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [he] at hb' hc'
      omega
    · have hl' := hrow 0 15 h.2.2.1
      have he : (∑ j : Fin 4, ((15 : ℕ).testBit j.val).toNat) = 4 := by decide +kernel
      rw [he] at hl'
      omega
    · have hl' := hrow 0 7 h.2.1
      have he : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [he] at hl'
      omega
    · have hl' := hrow 0 7 h.2.1
      have he : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [he] at hl'
      omega
    · have hl' := hrow 0 1 h.2.1
      have hb' := hrow 2 13 h.2.2.1
      have hc' := hrow 3 7 h.2.2.2
      have he1 : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
      have he13 : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      have he7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [he1] at hl'
      rw [he13] at hb'
      rw [he7] at hc'
      omega
    · exact False.elim (hc.not_weighted_pattern14 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)
  · omega

end Erdos577

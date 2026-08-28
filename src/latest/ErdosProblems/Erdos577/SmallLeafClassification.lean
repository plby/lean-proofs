import ErdosProblems.Erdos577.WeightedThirteenExcluded

/-! After excluding (13) and (14), a positive small heavy leaf row has exactly pattern (9). -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.small_leaf_pattern_nine {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hsmall : degreeIn G p.leaf q.support ≤ 2) (hpos : 0 < degreeIn G p.leaf q.support)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) :
    ∃ q' : Quadrilateral G, q'.support = q.support ∧ WeightedPawBlock.Pattern9 p q' := by
  obtain ⟨swap, q', hq', hpatt⟩ := hc.weighted_paw_classification hcard hdeg hn
    p hp hb q hq hheavy hpos
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
  have hl : degreeIn G (p'.vertices 0) q'.support = degreeIn G p.leaf q.support := by
    rw [hq']
    cases swap <;> rfl
  have hrow (mask : ℕ) (hr : WeightedPawBlock.Row p' q' 0 mask) := hr.degree p' q' 0 mask
  rcases hpatt with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | h
  · refine ⟨q', hq', ?_⟩
    cases swap
    · exact h
    · exact ⟨h.1, h.2.2, h.2.1⟩
  · have hleaf := hrow 15 h.2.2.1
    have he : (∑ j : Fin 4, ((15 : ℕ).testBit j.val).toNat) = 4 := by decide +kernel
    rw [he] at hleaf
    omega
  · have hleaf := hrow 7 h.2.1
    have he : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
    rw [he] at hleaf
    omega
  · have hleaf := hrow 7 h.2.1
    have he : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
    rw [he] at hleaf
    omega
  · exact False.elim (hc.not_weighted_pattern13 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)
  · exact False.elim (hc.not_weighted_pattern14 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)

theorem TriangleChain.Feasible.small_leaf_precise {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hsmall : degreeIn G p.leaf q.support ≤ 2) (hpos : 0 < degreeIn G p.leaf q.support)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) :
    degreeIn G p.leaf q.support = 1 ∧ ∃ s : Finset V, s ⊆ q.support ∧ s.card = 3 ∧
      q.support.filter (G.Adj (p.vertices 2)) = s ∧
      q.support.filter (G.Adj (p.vertices 3)) = s := by
  obtain ⟨q', hq', h⟩ := hc.small_leaf_pattern_nine hcard hdeg hn p hp hb q hq hsmall hpos hheavy
  have hleaf : degreeIn G p.leaf q.support = 1 := by rw [← hq']; exact h.1
  have hthree : degreeIn G (p.vertices 2) q.support = 3 := by
    rw [← hq', h.2.1.degree p q' 2 14]
    decide +kernel
  refine ⟨hleaf, q.support.filter (G.Adj (p.vertices 2)), filter_subset _ _, hthree, rfl, ?_⟩
  ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨hu, he⟩
    refine ⟨hu, ?_⟩
    obtain ⟨j, rfl⟩ := (q'.mem_support u).mp (hq'.symm ▸ hu)
    exact (h.2.1 j).mpr ((h.2.2 j).mp he)
  · rintro ⟨hu, he⟩
    refine ⟨hu, ?_⟩
    obtain ⟨j, rfl⟩ := (q'.mem_support u).mp (hq'.symm ▸ hu)
    exact (h.2.2 j).mpr ((h.2.1 j).mp he)

end Erdos577

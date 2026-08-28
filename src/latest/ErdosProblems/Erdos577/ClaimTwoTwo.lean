import ErdosProblems.Erdos577.FirstPawEightExcluded

/-! Wang's Claim2.2, with the original noncentral paw labels restored by cycle reflection. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma PawBlock.Pattern3.unswap_reverse (p : Paw G) (q : Quadrilateral G)
    (h : PawBlock.Pattern3 p.swapNoncentral q) : PawBlock.Pattern3 p q.reverse := by
  refine ⟨⟨h.1.1, fun hh ↦ h.1.2 hh.symm⟩, ?_⟩
  have hbits : ∀ i j : Fin 4,
      ((![1, 15, 9, 3] : Fin 4 → ℕ) (Equiv.swap 2 3 i)).testBit (-j).val =
        ((![1, 15, 9, 3] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  have hp (i : Fin 4) : p.swapNoncentral.vertices (Equiv.swap 2 3 i) = p.vertices i := by
    fin_cases i <;> rfl
  intro i j
  have hh := h.2 (Equiv.swap 2 3 i) (-j)
  rw [hp, hbits] at hh
  exact hh

omit [DecidableRel G.Adj] in
lemma PawBlock.Pattern3.unnormalize (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (h : PawBlock.Pattern3 (FirstPaw.normalizedPaw p swap) q) :
    ∃ v : Quadrilateral G, v.support = q.support ∧ PawBlock.Pattern3 p v := by
  cases swap
  · exact ⟨q, rfl, h⟩
  · exact ⟨q.reverse, q.reverse_support, PawBlock.Pattern3.unswap_reverse p q h⟩

variable [Fintype V]

theorem TriangleChain.Feasible.claim_two_two {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    degreeIn G p.leaf q.support = 0 ∨
      ∃ v : Quadrilateral G, v.support = q.support ∧ PawBlock.Pattern3 p v := by
  by_cases hz : degreeIn G p.leaf q.support = 0
  · exact Or.inl hz
  · obtain ⟨_, _, _, swap, v, hv, hpat⟩ :=
      hc.first_paw_final hcard hdeg hn p hp hb q hq hheavy (by omega)
    rcases hpat with h3 | h8
    · obtain ⟨w, hw, h3'⟩ := h3.unnormalize p v swap
      exact Or.inr ⟨w, hw.trans hv, h3'⟩
    · exact False.elim (hc.not_first_paw_pattern8 hcard hdeg hn
        (FirstPaw.normalizedPaw p swap) (by rw [FirstPaw.normalizedPaw_support, hp])
        hb v (hv.trans hq) h8)

end Erdos577

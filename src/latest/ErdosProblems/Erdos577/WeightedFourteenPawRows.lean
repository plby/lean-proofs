import ErdosProblems.Erdos577.WeightedFourteenFourRows
import ErdosProblems.Erdos577.WeightedFourteenSixExcluded

/-! The two exact nine-contact paw matrices at the heavy block of pattern (14). -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem paw_rows_at_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    contacts G p.support a = 9 ∧ ∃ v : Quadrilateral G, v.support = a ∧
      PawBlock.OnlyFirst v ∧ (PawBlock.ExactRows p v ![5, 13, 5, 5] ∨
        ∃ swap : Bool, PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![5, 5, 13, 5]) := by
  obtain ⟨hx2, hy2, _, _, hE, _⟩ := heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  obtain ⟨swap, v, hv, hcase⟩ := four_or_five_at_heavy hc hcard hdeg hn p hp hb q hq hd h
    ha hab hheavy
  rcases hcase with h4 | h5
  · obtain ⟨htotal, w, hw, hdw, hrows⟩ := four_rows hc hcard hn p hp hb q hq hd h ha hab
      v hv swap h4 hx2 hy2 hE
    exact ⟨htotal, w, hw, hdw, Or.inl hrows⟩
  · have hcenter := h5.center_le_two (FirstPaw.normalizedPaw p swap) v
    rw [FirstPaw.normalizedPaw_center] at hcenter
    obtain ⟨htotal, _, swap', w, hws, hnon, hrows⟩ := hc.paw_leaf_two_center_le_two
      hcard hdeg hn p hp ha v hv (by rw [hv]; exact hE) (by rw [hv]; exact hx2) hcenter
    have hscore : edgeCount G v.support = 5 := by
      rw [v.edgeCount_eq, if_pos h5.1.1, if_neg h5.1.2]
    have hdiag : G.Adj (w 0) (w 2) := by
      have he := w.edgeCount_eq
      rw [hws, hscore, if_neg hnon] at he
      by_contra hh
      rw [if_neg hh] at he
      omega
    rw [hv] at htotal
    exact ⟨htotal, w, hws.trans hv, ⟨hdiag, hnon⟩, Or.inr ⟨swap', hrows⟩⟩

end Erdos577.WeightedFourteen

import ErdosProblems.Erdos577.WeightedFourteenSixRows
import ErdosProblems.Erdos577.WeightedFourteenPreparation
import ErdosProblems.Erdos577.WeightedFourteenAlternatePaw
import ErdosProblems.Erdos577.PawCenterTwo
import ErdosProblems.Erdos577.FirstPawRowBounds
import ErdosProblems.Erdos577.DiamondLabels

/-! The alternate paw forces the missing contact at the fourth vertex of a case-(6) block. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_alternate_contact {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h6 : PawBlock.Pattern6 (FirstPaw.normalizedPaw p swap) v) :
    swap = false ∧ G.Adj (q 3) (v 3) := by
  obtain ⟨hx2, hy2, _, _, hE, hE', htotalrow⟩ :=
    heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  obtain ⟨_, _, htotal, hrows⟩ := six_rows hc hcard hn p hp hb q hq hd h ha hab
    v hv swap h6 hx2 hy2 hE
  have hw2 := htotalrow htotal
  let z := FirstPaw.normalizedPaw p swap
  have hr3 := WeightedPawBlock.Row.degree z v 1 13 (hrows 1)
  have hb3 := WeightedPawBlock.Row.degree z v 2 7 (hrows 2)
  have hc1 := WeightedPawBlock.Row.degree z v 3 1 (hrows 3)
  have hm13 : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have hm7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have hm1 : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  rw [hm13] at hr3
  rw [hm7, hv] at hb3
  rw [hm1, hv] at hc1
  change degreeIn G z.center v.support = 3 at hr3
  rw [FirstPaw.normalizedPaw_center, hv] at hr3
  change degreeIn G (p.vertices 1) a = 3 at hr3
  have hb31 : degreeIn G (p.vertices 2) a = 3 ∨ degreeIn G (p.vertices 2) a = 1 := by
    cases swap
    · exact Or.inl hb3
    · exact Or.inr hc1
  let alt := alternatePaw p q hd h
  obtain ⟨d, hdS, _, _, hpalt, hkeep⟩ := exists_alternate_strong_chain hc hcard hn
    p hp hb q hq hd h
  have ha' := hkeep a ha hab
  have hEalt : 9 ≤ contacts G alt.support v.support := by
    rw [alternatePaw_contacts, hv]
    exact hE'
  have hxalt : degreeIn G alt.leaf v.support = 2 := by
    change degreeIn G (q 3) v.support = 2
    rw [hv]
    exact hw2
  have hclass := hdS.toFeasible.first_paw_classification hcard hdeg hn alt hpalt ha' v hv
    hEalt (by omega)
  obtain ⟨aswap, w, hws, hpattern⟩ := hclass.leaf_two alt v hxalt
  have hwa : w.support = a := hws.trans hv
  have hnewhp : (FirstPaw.normalizedPaw alt aswap).support = d.remainder := by
    rw [FirstPaw.normalizedPaw_support]
    exact hpalt
  have hnewE : 9 ≤ contacts G (FirstPaw.normalizedPaw alt aswap).support w.support := by
    rw [FirstPaw.normalizedPaw_support, hws]
    exact hEalt
  have hnewx : degreeIn G (FirstPaw.normalizedPaw alt aswap).leaf w.support = 2 := by
    rw [FirstPaw.normalizedPaw_leaf, hws]
    exact hxalt
  rcases hpattern with h4 | h5 | h6'
  · have hh := (h4.normalized_noncentral_bounds alt w aswap).1
    change degreeIn G (p.vertices 1) w.support ≤ 2 at hh
    rw [hwa] at hh
    omega
  · have hh := (hdS.toFeasible.first_pattern5_exact hcard hdeg hn
      (FirstPaw.normalizedPaw alt aswap) hnewhp ha' w hwa hnewE hnewx h5).2.1
    rw [FirstPaw.normalizedPaw_center, hwa] at hh
    change degreeIn G (p.vertices 2) a = 2 at hh
    omega
  · have hh := h6'.center_ge_three (FirstPaw.normalizedPaw alt aswap) w hnewE
    rw [FirstPaw.normalizedPaw_center, hwa] at hh
    change 3 ≤ degreeIn G (p.vertices 2) a at hh
    have hswap : swap = false := by
      cases swap
      · rfl
      · have hlow : degreeIn G (p.vertices 2) a = 1 := hc1
        omega
    subst swap
    have haswap : aswap = false := by
      cases aswap
      · rfl
      · have hl := h6'.last_bound (FirstPaw.normalizedPaw alt true) w
        change degreeIn G (p.vertices 1) w.support ≤ 1 at hl
        rw [hwa] at hl
        omega
    subst aswap
    have h6alt : PawBlock.Pattern6 alt w := h6'
    have hmissing : ¬G.Adj (p.vertices 1) (w 3) := by
      intro he
      exact h6alt.2.2.1 3 he rfl
    have hthird : w 3 = v 1 := v.missing_column_thirteen (p.vertices 1) (hrows 1)
      (w 3) (hws ▸ (w.mem_support _).mpr ⟨3, rfl⟩) hmissing
    have hsecond := v.low_label_swap w hws h6.1.1 h6alt.1.2 hthird
    have hleaf := (h6alt.leaf_exact alt w hnewx 1).mpr (by decide)
    change G.Adj (q 3) (w 1) at hleaf
    rw [hsecond] at hleaf
    exact ⟨rfl, hleaf⟩

end Erdos577.WeightedFourteen

import ErdosProblems.Erdos577.WeightedThirteenAdjacentFactor
import ErdosProblems.Erdos577.WeightedThirteenLeafLower
import ErdosProblems.Erdos577.TwoContactLabels
import ErdosProblems.Erdos577.TwoNeighborReplacements
import ErdosProblems.Erdos577.UniversalDiagonal

/-! The last, two-neighbor leaf case of pattern (13) yields an explicit four-cycle factor. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem final_leaf_two_false {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hheavy : 13 ≤ denseWeight p q v t)
    (hleaf : degreeIn G p.leaf t = 2) (hsmall : degreeIn G (q 3) t ≤ 2)
    (hlarge : 3 ≤ degreeIn G (q 1) t)
    (hrep : ∀ u ∈ t, QuadOn G (insert (q 1) (t.erase u)))
    (hxv1 : ∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 1) u))
    (hxv2 : ∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 2) u))
    (hseven : 7 ≤ 2 * degreeIn G p.leaf t + degreeIn G (v 1) t + degreeIn G (v 2) t) : False := by
  have htq := c.property.blocks_quad t ht
  have hno : ¬CommonReplacement G (v 1) (v 2) p.leaf t :=
    no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 0
  obtain ⟨w₀, hw₀⟩ := htq
  obtain ⟨w, hww, hrow⟩ := w₀.exists_two_contact_labels p.leaf (by rw [hw₀]; exact hleaf)
  have hw : w.support = t := hww.trans hw₀
  have hdt : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support := by
    rw [hw]
    exact dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have hxout : p.leaf ∉ w.support := fun hh ↦ disjoint_left.mp hdt
    (mem_union_left _ (mem_union_left _ (p.support_eq ▸ mem_insert_self _ _))) hh
  have hqout : q 1 ∉ w.support := fun hh ↦ disjoint_left.mp hdt
    (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨1, rfl⟩))) hh
  have hdis1 : ∀ u ∈ w.support, ¬(G.Adj p.leaf u ∧ G.Adj (v 1) u) := by rw [hw]; exact hxv1
  have hdis2 : ∀ u ∈ w.support, ¬(G.Adj p.leaf u ∧ G.Adj (v 2) u) := by rw [hw]; exact hxv2
  have hthree : 3 ≤ degreeIn G (v 1) w.support + degreeIn G (v 2) w.support := by
    rw [hw]
    omega
  rcases hrow with hrow | hrow
  · have hx0 := (hrow 0).mpr (by decide)
    have hx1 := (hrow 1).mpr (by decide)
    have hmiss1 : ¬G.Adj (v 1) (w 0) ∧ ¬G.Adj (v 1) (w 1) :=
      ⟨fun he ↦ hdis1 _ ((w.mem_support _).mpr ⟨0, rfl⟩) ⟨hx0, he⟩,
        fun he ↦ hdis1 _ ((w.mem_support _).mpr ⟨1, rfl⟩) ⟨hx1, he⟩⟩
    have hmiss2 : ¬G.Adj (v 2) (w 0) ∧ ¬G.Adj (v 2) (w 1) :=
      ⟨fun he ↦ hdis2 _ ((w.mem_support _).mpr ⟨0, rfl⟩) ⟨hx0, he⟩,
        fun he ↦ hdis2 _ ((w.mem_support _).mpr ⟨1, rfl⟩) ⟨hx1, he⟩⟩
    have hnotboth : ¬(G.Adj (q 1) (w 0) ∧ G.Adj (q 1) (w 1)) := by
      intro hh
      have hf := adjacent_leaf_factor p q hd h v hdis hcl hrows w hdt hx0 hx1 hh.1 hh.2
        hmiss1 hmiss2 hthree
      rw [hw] at hf
      exact no_dense_factor hcard hn p hp hb q hq ha v hv ht hf
    have hzbound : degreeIn G (q 1) w.support ≤ 3 := by
      rcases not_and_or.mp hnotboth with hh | hh
      · exact w.degree_le_three_of_nonadjacent _ 0 hh
      · exact w.degree_le_three_of_nonadjacent _ 1 hh
    have hz3 : degreeIn G (q 1) w.support = 3 := by rw [hw] at hzbound ⊢; omega
    have hb1 := degree_pair_le_card p.leaf (v 1) t hxv1
    have hb2 := degree_pair_le_card p.leaf (v 2) t hxv2
    rw [hleaf, (c.property.blocks_quad t ht).card] at hb1 hb2
    have hz3t : degreeIn G (q 1) t = 3 := hw ▸ hz3
    have hfour : 4 ≤ degreeIn G (v 1) t + degreeIn G (v 2) t := by
      unfold denseWeight at hheavy
      omega
    have he1 : degreeIn G (v 1) w.support = 2 := by rw [hw]; omega
    have he2 : degreeIn G (v 2) w.support = 2 := by rw [hw]; omega
    have hrow1 : ∀ j : Fin 4, G.Adj (v 1) (w j) ↔ (12 : ℕ).testBit j.val = true := by
      apply w.row_saturated (v 1) 12
      · intro j hj
        fin_cases j
        · exact False.elim (hmiss1.1 hj)
        · exact False.elim (hmiss1.2 hj)
        · decide
        · decide
      · rw [he1]
        decide +kernel
    have hrow2 : ∀ j : Fin 4, G.Adj (v 2) (w j) ↔ (12 : ℕ).testBit j.val = true := by
      apply w.row_saturated (v 2) 12
      · intro j hj
        fin_cases j
        · exact False.elim (hmiss2.1 hj)
        · exact False.elim (hmiss2.2 hj)
        · decide
        · decide
      · rw [he2]
        decide +kernel
    have hdiag := w.diagonal_of_universal_three (q 1) hqout hz3 (by rw [hw]; exact hrep)
    obtain ⟨i, hi, hquad⟩ := w.adjacent_pair_replacement_of_diagonal p.leaf hxout hx0 hx1 hdiag
    have hcommon : CommonReplacement G (v 1) (v 2) p.leaf w.support := by
      refine ⟨w i, (w.mem_support _).mpr ⟨i, rfl⟩, ?_, ?_, hquad⟩
      · apply (hrow1 i).mpr
        rcases hi with rfl | rfl <;> decide
      · apply (hrow2 i).mpr
        rcases hi with rfl | rfl <;> decide
    rw [hw] at hcommon
    exact hno hcommon
  · have hcommon := w.opposite_pair_common p.leaf (v 1) (v 2) hxout hrow hdis1 hdis2 hthree
    rw [hw] at hcommon
    exact hno hcommon

end Erdos577.WeightedThirteen

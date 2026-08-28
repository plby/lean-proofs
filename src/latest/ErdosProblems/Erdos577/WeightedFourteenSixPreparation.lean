import ErdosProblems.Erdos577.WeightedFourteenColumnAvoidance
import ErdosProblems.Erdos577.WeightedFourteenFactors
import ErdosProblems.Erdos577.FirstPawSixColumns
import ErdosProblems.Erdos577.OddEraseTriangles

/-! The forbidden second contact and exact columns when pattern (14)'s heavy block has case (6). -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_second_column {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h6 : PawBlock.Pattern6 (FirstPaw.normalizedPaw p swap) v)
    (hx2 : degreeIn G p.leaf a = 2) (hy2 : degreeIn G (q 1) a = 2)
    (hE : 9 ≤ contacts G p.support a) :
    ¬G.Adj (q 1) (v 1) ∧ degreeIn G (v 1) p.triangle ≤ 1 := by
  let z := FirstPaw.normalizedPaw p swap
  have hz2 : degreeIn G z.leaf v.support = 2 := by
    rw [FirstPaw.normalizedPaw_leaf, hv]
    exact hx2
  have hzE : 9 ≤ contacts G z.support v.support := by
    rw [FirstPaw.normalizedPaw_support, hv]
    exact hE
  have hr3 := h6.center_ge_three z v hzE
  rw [FirstPaw.normalizedPaw_center] at hr3
  have hrout : p.center ∉ v.support := by
    intro hh
    have hmem : p.center ∈ c.remainder := by
      rw [← hp, p.support_eq]
      exact mem_insert_of_mem p.center_mem_triangle
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hv ▸ hh))).2 hmem
  have hrep := v.replace_odd_of_three h6.1.1 1 (Or.inl rfl) p.center hrout hr3
  rw [hv] at hrep
  have hxv := (h6.leaf_exact z v hz2 1).mpr (by decide)
  change G.Adj z.leaf (v 1) at hxv
  rw [FirstPaw.normalizedPaw_leaf] at hxv
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab 8
  change ¬CommonReplacement G p.leaf (q 1) p.center a at hno
  have hu : v 1 ∈ a := hv ▸ (v.mem_support _).mpr ⟨1, rfl⟩
  have hnon : ¬G.Adj (q 1) (v 1) := fun he ↦ hno ⟨v 1, hu, hxv, he, hrep⟩
  obtain ⟨d, _, hdx, _, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h 1
  change d.terminal = q 1 at hdx
  have hyout : q 1 ∉ v.support := by
    rw [← hdx, hv]
    exact d.terminal_not_mem_block (hkeep a ha hab)
  have hcount := degreeIn_erase_add G (q 1) (v 1) ((v.mem_support _).mpr ⟨1, rfl⟩)
  rw [if_neg hnon, hv, hy2] at hcount
  have hrep' := v.replace_odd_of_two h6.1.1 1 (Or.inl rfl) (q 1) hyout (by rw [hv]; omega)
  rw [hv] at hrep'
  exact ⟨hnon, replacement_triangle_degree_le_one hc hcard hn p hp hb q hq hd h 1
    ha hab (v 1) hu hrep'⟩

theorem six_columns_exact {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h6 : PawBlock.Pattern6 (FirstPaw.normalizedPaw p swap) v)
    (hx2 : degreeIn G p.leaf a = 2) (hy2 : degreeIn G (q 1) a = 2)
    (hE : 9 ≤ contacts G p.support a) :
    ¬G.Adj (q 1) (v 1) ∧ contacts G p.support a = 9 ∧
      (PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![3, 13, 7, 1] ∨
        PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![3, 15, 5, 1]) := by
  obtain ⟨hnon, hcolumn⟩ := six_second_column hc hcard hn p hp hb q hq hd h ha hab
    v hv swap h6 hx2 hy2 hE
  obtain ⟨htotal, hrows⟩ := h6.columns_exact (FirstPaw.normalizedPaw p swap) v
    (by rw [FirstPaw.normalizedPaw_leaf, hv]; exact hx2)
    (by rw [FirstPaw.normalizedPaw_support, hv]; exact hE)
    (by rw [FirstPaw.normalizedPaw_triangle]; exact hcolumn)
  rw [FirstPaw.normalizedPaw_support, hv] at htotal
  exact ⟨hnon, htotal, hrows⟩

end Erdos577.WeightedFourteen

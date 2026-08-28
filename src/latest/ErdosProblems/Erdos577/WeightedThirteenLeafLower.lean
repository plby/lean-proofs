import ErdosProblems.Erdos577.WeightedThirteenFinalSetup
import ErdosProblems.Erdos577.ThreeRowReplacement

/-! The zero- and one-neighbor leaf cases are excluded by actual insertion factors. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem final_leaf_at_least_two {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hlows : 5 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t)
    (hrep : ∀ u ∈ t, QuadOn G (insert (q 1) (t.erase u)))
    (hx1 : ∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 1) u))
    (hx2 : ∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 2) u))
    (hseven : 7 ≤ 2 * degreeIn G p.leaf t + degreeIn G (v 1) t + degreeIn G (v 2) t) :
    2 ≤ degreeIn G p.leaf t := by
  by_contra! hsmall
  have htq := c.property.blocks_quad t ht
  have hdt := dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have hvout (j : Fin 4) : v j ∉ t := fun hj ↦ disjoint_left.mp hdt
    (mem_union_right _ ((v.mem_support _).mpr ⟨j, rfl⟩)) hj
  have hqout : q 1 ∉ t := fun hj ↦ disjoint_left.mp hdt
    (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨1, rfl⟩))) hj
  have hnu := no_new_universal hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows
    ht htb hta hlows
  have hbound (second : Bool) : degreeIn G (v (if second then 2 else 1)) t ≤ 3 := by
    have hb := degreeIn_le_card G (v (if second then 2 else 1)) t
    rw [htq.card] at hb
    by_contra! hh
    have hfour : degreeIn G (v (if second then 2 else 1)) t = 4 := by omega
    exact hnu second (fun u hu ↦ htq.replace_of_degree_four (hvout _) hfour hu)
  have hb1 : degreeIn G (v 1) t ≤ 3 := hbound false
  have hb2 : degreeIn G (v 2) t ≤ 3 := hbound true
  have hpos : 0 < degreeIn G p.leaf t := by omega
  have hex : ∃ second : Bool, 3 ≤ degreeIn G (v (if second then 2 else 1)) t := by
    by_cases hh : 3 ≤ degreeIn G (v 1) t
    · exact ⟨false, hh⟩
    · exact ⟨true, by change 3 ≤ degreeIn G (v 2) t; omega⟩
  obtain ⟨second, hthree⟩ := hex
  have hx : ∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v (if second then 2 else 1)) u) := by
    cases second
    · exact hx1
    · exact hx2
  rcases common_or_universal_of_three_row htq p.leaf (v (if second then 2 else 1)) (q 1)
    (hvout _) hqout hpos hx hthree hrep with hc | hr
  · have hno : ¬CommonReplacement G p.leaf (q 1) (v (if second then 2 else 1)) t := by
      cases second
      · exact no_extra_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 2
      · exact no_extra_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 3
    exact hno hc
  · exact hnu second hr

end Erdos577.WeightedThirteen

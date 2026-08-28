import ErdosProblems.Erdos577.WeightedThirteenThirdRows

/-! In pattern (13), every low row with at least three third-block contacts is universal. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem third_low_universal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hheavy : 13 ≤ denseWeight p q v t) (second : Bool)
    (hthree : 3 ≤ degreeIn G (q (lowIndex second)) t) :
    ∀ u ∈ t, QuadOn G (insert (q (lowIndex second)) (t.erase u)) := by
  by_contra hnot
  have hdiag := diagonal_of_nonuniversal_low hc p hp hb q hq hd h second ht htb hthree hnot
  obtain ⟨w₀, hw₀⟩ := c.property.blocks_quad t ht
  have hdt₀ : Disjoint ((p.support ∪ q.support) ∪ v.support) w₀.support := by
    rw [hw₀]
    exact dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have hout : q (lowIndex second) ∉ w₀.support := by
    intro hz
    exact disjoint_left.mp hdt₀
      (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨lowIndex second, rfl⟩))) hz
  obtain ⟨_, w, hww, hrow, hwdiag⟩ :=
    w₀.exists_nonuniversal_three_labels (q (lowIndex second)) hout
      (by rw [hw₀]; exact hthree) (by rw [hw₀]; exact hnot)
  have hw : w.support = t := hww.trans hw₀
  have hdt : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support := by
    rw [hww]
    exact hdt₀
  have hbound := nonuniversal_weight_le_twelve hc hcard hdeg hn p hp hb q hq hd h ha hab v hv
    hdis hcl hrows ht htb hta w hw hdt hdiag second hrow hwdiag
  omega

end Erdos577.WeightedThirteen

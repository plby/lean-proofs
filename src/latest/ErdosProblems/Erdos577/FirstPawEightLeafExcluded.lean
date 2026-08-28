import ErdosProblems.Erdos577.FirstPawEightLowBounds

/-! The high-pair leaf supplies the seven-core factor, forcing the contradiction35≤33. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma row_high_reflection (d : Quadrilateral G) (z : V)
    (h : ∀ j : Fin 4, G.Adj z (d j) ↔ j ≠ 3) :
    ∀ j : Fin 4, G.Adj z ((d.rotate 2).reverse j) ↔ j ≠ 3 := by
  intro j
  change G.Adj z (d (-j + 2)) ↔ j ≠ 3
  rw [h]
  fin_cases j <;> decide

theorem third_row_high_contact {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (d : Quadrilateral G) (hdA : d.support = a)
    (hrow : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3)
    (hx0 : G.Adj p.leaf (d 0)) (hx2 : G.Adj p.leaf (d 2)) :
    ¬G.Adj (q 3) (d 1) ∧ (G.Adj (q 3) (d 0) ∨ G.Adj (q 3) (d 2)) := by
  have hout : p.leaf ∉ d.support := by
    intro hh
    have hpa : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hdA ▸ hh))).2 (hp ▸ hpa)
  have hr := d.low_replace_of_highs p.leaf hout hx0 hx2 1 (Or.inl rfl)
  rw [hdA] at hr
  have hn1 : ¬G.Adj (q 3) (d 1) := by
    intro hh
    exact no_common_pair hcard hn p hp hb q hq hd h ha hab 0 5 7
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      ⟨d 1, hdA ▸ (d.mem_support _).mpr ⟨1, rfl⟩, (hrow 1).mpr (by decide), hh, hr⟩
  refine ⟨hn1, ?_⟩
  obtain ⟨_, _, hq1, _, hsum⟩ := low_row_bounds hc hcard hn p hp hb q hq hd h ha hab hheavy
  have htwo : 2 ≤ degreeIn G (q 3) a := by omega
  by_contra! hh
  have hsmall := d.degree_le_mask (q 3) 8 (by
    intro j hj
    fin_cases j
    · exact False.elim (hh.1 hj)
    · exact False.elim (hn1 hj)
    · exact False.elim (hh.2 hj)
    · decide)
  have he : (∑ j : Fin 4, ((8 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  rw [he, hdA] at hsmall
  omega

theorem normalized_leaf_highs_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a)
    (hrow : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3) (hdiag : ¬G.Adj (d 1) (d 3))
    (hx0 : G.Adj p.leaf (d 0)) (hx2 : G.Adj p.leaf (d 2)) (hw2 : G.Adj (q 3) (d 2)) :
    False := by
  let cp := c.presentPaw p hp
  have hcp : cp.Strong := hc.presentPaw_strong hcard hn p hp
  have hpr : cp.remainder = p.support := p.support_eq.symm
  have hD : d.support ∈ cp.blocks := by change d.support ∈ c.blocks; rwa [hdA]
  have hbD : b ≠ d.support := by rw [hdA]; exact hab.symm
  have htwo : 2 ≤ degreeIn G (d 2) q.support := by
    have hh := q.degree_ge_mask (d 2) 10 (by
      intro j hj
      fin_cases j
      · contradiction
      · exact ((hrow 2).mpr (by decide)).symm
      · contradiction
      · exact hw2.symm)
    have he : (∑ j : Fin 4, ((10 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
    rwa [he] at hh
  have hf := h.outside_factor p q hd (d 2) (outside_old_core p hp hb q hq ha hab d hdA 2) htwo
  rw [hq] at hf
  have hz : q 1 ∈ cp.triangle ∪ b := mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩)
  have hzrep : q 1 ∈ b → ∃ x ∈ cp.triangle, ∃ y ∈ cp.triangle,
      x ≠ y ∧ G.Adj (q 1) x ∧ QuadOn G (insert y (b.erase (q 1))) := by
    intro _
    have hout : p.center ∉ q.support := fun hh ↦ disjoint_left.mp hd
      ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
    have hr := q.quad_replaceAt 1 p.center hout (by
      intro j _
      exact (h.2 1 j).mpr (by fin_cases j <;> decide))
    rw [hq] at hr
    refine ⟨p.vertices 2, ?_, p.center, p.center_mem_triangle, ?_, ?_, hr⟩
    · change p.vertices 2 ∈ p.triangle
      simp [Paw.triangle]
    · exact p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
    · exact ((h.2 2 1).mpr (by decide)).symm
  have hbound := CoreTransfer.direct_inside_bound_of_highs hcp d hD hcard hdeg hn hdiag
    hx0 hx2 hb hbD hf hz ((hrow 1).mpr (by decide)) hzrep
  change 35 ≤ contacts G (cp.remainder ∪ {d 1, d 3}) (cp.remainder ∪ (b ∪ d.support)) at hbound
  rw [hpr, ← hq] at hbound
  have hupper := inside_upper hc hcard hdeg hn p hp hb q hq hd h ha hab d hdA hdiag hx0 hx2
  omega

theorem leaf_highs_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (d : Quadrilateral G) (hdA : d.support = a)
    (hrow : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3) (hdiag : ¬G.Adj (d 1) (d 3))
    (hx0 : G.Adj p.leaf (d 0)) (hx2 : G.Adj p.leaf (d 2)) : False := by
  obtain ⟨_, hw⟩ := third_row_high_contact hc hcard hn p hp hb q hq hd h ha hab hheavy
    d hdA hrow hx0 hx2
  rcases hw with hw0 | hw2
  · let v := (d.rotate 2).reverse
    have hv : v.support = a := (Quadrilateral.reverse_support _).trans
      ((d.rotate_support 2).trans hdA)
    exact normalized_leaf_highs_false hc hcard hdeg hn p hp hb q hq hd h ha hab v hv
      (row_high_reflection d (q 1) hrow) hdiag hx2 hx0 hw0
  · exact normalized_leaf_highs_false hc hcard hdeg hn p hp hb q hq hd h ha hab d hdA
      hrow hdiag hx0 hx2 hw2

end Erdos577.FirstPawEight

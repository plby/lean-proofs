import ErdosProblems.Erdos577.JointThreeQuads

/-! Exact seven-set partitions for the triangle-gain comparisons. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma triple_edge_split (v : Quadrilateral G) (a b c : V)
    (ha : a ∉ v.support) (hb : b ∉ v.support) (hc : c ∉ v.support)
    (hab : a ≠ b) (hac : a ≠ c) :
    Disjoint ({a, v 0, v 3} : Finset V) {b, c, v 1, v 2} ∧
      ({a, v 0, v 3} : Finset V) ∪ {b, c, v 1, v 2} = insert a ({b, c} ∪ v.support) := by
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have han (i : Fin 4) : a ≠ v i := fun he ↦ ha (he.symm ▸ hm i)
  have hbn (i : Fin 4) : v i ≠ b := fun he ↦ hb (he ▸ hm i)
  have hcn (i : Fin 4) : v i ≠ c := fun he ↦ hc (he ▸ hm i)
  have hao : a ∉ ({b, c, v 1, v 2} : Finset V) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro hab ⟨hac, han 1, han 2⟩
  have hcol (i : Fin 4) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
      v i ∉ ({b, c, v 1, v 2} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hbn i, hcn i, v.injective.ne hi1, v.injective.ne hi2⟩
  refine ⟨disjoint_insert_left.mpr ⟨hao, disjoint_insert_left.mpr
    ⟨hcol 0 (by decide) (by decide),
      disjoint_singleton_left.mpr (hcol 3 (by decide) (by decide))⟩⟩, ?_⟩
  rw [v.support_four]
  ext u
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

lemma triple_middle_split (v : Quadrilateral G) (a b c : V)
    (ha : a ∉ v.support) (hb : b ∉ v.support) (hc : c ∉ v.support)
    (hab : a ≠ b) (hac : a ≠ c) :
    Disjoint ({a, v 1, v 2} : Finset V) {b, c, v 0, v 3} ∧
      ({a, v 1, v 2} : Finset V) ∪ {b, c, v 0, v 3} = insert a ({b, c} ∪ v.support) := by
  let v' := (v.rotate 1).reverse
  have hv : v'.support = v.support := by
    simp only [v', Quadrilateral.reverse_support, Quadrilateral.rotate_support]
  obtain ⟨hd, he⟩ := triple_edge_split v' a b c (by rwa [hv]) (by rwa [hv]) (by rwa [hv]) hab hac
  change Disjoint ({a, v 1, v 2} : Finset V) {b, c, v 0, v 3} at hd
  change ({a, v 1, v 2} : Finset V) ∪ {b, c, v 0, v 3} = insert a ({b, c} ∪ v'.support) at he
  rw [hv] at he
  exact ⟨hd, he⟩

variable [DecidableRel G.Adj]

lemma FinalRows.high_diagonal_of_gain {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hdiag : ¬G.Adj (v 1) (v 3))
    (u : V) (hu : u = x ∨ u = y) {t b : Finset V}
    (ht : G.IsNClique 3 t) (hb : QuadOn G b) (htb : Disjoint t b)
    (hcover : t ∪ b = insert u ({z, w} ∪ v.support)) (hfive : 5 ≤ edgeCount G b) :
    G.Adj (v 0) (v 2) := by
  have hle := h.gain u hu t b ht hb htb hcover
  have he := v.edgeCount_eq
  by_contra hno
  rw [if_neg hno, if_neg hdiag] at he
  omega

theorem FinalRows.extreme_contact_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hdiag : ¬G.Adj (v 1) (v 3))
    (u : V) (hu : u = x ∨ u = y) (hu0 : G.Adj u (v 0)) (hu3 : G.Adj u (v 3))
    (hcontact : G.Adj w (v 1) ∨ G.Adj w (v 2)) : False := by
  obtain ⟨huz, huw, huout, hubound⟩ := h.terminal_data u hu
  have hm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hwo : w ∉ ({z, v 1, v 2} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨h.pair_edge.symm.ne, fun he ↦ h.w_out (he.symm ▸ hm 1),
      fun he ↦ h.w_out (he.symm ▸ hm 2)⟩
  obtain ⟨hquad, hfive⟩ := edge_triangle_five z w (v 1) (v 2) hwo
    (h.three 1 (by decide)) (h.three 2 (by decide)) (v.adjacent 1) h.pair_edge.symm hcontact
  have ht : G.IsNClique 3 {u, v 0, v 3} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hu0, hu3, (v.adjacent 3).symm⟩
  obtain ⟨hdis, hcover⟩ := triple_edge_split v u z w huout h.z_out h.w_out huz huw
  have hhigh := h.high_diagonal_of_gain hdiag u hu ht hquad hdis hcover hfive
  have hpos : 1 ≤ degreeIn G w {v 1, v 2} := by
    rcases hcontact with hw1 | hw2
    · exact card_pos.mpr ⟨v 1, mem_filter.mpr ⟨by simp, hw1⟩⟩
    · exact card_pos.mpr ⟨v 2, mem_filter.mpr ⟨by simp, hw2⟩⟩
  exact h.low u hu v rfl ⟨hhigh, hdiag⟩ (exact_extreme_row v u hubound hu0 hu3)
    z w (Or.inl ⟨rfl, rfl⟩) h.three hpos

end Erdos577.JointFinal

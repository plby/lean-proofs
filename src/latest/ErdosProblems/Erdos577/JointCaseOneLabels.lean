import ErdosProblems.Erdos577.JointFirstSwap

/-! A full leaf row, a center neighbor, and two noncentral neighbors give CaseI labels. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem case_one_labels_of_clique (p : Paw G) {s : Finset V} (hs : G.IsNClique 4 s)
    (hfull : degreeIn G p.leaf s = 4) (hcenter : 0 < degreeIn G p.center s)
    (hsecond : 2 ≤ degreeIn G (p.vertices 2) s)
    (hd : Disjoint (s.filter (G.Adj p.center)) (s.filter (G.Adj (p.vertices 2)))) :
    ∃ q : Quadrilateral G, q.support = s ∧ CaseOne p q := by
  obtain ⟨v, hv⟩ := card_pos.mp hcenter
  obtain ⟨b1, hb1, b2, hb2, hb12⟩ := one_lt_card.mp
    (show 1 < (s.filter (G.Adj (p.vertices 2))).card from
      lt_of_lt_of_le (by decide : 1 < 2) hsecond)
  have hvb1 : v ≠ b1 := fun he ↦ disjoint_left.mp hd hv (he.symm ▸ hb1)
  have hvb2 : v ≠ b2 := fun he ↦ disjoint_left.mp hd hv (he.symm ▸ hb2)
  have hsub : ({v, b1, b2} : Finset V) ⊆ s :=
    insert_subset (mem_filter.mp hv).1 (insert_subset (mem_filter.mp hb1).1
      (singleton_subset_iff.mpr (mem_filter.mp hb2).1))
  have hrest : (s \ {v, b1, b2}).card = 1 := by
    rw [card_sdiff_of_subset hsub, hs.card_eq,
      card_triple_eq_three_iff.mpr ⟨hvb1, hvb2, hb12⟩]
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < (s \ {v, b1, b2}).card)
  have hneq : w ≠ v ∧ w ≠ b1 ∧ w ≠ b2 := by
    simpa only [mem_insert, mem_singleton, not_or] using (mem_sdiff.mp hw).2
  let e := fourTuple w v b1 b2 hneq.1 hneq.2.1 hneq.2.2 hvb1 hvb2 hb12
  have hem (i : Fin 4) : e i ∈ s := by
    fin_cases i
    · exact (mem_sdiff.mp hw).1
    · exact (mem_filter.mp hv).1
    · exact (mem_filter.mp hb1).1
    · exact (mem_filter.mp hb2).1
  let q := Quadrilateral.ofEdges e (fun i ↦ hs.isClique (hem i) (hem (i + 1))
    (e.injective.ne (by fin_cases i <;> decide)))
  have hq : q.support = s := by
    apply eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
      exact hem i
    · rw [q.card_support, hs.card_eq]
  exact ⟨q, hq, hq.symm ▸ hfull, (mem_filter.mp hv).2,
    (mem_filter.mp hb1).2, (mem_filter.mp hb2).2⟩

variable [Fintype V]

theorem case_one_labels_of_degrees {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hcenter : 0 < degreeIn G p.center s)
    (hsecond : 2 ≤ degreeIn G (p.vertices 2) s) :
    ∃ q : Quadrilateral G, q.support = s ∧ CaseOne p q := by
  have hcl := FullRow.full_leaf_clique hc p hp hs hfull
  have hd := triangle_rows_disjoint hc hcard hn p hp hs (by omega) p.center (p.vertices 2)
    p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  exact case_one_labels_of_clique p hcl hfull hcenter hsecond hd

end Erdos577.JointClaims

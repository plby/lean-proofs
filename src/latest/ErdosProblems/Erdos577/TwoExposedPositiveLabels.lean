import ErdosProblems.Erdos577.TwoExposedZeroExchange

/-! Three positive, disjoint triangle rows label three distinct vertices of the complete block. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_positive_labels {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hx : degreeIn G p.leaf a = 4) (hr : 0 < degreeIn G p.center a)
    (hb : 0 < degreeIn G (p.vertices 2) a) (ht : 0 < degreeIn G (p.vertices 3) a) :
    ∃ q : Quadrilateral G, q.support = a ∧ G.Adj p.center (q 0) ∧
      G.Adj (p.vertices 2) (q 1) ∧ G.Adj (p.vertices 3) (q 2) := by
  obtain ⟨v, hv⟩ := card_pos.mp hr
  obtain ⟨w, hw⟩ := card_pos.mp hb
  obtain ⟨z, hz⟩ := card_pos.mp ht
  have hcl := FullRow.full_leaf_clique hc p hp ha hx
  have hrow (x y : V) (hxt : x ∈ p.triangle) (hyt : y ∈ p.triangle) (hxy : x ≠ y) :=
    JointClaims.triangle_rows_disjoint hc hcard hn p hp ha (by omega) x y hxt hyt hxy
  have hvw : v ≠ w := fun he ↦ disjoint_left.mp
    (hrow p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
      (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))) hv (he.symm ▸ hw)
  have hvz : v ≠ z := fun he ↦ disjoint_left.mp
    (hrow p.center (p.vertices 3) p.center_mem_triangle (by simp [Paw.triangle])
      (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))) hv (he.symm ▸ hz)
  have hwz : w ≠ z := fun he ↦ disjoint_left.mp
    (hrow (p.vertices 2) (p.vertices 3) (by simp [Paw.triangle]) (by simp [Paw.triangle])
      (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3))) hw (he.symm ▸ hz)
  have hsub : ({v, w, z} : Finset V) ⊆ a := insert_subset (mem_filter.mp hv).1
    (insert_subset (mem_filter.mp hw).1 (singleton_subset_iff.mpr (mem_filter.mp hz).1))
  have hsize : (a \ {v, w, z}).card = 1 := by
    rw [card_sdiff_of_subset hsub, hcl.card_eq, card_triple_eq_three_iff.mpr ⟨hvw, hvz, hwz⟩]
  obtain ⟨t, ht⟩ := card_pos.mp (by omega : 0 < (a \ {v, w, z}).card)
  have hneq : t ≠ v ∧ t ≠ w ∧ t ≠ z := by
    simpa only [mem_insert, mem_singleton, not_or] using (mem_sdiff.mp ht).2
  let e := fourTuple v w z t hvw hvz hneq.1.symm hwz hneq.2.1.symm hneq.2.2.symm
  have hem (i : Fin 4) : e i ∈ a := by
    fin_cases i
    · exact (mem_filter.mp hv).1
    · exact (mem_filter.mp hw).1
    · exact (mem_filter.mp hz).1
    · exact (mem_sdiff.mp ht).1
  let q := Quadrilateral.ofEdges e (fun i ↦ hcl.isClique (hem i) (hem (i + 1))
    (e.injective.ne (by fin_cases i <;> decide)))
  have hq : q.support = a := by
    apply eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
      exact hem i
    · rw [q.card_support, hcl.card_eq]
  exact ⟨q, hq, (mem_filter.mp hv).2, (mem_filter.mp hw).2, (mem_filter.mp hz).2⟩

end Erdos577.TwoExposed

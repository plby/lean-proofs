import ErdosProblems.Erdos577.LargeLeafCore

/-! Both source distinguished pairs are labeled simultaneously by an actual quadrilateral. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_pair_labels (p : Paw G) {a : Finset V} (ha : G.IsNClique 4 a)
    (hd : Disjoint p.support a) (hT : 11 ≤ contacts G p.triangle a) :
    ∃ d : Quadrilateral G, d.support = a ∧
      (∀ i : Fin 4, i ≠ 0 → G.Adj p.center (d i)) ∧
      G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 1} ∧
      G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 3} := by
  have hTA := hd.mono_left (p.support_eq ▸ subset_insert _ _)
  obtain ⟨a1, a2, a3, a4, hA, hr1, hr2, hr3, hcl2, hcl3⟩ :=
    dense_triangle_clique_label p.triangle_clique ha hTA hT p.center_mem_triangle
  have hfour : ({a1, a2, a3, a4} : Finset V).card = 4 := hA ▸ ha.card_eq
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := JointCore.four_distinct hfour
  have hm1 : a1 ∈ a := by rw [hA]; simp
  have hm2 : a2 ∈ a := by rw [hA]; simp
  have hm3 : a3 ∈ a := by rw [hA]; simp
  have hm4 : a4 ∈ a := by rw [hA]; simp
  let e := fourTuple a4 a3 a1 a2 h34.symm h14.symm h24.symm h13.symm h23.symm h12
  have hem (i : Fin 4) : e i ∈ a := by fin_cases i <;> assumption
  let d := Quadrilateral.ofEdges e (fun i ↦ ha.isClique (hem i) (hem (i + 1))
    (e.injective.ne (by fin_cases i <;> decide)))
  have heq : d.support = a := by
    change tupleSupport e = a
    rw [fourTuple_support, hA]
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hrout : p.center ∉ ({p.vertices 2, p.vertices 3} : Finset V) := by
    simp only [Paw.center, mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  have htri : p.triangle.erase p.center = {p.vertices 2, p.vertices 3} := erase_insert hrout
  have complete_pair (u : V) (hu : u ∈ a) (hu4 : u ≠ a4)
      (hcl : G.IsClique (p.triangle.erase p.center ∪ {a4, u} : Finset V)) :
      G.IsNClique 4 {p.vertices 2, p.vertices 3, a4, u} := by
    have hsmall : ({p.vertices 2, p.vertices 3} : Finset V) ⊆ p.support := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩
      · exact (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
    have hpair : ({a4, u} : Finset V) ⊆ a := insert_subset hm4 (singleton_subset_iff.mpr hu)
    have hdis := hd.mono hsmall hpair
    rw [htri, insert_union, singleton_union] at hcl
    refine ⟨hcl, ?_⟩
    have hcard := card_union_of_disjoint hdis
    rw [card_pair (p.vertices.injective.ne (by decide)), card_pair hu4.symm] at hcard
    simpa only [insert_union, singleton_union] using hcard
  refine ⟨d, heq, ?_, complete_pair a3 hm3 h34 hcl3, complete_pair a2 hm2 h24 hcl2⟩
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · exact hr3
  · exact hr1
  · exact hr2

end Erdos577.LargeLeaf

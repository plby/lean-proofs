import ErdosProblems.Erdos577.JointClaimFourRows

/-! The same maximal core with reversed cyclic labels and the alternate distinguished pair. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.reversed_early {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a)
    (hmiss : ¬G.Adj (p.vertices 2) (d 2) ∧ ¬G.Adj (p.vertices 2) (d 3)) :
    Core c p q d.reverse a := by
  obtain ⟨hlow, tag, htag, hpat⟩ := h.missing_pair_source hmiss
  have hpat' := early_source_reverse tag p d htag hpat.1
  have hlabels : d.reverse.support = a := d.reverse_support.trans h.labels
  have hPA : Disjoint p.support d.reverse.support := by
    rw [hlabels]
    exact h.paw_disjoint h.config.2.2.1
  have hTA : Disjoint p.triangle d.reverse.support :=
    hPA.mono_left (p.support_eq ▸ subset_insert _ _)
  have hx : p.leaf ∉ p.triangle ∪ d.reverse.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact disjoint_left.mp hPA (p.support_eq ▸ mem_insert_self _ _) hh
  have hlocal := hpat'.1.complements tag p d.reverse hTA p.leaf hx
  rw [hlabels] at hlocal
  obtain ⟨hr1, hr2, hz, hprimary, hpe, hs1, hs2, ht⟩ := hlocal
  obtain ⟨hp, hs, ha, has, hcase, houter, hweighted⟩ := h.config
  have hm (i : Fin 4) : d.reverse i ∈ a := hlabels ▸ (d.reverse.mem_support _).mpr ⟨i, rfl⟩
  have hz1 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) houter hweighted (d.reverse 2) (hm 2) hr1 hs1
  have hz2 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) houter hweighted (d.reverse 3) (hm 3) hr2 hs2
  obtain ⟨h17, h22⟩ := JointCore.core_inside_sums hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) h.leaf_zero h.last_zero (d.reverse 2) (d.reverse 3) (hm 2) (hm 3) hz1 hz2
  refine ⟨h.maximal, hlabels, hr1, hr2, hz, h.leaf_zero, h.last_zero, h.third_replacement,
    hprimary, hpe, hs1, hs2, ht, h.outside_factor, hz1, hz2, h17, h22, ?_, ?_⟩
  · intro hh
    exact False.elim (by omega)
  · intro _
    exact ⟨tag, hpat'⟩

end Erdos577.JointFinal

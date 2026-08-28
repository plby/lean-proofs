import ErdosProblems.Erdos577.TripleFinalExcluded

/-! The specified three-leaf block supplies its actual triple-pattern configuration. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.triple_configuration_of_rows {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hcl : G.IsNClique 4 s) (hthree : degreeIn G p.leaf s = 3)
    (hsecond : s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj p.leaf))
    (hthird : s.filter (G.Adj (p.vertices 3)) = ∅) :
    ∃ q : Quadrilateral G, q.support = s ∧ UniversalTriple.Configuration c p q := by
  obtain ⟨v, hv⟩ := c.property.blocks_quad s hs
  obtain ⟨q, hqv, hrow⟩ := v.exists_three_contact_labels p.leaf (by rw [hv]; exact hthree)
  have hq : q.support = s := hqv.trans hv
  have hm (i : Fin 4) : q i ∈ s := by
    rw [← hq]
    exact (q.mem_support _).mpr ⟨i, rfl⟩
  have h2 (i : Fin 4) : G.Adj (p.vertices 2) (q i) ↔ i ≠ 3 := by
    constructor
    · intro he
      have hh : q i ∈ s.filter (G.Adj (p.vertices 2)) := mem_filter.mpr ⟨hm i, he⟩
      rw [hsecond] at hh
      exact (hrow i).mp (mem_filter.mp hh).2
    · intro hi
      have hh : q i ∈ s.filter (G.Adj p.leaf) := mem_filter.mpr ⟨hm i, (hrow i).mpr hi⟩
      rw [← hsecond] at hh
      exact (mem_filter.mp hh).2
  have hrows := JointClaims.triangle_rows_disjoint hc hcard hn p hp hs hthree.ge
    p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  refine ⟨q, hq, hp, hq.symm ▸ hs, hq.symm ▸ hcl, hrow, h2, ?_, ?_,
    hc.paw_triangle_block_bound hcard hdeg hn p hp⟩
  · intro i he
    have hh : q i ∈ s.filter (G.Adj (p.vertices 3)) := mem_filter.mpr ⟨hm i, he⟩
    rw [hthird] at hh
    exact notMem_empty _ hh
  · intro i he
    by_contra hi
    exact disjoint_left.mp hrows (mem_filter.mpr ⟨hm i, he⟩)
      (mem_filter.mpr ⟨hm i, (h2 i).mpr hi⟩)

end Erdos577

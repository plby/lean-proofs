import ErdosProblems.Erdos577.UniversalTriple
import ErdosProblems.Erdos577.ThreeContactLabels

/-! Actual paw and cyclic block labels for Property A, available in every strong chain. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure UniversalTriple.Configuration (c : TriangleChain G) (p : Paw G)
    (q : Quadrilateral G) : Prop where
  paw : p.support = c.remainder
  block : q.support ∈ c.blocks
  complete : G.IsNClique 4 q.support
  leaf_row : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3
  second_row : ∀ i : Fin 4, G.Adj (p.vertices 2) (q i) ↔ i ≠ 3
  third_row : ∀ i : Fin 4, ¬G.Adj (p.vertices 3) (q i)
  center_row : ∀ i : Fin 4, G.Adj p.center (q i) → i = 3
  triangle_bound : ∀ a ∈ c.blocks, contacts G p.triangle a ≤ 10

lemma UniversalTriple.Configuration.disjoint {c : TriangleChain G} {p : Paw G}
    {q : Quadrilateral G} (h : UniversalTriple.Configuration c p q) :
    Disjoint p.support q.support := by
  rw [h.paw]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset h.block)

theorem TriangleChain.Feasible.exists_triple_configuration {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) :
    ∃ (p' : Paw G) (q : Quadrilateral G), p'.leaf = p.leaf ∧
      p'.triangle = p.triangle ∧ UniversalTriple.Configuration c p' q := by
  obtain ⟨p', s, hleaf, htri, hsupp, hs, hthree, hcl, hb, h2, h3⟩ :=
    hc.exists_ordered_three_leaf_block hcard hdeg hn p hp
  obtain ⟨v, hv⟩ := c.property.blocks_quad s hs
  obtain ⟨q, hqv, hrow⟩ := v.exists_three_contact_labels p'.leaf (by rw [hv]; exact hthree)
  have hq : q.support = s := hqv.trans hv
  have hm (i : Fin 4) : q i ∈ s := by
    rw [← hq]
    exact (q.mem_support _).mpr ⟨i, rfl⟩
  have hsecond (i : Fin 4) : G.Adj (p'.vertices 2) (q i) ↔ i ≠ 3 := by
    constructor
    · intro he
      have hh : q i ∈ s.filter (G.Adj (p'.vertices 2)) := mem_filter.mpr ⟨hm i, he⟩
      rw [h2] at hh
      exact (hrow i).mp (mem_filter.mp hh).2
    · intro hi
      have hh : q i ∈ s.filter (G.Adj p'.leaf) := mem_filter.mpr ⟨hm i, (hrow i).mpr hi⟩
      rw [← h2] at hh
      exact (mem_filter.mp hh).2
  have hrows := JointClaims.triangle_rows_disjoint hc hcard hn p' (hsupp.trans hp) hs
    (by omega : 3 ≤ degreeIn G p'.leaf s) p'.center (p'.vertices 2)
    p'.center_mem_triangle (by simp [Paw.triangle])
    (p'.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  refine ⟨p', q, hleaf, htri, hsupp.trans hp, hq.symm ▸ hs, hq.symm ▸ hcl,
    hrow, hsecond, ?_, ?_, hb⟩
  · intro i he
    have hh : q i ∈ s.filter (G.Adj (p'.vertices 3)) := mem_filter.mpr ⟨hm i, he⟩
    rw [h3] at hh
    simp at hh
  · intro i he
    by_contra hi
    exact disjoint_left.mp hrows (mem_filter.mpr ⟨hm i, he⟩)
      (mem_filter.mpr ⟨hm i, (hsecond i).mpr hi⟩)

theorem TriangleChain.Strong.exists_triple_configuration {c : TriangleChain G}
    (hc : c.Strong) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    ∃ (p : Paw G) (q : Quadrilateral G), p.leaf = c.terminal ∧
      p.triangle = c.triangle ∧ UniversalTriple.Configuration c p q := by
  obtain ⟨p, hx, ht, hp⟩ := hc.exists_paw
  obtain ⟨p', q, hleaf, htri, hconfig⟩ :=
    hc.toFeasible.exists_triple_configuration hcard hdeg hn p hp
  exact ⟨p', q, hleaf.trans hx, htri.trans ht, hconfig⟩

theorem TriangleChain.Strong.triangle_block_bound {c : TriangleChain G} (hc : c.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) : ∀ a ∈ c.blocks, contacts G c.triangle a ≤ 10 := by
  obtain ⟨p, _, ht, hp⟩ := hc.exists_paw
  rw [← ht]
  exact hc.toFeasible.paw_triangle_block_bound hcard hdeg hn p hp

end Erdos577

import ErdosProblems.Erdos577.TripleForbiddenCases

/-! The two different paw centers give explicit strong chains with both scores preserved. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

theorem UCase.exists_chain (s : UCase p a w u v) (h : HighCore c p q a w)
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ d : TriangleChain G, d.Strong ∧ (s.paw h).support = d.remainder ∧
      d.terminal = q 3 ∧ d.triangle = {w, u, v} ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ q.support → j ≠ a → j ∈ d.blocks := by
  obtain ⟨d, hd, hY, hT, hE, hC, hblocks⟩ := h.toConfiguration.exists_exposed_chain hc
  have ha : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨h.core_ne, h.core_block⟩)
  have hleaf : (s.paw h).leaf = d.terminal := by rw [hY]; rfl
  have hsub : (s.paw h).triangle ⊆ d.triangle ∪ a := by
    rw [hT, s.paw_triangle]
    exact fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hquad : QuadOn G ((d.triangle ∪ a) \ (s.paw h).triangle) := by
    rw [hT, s.paw_triangle]
    exact s.complement_quad
  have hscore : edgeCount G a ≤ edgeCount G ((d.triangle ∪ a) \ (s.paw h).triangle) := by
    rw [hT, s.paw_triangle]
    exact s.complement_score
  obtain ⟨e, he, hp, ht, htri, heE, heC, hbs⟩ :=
    hd.exchange_core_triangle hcard hn ha (s.paw h) hleaf hsub hquad hscore
  refine ⟨e, he, hp, ht, htri.trans (s.paw_triangle h), heE.trans hE, heC.trans hC, ?_⟩
  intro j hj hjQ hja
  rw [hbs]
  apply mem_union_left
  apply mem_erase.mpr
  refine ⟨hja, ?_⟩
  rw [hblocks]
  exact mem_union_left _ (mem_erase.mpr ⟨hjQ, hj⟩)

theorem VCase.exists_chain (s : VCase p a w u v) (h : HighCore c p q a w)
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ d : TriangleChain G, d.Strong ∧ (s.paw h).support = d.remainder ∧
      d.terminal = p.leaf ∧ d.triangle = {p.center, u, v} ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ a → j ∈ d.blocks := by
  let d := c.presentPaw p h.paw
  have hd : d.Feasible := hc.presentPaw_feasible p h.paw
  have hleaf : (s.paw h).leaf = d.terminal := rfl
  have hsub : (s.paw h).triangle ⊆ d.triangle ∪ a := by
    rw [s.paw_triangle]
    exact fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hquad : QuadOn G ((d.triangle ∪ a) \ (s.paw h).triangle) := by
    rw [s.paw_triangle]
    exact s.complement_quad
  have hscore : edgeCount G a ≤ edgeCount G ((d.triangle ∪ a) \ (s.paw h).triangle) := by
    rw [s.paw_triangle]
    exact s.complement_score
  obtain ⟨e, he, hp, ht, htri, heE, heC, hbs⟩ :=
    hd.exchange_core_triangle hcard hn h.core_block (s.paw h) hleaf hsub hquad hscore
  refine ⟨e, he, hp, ht, htri.trans (s.paw_triangle h), heE, heC, ?_⟩
  intro j hj hja
  rw [hbs]
  exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)

end Erdos577.UniversalTriple

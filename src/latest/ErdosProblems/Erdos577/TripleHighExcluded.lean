import ErdosProblems.Erdos577.TripleCaseImages

/-! The actual core patterns and forty-eight witnesses exclude the high-contact branch. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w : V}

theorem HighCore.false (h : HighCore c p q a w) (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : False := by
  obtain ⟨b, hb⟩ := c.property.blocks_quad a h.core_block
  obtain ⟨tag, d, hda, hs⟩ := TripleCorePatterns.source_classification hc p h.paw
    h.core_block b hb h.triangle_ten
  have hd : Disjoint p.support d.support := by
    rw [hda]
    exact h.toConfiguration.paw_disjoint_block h.core_block
  obtain ⟨j, hj⟩ := (d.mem_support w).mp (hda.symm ▸ h.marked)
  have hmark : hs.copy hd (TripleCorePatterns.marked j) = w := by
    rw [hs.copy_apply]
    change PawEncoding.labeling p d hd (Fin.natAdd 4 j) = w
    rw [PawEncoding.labeling_right]
    exact hj
  rcases TripleCorePatterns.witness tag j with hu | hv | ht
  · have him := hu.image (hs.copy hd) (hs.copy_block_score hd)
    rw [hs.copy_paw hd, hs.copy_block hd, hda, hmark] at him
    exact him.false h hc hcard hdeg hn
  · have him := hv.image (hs.copy hd) (hs.copy_block_score hd)
    rw [hs.copy_paw hd, hs.copy_block hd, hda, hmark] at him
    exact him.false h hc hcard hdeg hn
  · have hupper : ∀ x ∈ (TripleCorePatterns.paw tag).triangle ∪ TripleCorePatterns.block,
        ∀ y ∈ (TripleCorePatterns.paw tag).triangle ∪ TripleCorePatterns.block,
          G.Adj (hs.copy hd x) (hs.copy hd y) → (TripleCorePatterns.graph tag).Adj x y := by
      rw [TripleCorePatterns.paw_core]
      exact fun x hx y hy ↦ (hs.core_adj_iff hd x hx y hy).mp
    have him := ht.image (hs.copy hd) (hs.copy_block_score hd) hupper
    rw [hs.copy_paw hd, hs.copy_block hd, hda, hmark] at him
    exact him.false h hc hcard hdeg hn

theorem Configuration.heavy_paw_contacts_le_eight (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a) : contacts G p.support a ≤ 8 := by
  by_contra hlarge
  obtain ⟨w, hw⟩ := h.exists_high_core hc hcard hdeg hn ha haq hheavy (by omega)
  exact hw.false hc hcard hdeg hn

end Erdos577.UniversalTriple

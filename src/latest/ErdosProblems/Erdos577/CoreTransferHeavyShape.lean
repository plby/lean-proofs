import ErdosProblems.Erdos577.CoreTransferSmallPaw
import ErdosProblems.Erdos577.FirstPawFinalClassification

/-! Every heavy outside block has a zero leaf row, two low rows at most one,
and a complete block with at least eleven triangle contacts. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_shape {c : TriangleChain G} (hc : c.Strong) {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) (hab : a ≠ b)
    (hheavy : 13 ≤ contacts G (rows c q) a) :
    degreeIn G c.terminal a = 0 ∧ 11 ≤ contacts G c.triangle a ∧
      degreeIn G (q 1) a ≤ 1 ∧ degreeIn G (q 3) a ≤ 1 ∧ G.IsNClique 4 a ∧
      ∀ v ∈ c.triangle, ∀ u ∈ a, QuadOn G (insert v (a.erase u)) := by
  have hq := r.blocks_subset r.contains_cycle
  have haq : a ≠ q.support := fun he ↦ hna (he ▸ r.contains_cycle)
  have hF : 9 ≤ contacts G c.remainder a := by
    by_contra! hh
    exact small_remainder_false r hcard hn hb hbq hcore ha hna hab hheavy (by omega)
  have hrows := rows_contacts c q hq a
  have hrem := remainder_contacts c a
  have hzero : degreeIn G c.terminal a = 0 := by
    by_contra hz
    obtain ⟨p, hx, ht, hp⟩ := hc.exists_paw
    obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
    have hclassification := hc.toFeasible.first_paw_final hcard hdeg hn p hp ha v hv
      (by rw [hp, hv]; exact hF) (by rw [hx, hv]; omega)
    have hnine : contacts G c.remainder a = 9 := by
      rw [← hp, ← hv]
      exact hclassification.2.1
    obtain ⟨i, hi, hrow⟩ : ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ 2 ≤ degreeIn G (q i) a := by
      by_cases hh : 2 ≤ degreeIn G (q 1) a
      · exact ⟨1, Or.inl rfl, hh⟩
      · exact ⟨3, Or.inr rfl, by omega⟩
    have hout : q i ∉ p.support ∪ v.support := by
      rw [hp, hv]
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact (mem_sdiff.mp (c.complementPartition.block_subset hq
          ((q.mem_support _).mpr ⟨i, rfl⟩))).2 hh
      · exact disjoint_left.mp (c.property.blocks_disjoint hq ha haq.symm)
          ((q.mem_support _).mpr ⟨i, rfl⟩) hh
    have hf := hclassification.2.2.1 (q i) hout (by rw [hv]; exact hrow)
    rw [ht, hv] at hf
    exact r.no_local_factor hcard hn i hi ha hna hf
  have ht9 : 9 ≤ contacts G c.triangle a := by omega
  have h1 := r.low_degree_le_one hcard hn 1 (Or.inl rfl) ha hna ht9
  have h3 := r.low_degree_le_one hcard hn 3 (Or.inr rfl) ha hna ht9
  have ht11 : 11 ≤ contacts G c.triangle a := by omega
  obtain ⟨hcomplete, hreplace⟩ := hc.toFeasible.all_triangle_universal_replacements ha ht11
  exact ⟨hzero, ht11, h1, h3, hcomplete, hreplace⟩

end Erdos577.CoreTransfer

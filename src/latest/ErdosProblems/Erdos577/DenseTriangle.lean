import ErdosProblems.Erdos577.DenseTriangleWitnesses0
import ErdosProblems.Erdos577.DenseTriangleWitnesses1
import ErdosProblems.Erdos577.DenseTriangleWitnesses2
import ErdosProblems.Erdos577.DenseTriangleTransport
import ErdosProblems.Erdos577.CliqueRows
import ErdosProblems.Erdos577.CliqueCounts

/-! The dense-triangle replacement restrictions in every feasible chain. -/

namespace Erdos577

open Finset

namespace DenseTriangle

theorem finite_classification (diagonal : Fin 4) (hd : diagonal ≠ 3) (m : Fin 65536)
    (hh : 10 ≤ DenseOutside.triangleCount m.val) :
    Positive diagonal m.val ∨ DiamondRows diagonal m.val := by
  fin_cases diagonal
  · exact D0.finite_classification m hh
  · exact D1.finite_classification m hh
  · exact D2.finite_classification m hh
  · exact False.elim (hd rfl)

end DenseTriangle

namespace TriangleChain

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Feasible.dense_triangle_dichotomy {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : 10 ≤ contacts G c.triangle b) :
    G.IsNClique 4 b ∨
      (edgeCount G b = 5 ∧ contacts G c.triangle b = 10 ∧
        (∃ u ∈ c.triangle, ∃ v ∈ c.triangle, u ≠ v ∧
          degreeIn G u b = 4 ∧ degreeIn G v b = 4) ∧
        ∃ low ∈ c.triangle,
          (∀ j : Fin 4, G.Adj low (q j) ↔ G.Adj (q j) (q (j + 2))) ∧
          ∀ v ∈ c.triangle, v ≠ low → degreeIn G v b = 4) := by
  by_cases hd : Unattached.diagonal q = 3
  · left
    apply clique_of_four_six (hq ▸ q.card_support)
    rw [← hq, ← Unattached.oldEdges_diagonal, hd]
    decide +kernel
  · have hdisj : Disjoint c.remainder q.support := by
      rw [hq]
      apply disjoint_left.mpr
      intro v hv hvb
      exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
    have hf := DenseTriangle.finite_classification (Unattached.diagonal q) hd
      (Unattached.encoded c q) (by rw [DenseOutside.triangleCount_encoded, hq]; exact h)
    rcases hf with hp | hr
    · have hg := hp.transport c q hdisj
      rw [hq] at hg
      exact False.elim (hc.no_strict_improvement hb hg)
    · right
      have he := hr.oldEdges
      rw [Unattached.oldEdges_diagonal, hq] at he
      have ht := hr.triangleCount
      rw [DenseOutside.triangleCount_encoded, hq] at ht
      have hp := hr.full_pair c q
      have hs := hr.exact_shape c q
      rw [hq] at hp hs
      exact ⟨he, ht, hp, hs⟩

omit [DecidableRel G.Adj] in
lemma triangle_disjoint_block (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks) :
    Disjoint c.triangle b := by
  apply disjoint_left.mpr
  intro v hv hvb
  exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 (mem_insert_of_mem hv)

theorem Feasible.two_triangle_universal_replacements {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (h : 10 ≤ contacts G c.triangle b) :
    5 ≤ edgeCount G b ∧ ∃ u ∈ c.triangle, ∃ v ∈ c.triangle, u ≠ v ∧
      (∀ w ∈ b, QuadOn G (insert u (b.erase w))) ∧
      (∀ w ∈ b, QuadOn G (insert v (b.erase w))) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  rcases hc.dense_triangle_dichotomy hb q hq h with hcl | ⟨he, _, hp, _⟩
  · refine ⟨?_, two_universal_rows_of_ten_clique c.property.triangle_clique.card_eq hcl
      (c.triangle_disjoint_block hb) h⟩
    rw [edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  · obtain ⟨u, hu, v, hv, hne, hdu, hdv⟩ := hp
    have hqu : u ∉ b := fun h ↦ disjoint_left.mp (c.triangle_disjoint_block hb) hu h
    have hqv : v ∉ b := fun h ↦ disjoint_left.mp (c.triangle_disjoint_block hb) hv h
    exact ⟨by omega, u, hu, v, hv, hne,
      fun _ hw ↦ (c.property.blocks_quad b hb).replace_of_degree_four hqu hdu hw,
      fun _ hw ↦ (c.property.blocks_quad b hb).replace_of_degree_four hqv hdv hw⟩

theorem Feasible.all_triangle_universal_replacements {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) (h : 11 ≤ contacts G c.triangle b) :
    G.IsNClique 4 b ∧ ∀ v ∈ c.triangle, ∀ w ∈ b, QuadOn G (insert v (b.erase w)) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  rcases hc.dense_triangle_dichotomy hb q hq (by omega) with hcl | ⟨_, ht, _⟩
  · exact ⟨hcl, fun _ hv _ hw ↦ every_universal_row_of_eleven_clique
      c.property.triangle_clique.card_eq hcl (c.triangle_disjoint_block hb) h hv hw⟩
  · omega

end TriangleChain

end Erdos577

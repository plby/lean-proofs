import ErdosProblems.Erdos577.PawNine
import ErdosProblems.Erdos577.AlmostComplete

/-! Dense joins to complete blocks, as an immediate consequence of Wang 3.4(b). -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Paw.clique_nine_triangle_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsClique q.support)
    (hleaf : 1 ≤ degreeIn G p.leaf q.support) (htri : 9 ≤ contacts G p.triangle q.support) :
    LocalFactor G (p.support ∪ q.support) := by
  have hv : ∃ v ∈ p.triangle, 3 ≤ degreeIn G v q.support := by
    by_contra hn
    have hle (v : V) (hv : v ∈ p.triangle) : degreeIn G v q.support ≤ 2 := by
      have hnot : ¬3 ≤ degreeIn G v q.support := fun h ↦ hn ⟨v, hv, h⟩
      omega
    have hsum : contacts G p.triangle q.support ≤ ∑ _ ∈ p.triangle, (2 : ℕ) :=
      sum_le_sum hle
    have hc : (∑ _ ∈ p.triangle, (2 : ℕ)) = 6 := by simp [p.triangle_clique.card_eq]
    rw [hc] at hsum
    omega
  obtain ⟨v, hv, hv3⟩ := hv
  have hz : v ∉ q.support := by
    intro h
    apply (disjoint_left.mp hd) _ h
    rw [p.support_eq]
    exact mem_insert_of_mem hv
  have hq4 : G.IsNClique 4 q.support := ⟨hq, q.card_support⟩
  have hedges : 5 ≤ edgeCount G q.support := by
    rw [edgeCount_clique hq, q.card_support]
    decide
  exact p.nine_triangle_universal_factor q hd hleaf htri hedges
    ⟨v, hv, fun _ hw ↦ clique_replace_of_degree_three hq4 hz hv3 hw⟩

variable [Fintype V]

theorem TriangleChain.Strong.terminal_degree_eq_zero_of_nine_clique
    {c : TriangleChain G} (hc : c.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hqcl : G.IsClique b)
    (ht : 9 ≤ contacts G c.triangle b) : degreeIn G c.terminal b = 0 := by
  by_contra hh
  have hpos : 1 ≤ degreeIn G c.terminal b := by omega
  obtain ⟨p, hpLeaf, hpTri, hpSupp⟩ := hc.exists_paw
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  have hd : Disjoint p.support q.support := by
    rw [hpSupp, hq]
    exact c.property.remainder_disjoint.mono le_rfl (c.blockPartition.block_subset hb)
  have hf := p.clique_nine_triangle_factor q hd (by rw [hq]; exact hqcl)
    (by rw [hpLeaf, hq]; exact hpos) (by rw [hpTri, hq]; exact ht)
  rw [hpSupp, hq] at hf
  exact c.no_local_factor hcard hn hb hf

end Erdos577

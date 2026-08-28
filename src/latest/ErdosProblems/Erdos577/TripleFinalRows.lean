import ErdosProblems.Erdos577.TripleOrientedLabels

/-! The new leaf has rows one and zero on the two changed blocks. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {u : V}

lemma HeavyChoice.third_first_degree (h : HeavyChoice c p q a u) :
    degreeIn G (p.vertices 3) (insert (p.vertices 2) (q.support.erase (q 3))) = 1 := by
  have hout : p.vertices 2 ∉ q.support.erase (q 3) :=
    fun hh ↦ h.toConfiguration.paw_outside 2 (mem_erase.mp hh).2
  have hzero : degreeIn G (p.vertices 3) (q.support.erase (q 3)) = 0 := by
    apply (degreeIn_eq_zero_iff _ _).mpr
    intro v hv
    obtain ⟨i, rfl⟩ := (q.mem_support _).mp (mem_erase.mp hv).2
    exact h.third_row i
  rw [degreeIn_insert G _ _ hout, if_pos p.edge23.symm, hzero]

lemma HeavyChoice.third_second_degree (h : HeavyChoice c p q a u) :
    degreeIn G (p.vertices 3) (insert (q 3) (a.erase u)) = 0 := by
  apply (degreeIn_eq_zero_iff _ _).mpr
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact h.third_row 3
  · exact (degreeIn_eq_zero_iff _ _).mp h.third_zero v (mem_erase.mp hv).2

lemma HeavyChoice.original_block_of_third_three (h : HeavyChoice c p q a u)
    {d : TriangleChain G}
    (hblocks : d.blocks = (c.blocks \ {q.support, a}) ∪
      {insert (p.vertices 2) (q.support.erase (q 3)), insert (q 3) (a.erase u)})
    {s : Finset V} (hs : s ∈ d.blocks) (hrow : 3 ≤ degreeIn G (p.vertices 3) s) :
    s ∈ c.blocks ∧ s ≠ q.support ∧ s ≠ a := by
  rw [hblocks] at hs
  rcases mem_union.mp hs with hs | hs
  · obtain ⟨hm, hn⟩ := mem_sdiff.mp hs
    simp only [mem_insert, mem_singleton, not_or] at hn
    exact ⟨hm, hn⟩
  · rcases mem_insert.mp hs with rfl | hs
    · rw [h.third_first_degree] at hrow
      omega
    · have he := mem_singleton.mp hs
      rw [he, h.third_second_degree] at hrow
      omega

end Erdos577.UniversalTriple

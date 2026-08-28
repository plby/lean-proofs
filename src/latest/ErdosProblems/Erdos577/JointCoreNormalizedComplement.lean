import ErdosProblems.Erdos577.JointCoreRefinedLabels
import ErdosProblems.Erdos577.TwoCoreCompleteComplement

/-! The optional pattern28 normalization has a complete primary complement. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma SourcePattern.normalized_primary_clique (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : SourcePattern 1 p q)
    (hb1 : G.Adj (p.vertices 2) (q 1)) :
    G.IsNClique 4 ((p.triangle ∪ q.support) \ {p.center, q 2, q 3}) := by
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have ht : ({p.center, q 2, q 3} : Finset V) = {q 2, q 3, p.center} := by
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hs : q.support \ {q 2, q 3} = {q 0, q 1} := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
      obtain ⟨i, rfl⟩ := (q.mem_support v).mp hv
      fin_cases i
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_singleton_self _)
      · exact False.elim (hn (mem_insert_self _ _))
      · exact False.elim (hn (mem_insert_of_mem (mem_singleton_self _)))
    · intro hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_sdiff.mpr ⟨hm 0, by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨q.injective.ne (by decide), q.injective.ne (by decide)⟩⟩
      · exact mem_sdiff.mpr ⟨hm 1, by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨q.injective.ne (by decide), q.injective.ne (by decide)⟩⟩
  rw [ht, TwoCore.core_complement_eq p q.support hd (q 2) (q 3) (hm 2) (hm 3), hs]
  have hc0 := (h.2.2 3 0 (by decide)).1 (by decide)
  have hc1 := (h.2.2 3 1 (by decide)).1 (by decide)
  have hb0 := (h.2.2 2 0 (by decide)).1 (by decide)
  have hthree : G.IsNClique 3 {p.vertices 3, q 0, q 1} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hc0, hc1, q.adjacent 0⟩
  apply hthree.insert
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact p.edge23
  · exact hb0
  · exact hb1

end Erdos577.JointCore

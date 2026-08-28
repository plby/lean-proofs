import ErdosProblems.Erdos577.WeightedRows
import ErdosProblems.Erdos577.TripleReplacements
import ErdosProblems.Erdos577.TerminalReplacements
import ErdosProblems.Erdos577.CommonReplacement

/-! The universal and common-neighbor replacements in weighted patterns (10)–(12). -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedPawBlock

omit [DecidableRel G.Adj] in
lemma vertex_not_mem (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (i : Fin 4) : p.vertices i ∉ q.support :=
  fun h ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) h

omit [DecidableRel G.Adj] in
lemma Pattern10.universal (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern10 p q) (u : V) (hu : u ∈ q.support) :
    QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  classical
  have hcl := q.clique_of_diagonals h.1 h.2.1
  have hrow := q.degree_ge_mask (p.vertices 2) 14 h.2.2.2.2
  have hsum : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  rw [hsum] at hrow
  exact clique_replace_of_degree_three hcl (vertex_not_mem p q hd 2) hrow hu

omit [DecidableRel G.Adj] in
lemma Pattern11.universal (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern11 p q) (u : V) (hu : u ∈ q.support) :
    QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  apply (show QuadOn G q.support from ⟨q, rfl⟩).replace_of_complete
    (vertex_not_mem p q hd 2) ?_ hu
  intro w hw
  obtain ⟨j, rfl⟩ := (q.mem_support w).mp hw
  exact h.2.2.1.full p q 2 j

omit [DecidableRel G.Adj] in
lemma Pattern12.universal (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern12 p q) (u : V) (hu : u ∈ q.support) :
    QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  classical
  apply (show QuadOn G q.support from ⟨q, rfl⟩).universal_replace_of_nonadjacent_degree
    (vertex_not_mem p q hd 2) (h.2.2.1.three_le p q 2) ?_ hu
  intro w hw hn
  obtain ⟨j, rfl⟩ := (q.mem_support w).mp hw
  have hbits : ∀ j : Fin 4, (7 : ℕ).testBit j.val = true ↔ j ≠ 3 := by decide +kernel
  have hj : j = 3 := by
    by_contra hj
    exact hn ((h.2.2.1 j).mpr ((hbits j).mpr hj))
  subst j
  rw [q.degreeIn_eq]
  change 3 ≤ 2 + if G.Adj (q 3) (q 1) then 1 else 0
  rw [if_pos h.1.symm]

lemma Pattern10.common_replacement (p : Paw G) (q : Quadrilateral G) (h : Pattern10 p q)
    (z : V) (hz : z ∉ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    CommonReplacement G p.leaf (p.vertices 2) z q.support := by
  obtain ⟨u, hu, hrep⟩ := q.replace_last_three_of_clique z hz
    (q.clique_of_diagonals h.1 h.2.1) hdegree
  have hbits : ∀ j : Fin 4, j ≠ 0 → (14 : ℕ).testBit j.val = true := by decide +kernel
  exact ⟨q u, (q.mem_support _).mpr ⟨u, rfl⟩,
    h.2.2.1.full p q 0 u, h.2.2.2.2 u (hbits u hu), hrep⟩

lemma common_replacement_first_three (p : Paw G) (q : Quadrilateral G)
    (hdiag : G.Adj (q 1) (q 3)) (hrow0 : Row p q 0 7)
    (hrow2 : ∀ j : Fin 4, j ≠ 3 → G.Adj (p.vertices 2) (q j))
    (z : V) (hz : z ∉ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    CommonReplacement G p.leaf (p.vertices 2) z q.support := by
  obtain ⟨u, hu, hrep⟩ := q.replace_first_three_of_diagonal z hz hdiag hdegree
  have hbits : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
  exact ⟨q u, (q.mem_support _).mpr ⟨u, rfl⟩,
    (hrow0 u).mpr (hbits u hu), hrow2 u hu, hrep⟩

lemma Pattern11.common_replacement (p : Paw G) (q : Quadrilateral G) (h : Pattern11 p q)
    (z : V) (hz : z ∉ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    CommonReplacement G p.leaf (p.vertices 2) z q.support := by
  exact common_replacement_first_three p q h.1 h.2.1
    (fun j _ ↦ h.2.2.1.full p q 2 j) z hz hdegree

lemma Pattern12.common_replacement (p : Paw G) (q : Quadrilateral G) (h : Pattern12 p q)
    (z : V) (hz : z ∉ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    CommonReplacement G p.leaf (p.vertices 2) z q.support := by
  apply common_replacement_first_three p q h.1 h.2.1 ?_ z hz hdegree
  intro j hj
  apply (h.2.2.1 j).mpr
  have hbits : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
  exact hbits j hj

end WeightedPawBlock

end Erdos577

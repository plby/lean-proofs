import ErdosProblems.Erdos76.HypergraphGreedyColoring
import Mathlib.Tactic

/-! # Inserting a dummy vertex into one hyperedge -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

def insertToEdge (H : FiniteHypergraph V E) (e : E) (d : V)
    (hd : d ∈ H.vertexSet) : FiniteHypergraph V E where
  vertexSet := H.vertexSet
  support f := if f = e then insert d (H.support f) else H.support f
  support_subset_vertexSet f := by
    by_cases hf : f = e
    · simpa only [if_pos hf] using insert_subset hd (H.support_subset_vertexSet f)
    · simpa only [if_neg hf] using H.support_subset_vertexSet f

@[simp] theorem insertToEdge_support_self (H : FiniteHypergraph V E) (e : E) (d : V)
    (hd : d ∈ H.vertexSet) : (insertToEdge H e d hd).support e = insert d (H.support e) := by
  simp [insertToEdge]

theorem insertToEdge_support_other (H : FiniteHypergraph V E) (e f : E) (d : V)
    (hd : d ∈ H.vertexSet) (hfe : f ≠ e) :
    (insertToEdge H e d hd).support f = H.support f := by
  simp [insertToEdge, hfe]

theorem insertToEdge_mem_support (H : FiniteHypergraph V E) (e f : E) (d x : V)
    (hd : d ∈ H.vertexSet) : x ∈ (insertToEdge H e d hd).support f ↔
      x ∈ H.support f ∨ (f = e ∧ x = d) := by
  by_cases hf : f = e <;> simp [insertToEdge, hf, or_comm]

/-- Only the newly inserted dummy gains one incidence. -/
theorem insertToEdge_edgeDegree (H : FiniteHypergraph V E) (e : E) (d x : V)
    (hd : d ∈ H.vertexSet) (hfresh : d ∉ H.support e) :
    (insertToEdge H e d hd).edgeDegree x = H.edgeDegree x + if x = d then 1 else 0 := by
  classical
  by_cases hxd : x = d
  · subst x
    have hfilter : (univ.filter fun f ↦ d ∈ (insertToEdge H e d hd).support f) =
        insert e (univ.filter fun f ↦ d ∈ H.support f) := by
      ext f
      simp [insertToEdge_mem_support, or_comm]
    unfold edgeDegree
    rw [hfilter, card_insert_of_notMem (by simp [hfresh])]
    simp
  · have hfilter : (univ.filter fun f ↦ x ∈ (insertToEdge H e d hd).support f) =
        (univ.filter fun f ↦ x ∈ H.support f) := by
      ext f
      simp [insertToEdge_mem_support, hxd]
    simp only [edgeDegree, hfilter, if_neg hxd, add_zero]

theorem insertToEdge_pool_load (H : FiniteHypergraph V E) (e : E) (d : V)
    (hd : d ∈ H.vertexSet) (hfresh : d ∉ H.support e) (P : Finset V) :
    (∑ x ∈ P, (insertToEdge H e d hd).edgeDegree x) =
      (∑ x ∈ P, H.edgeDegree x) + if d ∈ P then 1 else 0 := by
  simp_rw [insertToEdge_edgeDegree H e d _ hd hfresh]
  rw [sum_add_distrib]
  simp

/-- Inserting into just one indexed edge increases any codegree by at most one. -/
theorem insertToEdge_pairDegree_le_add_one (H : FiniteHypergraph V E)
    (e : E) (d x y : V) (hd : d ∈ H.vertexSet) :
    (insertToEdge H e d hd).edgePairDegree x y ≤ H.edgePairDegree x y + 1 := by
  classical
  unfold edgePairDegree
  have hsub : (univ.filter fun f ↦ x ∈ (insertToEdge H e d hd).support f ∧
      y ∈ (insertToEdge H e d hd).support f) ⊆
      insert e (univ.filter fun f ↦ x ∈ H.support f ∧ y ∈ H.support f) := by
    intro f hf
    by_cases hfe : f = e
    · exact mem_insert.mpr (Or.inl hfe)
    · apply mem_insert_of_mem
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      simpa only [insertToEdge_support_other H e f d hd hfe] using (mem_filter.mp hf).2
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem insertToEdge_pairDegree_eq_of_ne (H : FiniteHypergraph V E)
    (e : E) (d x y : V) (hd : d ∈ H.vertexSet) (hxd : x ≠ d) (hyd : y ≠ d) :
    (insertToEdge H e d hd).edgePairDegree x y = H.edgePairDegree x y := by
  classical
  unfold edgePairDegree
  congr 1
  ext f
  simp [insertToEdge_mem_support, hxd, hyd]

theorem insertToEdge_pairDegree_eq_of_not_mem (H : FiniteHypergraph V E)
    (e : E) (d y : V) (hd : d ∈ H.vertexSet) (hyd : y ≠ d) (hy : y ∉ H.support e) :
    (insertToEdge H e d hd).edgePairDegree d y = H.edgePairDegree d y := by
  classical
  unfold edgePairDegree
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and]
  by_cases hfe : f = e
  · subst f
    simp [insertToEdge, hyd, hy]
  · simp [insertToEdge, hfe]

theorem edgePairDegree_symm (H : FiniteHypergraph V E) (x y : V) :
    H.edgePairDegree x y = H.edgePairDegree y x := by
  classical
  simp only [edgePairDegree, and_comm]

/-- The availability conditions suffice to preserve maximum degree and
distinct-vertex codegree bounds after one insertion. -/
theorem insertToEdge_preserves_degree_and_pairDegree (H : FiniteHypergraph V E)
    (e : E) (d : V) (hd : d ∈ H.vertexSet) (hfresh : d ∉ H.support e)
    (D L : ℕ) (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hddeg : H.edgeDegree d < D)
    (hpair : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L)
    (hslack : ∀ x ∈ H.support e, H.edgePairDegree x d < L) :
    (∀ v ∈ (insertToEdge H e d hd).vertexSet,
      (insertToEdge H e d hd).edgeDegree v ≤ D) ∧
    (∀ x ∈ (insertToEdge H e d hd).vertexSet,
      ∀ y ∈ (insertToEdge H e d hd).vertexSet, x ≠ y →
        (insertToEdge H e d hd).edgePairDegree x y ≤ L) := by
  constructor
  · intro v hv
    rw [insertToEdge_edgeDegree H e d v hd hfresh]
    by_cases hvd : v = d
    · simpa [hvd] using Nat.succ_le_of_lt hddeg
    · simpa only [if_neg hvd, add_zero] using hdeg v hv
  · have hleft : ∀ y ∈ H.vertexSet, y ≠ d →
        (insertToEdge H e d hd).edgePairDegree d y ≤ L := by
      intro y hy hyd
      by_cases hye : y ∈ H.support e
      · have hcodeg : H.edgePairDegree d y < L := by
          rw [edgePairDegree_symm]
          exact hslack y hye
        exact (insertToEdge_pairDegree_le_add_one H e d d y hd).trans (by omega)
      · rw [insertToEdge_pairDegree_eq_of_not_mem H e d y hd hyd hye]
        exact hpair d hd y hy hyd.symm
    intro x hx y hy hxy
    by_cases hxd : x = d
    · subst x
      exact hleft y hy hxy.symm
    · by_cases hyd : y = d
      · subst y
        rw [edgePairDegree_symm]
        exact hleft x hx hxd
      · rw [insertToEdge_pairDegree_eq_of_ne H e d x y hd hxd hyd]
        exact hpair x hx y hy hxy

theorem insertToEdge_preserves_rank (H : FiniteHypergraph V E)
    (e : E) (d : V) (hd : d ∈ H.vertexSet) (R : ℕ)
    (hbound : H.IsBounded R) (hroom : (H.support e).card < R) :
    (insertToEdge H e d hd).IsBounded R := by
  intro f
  by_cases hfe : f = e
  · subst f
    rw [insertToEdge_support_self]
    exact (card_insert_le _ _).trans (by omega)
  · rw [insertToEdge_support_other H e f d hd hfe]
    exact hbound f

theorem insertToEdge_support_card (H : FiniteHypergraph V E)
    (e f : E) (d : V) (hd : d ∈ H.vertexSet) (hfresh : d ∉ H.support e) :
    ((insertToEdge H e d hd).support f).card =
      (H.support f).card + if f = e then 1 else 0 := by
  by_cases hfe : f = e
  · subst f
    simp [insertToEdge_support_self, card_insert_of_notMem hfresh]
  · simp only [insertToEdge_support_other H e f d hd hfe, if_neg hfe, add_zero]

theorem insertToEdge_support_inter_card (H : FiniteHypergraph V E)
    (e f : E) (d : V) (hd : d ∈ H.vertexSet) (hfresh : d ∉ H.support e) (P : Finset V) :
    ((insertToEdge H e d hd).support f ∩ P).card =
      (H.support f ∩ P).card + if f = e ∧ d ∈ P then 1 else 0 := by
  by_cases hfe : f = e
  · subst f
    rw [insertToEdge_support_self]
    by_cases hdP : d ∈ P
    · rw [insert_inter_of_mem hdP, card_insert_of_notMem (by simp [hfresh])]
      simp [hdP]
    · rw [insert_inter_of_notMem hdP]
      simp [hdP]
  · simp only [insertToEdge_support_other H e f d hd hfe, hfe, false_and,
      if_false, add_zero]

theorem support_subset_insertToEdge (H : FiniteHypergraph V E)
    (e f : E) (d : V) (hd : d ∈ H.vertexSet) :
    H.support f ⊆ (insertToEdge H e d hd).support f := by
  intro x hx
  exact (insertToEdge_mem_support H e f d x hd).mpr (Or.inl hx)

#print axioms insertToEdge_edgeDegree
#print axioms insertToEdge_preserves_degree_and_pairDegree
#print axioms insertToEdge_preserves_rank

end Erdos19

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos842.AlonTarsi
import ErdosProblems.Erdos842.Graph
import ErdosProblems.Erdos842.Parity
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Canonical indexed arcs for Erdős Problem 842

The canonical graph has one directed occurrence for each Hamiltonian-cycle edge and one for each
triangle edge.  We retain the two families as a sum type, even if their endpoints were to agree;
this is exactly the indexed-arc model required by the Alon--Tarsi coefficient argument.
-/

open SimpleGraph

namespace Erdos842

/-- One occurrence for every cycle position and one occurrence for every vertex in a triangle.
The latter is interpreted as the outgoing edge in a cyclic orientation of its triangle. -/
abbrev CanonicalOccurrence (n : ℕ) := Fin (3 * n) ⊕ (Fin n × Fin 3)

/-- Cyclic successor on a finite nonempty type.  The empty case is included so that all definitions
are uniform at `n = 0`; it has no inputs. -/
def finCyclicSucc : (m : ℕ) → Fin m → Fin m
  | 0, i => i.elim0
  | _ + 1, i => i + 1

@[simp]
lemma finCyclicSucc_succ (m : ℕ) (i : Fin (m + 1)) :
    finCyclicSucc (m + 1) i = i + 1 := rfl

/-- Tail of a canonical edge occurrence. -/
def canonicalOccurrenceTail (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    CanonicalOccurrence n → Fin (3 * n)
  | .inl i => i
  | .inr jk => triangleCoord.symm jk

/-- Head of a canonical edge occurrence.  Both the spanning cycle and every triangle are oriented
cyclically. -/
def canonicalOccurrenceHead (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    CanonicalOccurrence n → Fin (3 * n)
  | .inl i => finCyclicSucc (3 * n) i
  | .inr jk => triangleCoord.symm (jk.1, jk.2 + 1)

/-- The canonical occurrences packaged for the indexed-arc parity API. -/
def canonicalIndexedArcs (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Parity.IndexedArcs (Fin (3 * n)) (CanonicalOccurrence n) where
  tail := canonicalOccurrenceTail n triangleCoord
  head := canonicalOccurrenceHead n triangleCoord

@[simp]
lemma canonicalIndexedArcs_tail (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (a : CanonicalOccurrence n) :
    (canonicalIndexedArcs n triangleCoord).tail a = canonicalOccurrenceTail n triangleCoord a :=
  rfl

@[simp]
lemma canonicalIndexedArcs_head (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (a : CanonicalOccurrence n) :
    (canonicalIndexedArcs n triangleCoord).head a = canonicalOccurrenceHead n triangleCoord a :=
  rfl

lemma cycleGraph_adj_iff_finCyclicSucc {m : ℕ} (hm : 3 ≤ m) (u v : Fin m) :
    (cycleGraph m).Adj u v ↔ finCyclicSucc m u = v ∨ finCyclicSucc m v = u := by
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => omega
      | succ m =>
          cases m with
          | zero => omega
          | succ k =>
              rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add']
              simp only [finCyclicSucc_succ]
              aesop

lemma fin_three_cyclic_adj {i j : Fin 3} (hij : i ≠ j) :
    i + 1 = j ∨ j + 1 = i := by
  fin_omega

/-- Every edge of the canonical simple graph is represented by one of the indexed occurrences.
In fact the support is equal to the canonical graph; the inclusion is the direction consumed by
the coloring step. -/
lemma canonicalGraph_le_occurrenceSupport (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    canonicalGraph n triangleCoord ≤
      occurrenceSupport (canonicalOccurrenceTail n triangleCoord)
        (canonicalOccurrenceHead n triangleCoord) := by
  by_cases hn : n = 0
  · subst n
    intro u
    exact u.elim0
  · have hthree : 3 ≤ 3 * n := by omega
    intro u v huv
    have hne : u ≠ v := huv.ne
    rw [canonicalGraph, SimpleGraph.sup_adj] at huv
    rw [occurrenceSupport_adj]
    refine ⟨hne, ?_⟩
    rcases huv with hcycle | htriangle
    · rw [cycleGraph_adj_iff_finCyclicSucc hthree] at hcycle
      rcases hcycle with h | h
      · exact Or.inl ⟨Sum.inl u, rfl, h⟩
      · exact Or.inr ⟨Sum.inl v, rfl, h⟩
    · rw [triangleFactor_adj] at htriangle
      obtain ⟨huv, hfirst⟩ := htriangle
      let ui := triangleCoord u
      let vi := triangleCoord v
      have hsecond : ui.2 ≠ vi.2 := by
        intro h
        apply huv
        apply triangleCoord.injective
        exact Prod.ext hfirst h
      rcases fin_three_cyclic_adj hsecond with h | h
      · have hp : (ui.1, ui.2 + 1) = vi := by
          apply Prod.ext
          · exact hfirst
          · exact h
        exact Or.inl ⟨Sum.inr ui, by simp [canonicalOccurrenceTail, ui], by
          simp only [canonicalOccurrenceHead]
          rw [hp]
          exact triangleCoord.symm_apply_apply v⟩
      · have hp : (vi.1, vi.2 + 1) = ui := by
          apply Prod.ext
          · exact hfirst.symm
          · exact h
        exact Or.inr ⟨Sum.inr vi, by simp [canonicalOccurrenceTail, vi], by
          simp only [canonicalOccurrenceHead]
          rw [hp]
          exact triangleCoord.symm_apply_apply u⟩

/-- Every indexed occurrence is an edge of the canonical simple graph. -/
lemma occurrenceSupport_le_canonicalGraph (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    occurrenceSupport (canonicalOccurrenceTail n triangleCoord)
        (canonicalOccurrenceHead n triangleCoord) ≤
      canonicalGraph n triangleCoord := by
  by_cases hn : n = 0
  · subst n
    intro u
    exact u.elim0
  · have hthree : 3 ≤ 3 * n := by omega
    intro u v huv
    rw [occurrenceSupport_adj] at huv
    obtain ⟨-, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩ := huv
    · subst u
      subst v
      cases a with
      | inl i =>
          rw [canonicalGraph, SimpleGraph.sup_adj]
          exact Or.inl ((cycleGraph_adj_iff_finCyclicSucc hthree _ _).mpr (Or.inl rfl))
      | inr jk =>
          rw [canonicalGraph, SimpleGraph.sup_adj]
          apply Or.inr
          rw [triangleFactor_adj]
          constructor
          · intro heq
            have := congrArg triangleCoord heq
            simpa [canonicalOccurrenceTail, canonicalOccurrenceHead] using congrArg Prod.snd this
          · simp [canonicalOccurrenceTail, canonicalOccurrenceHead]
    · subst u
      subst v
      cases a with
      | inl i =>
          rw [canonicalGraph, SimpleGraph.sup_adj]
          exact Or.inl ((cycleGraph_adj_iff_finCyclicSucc hthree _ _).mpr (Or.inr rfl))
      | inr jk =>
          rw [canonicalGraph, SimpleGraph.sup_adj]
          apply Or.inr
          rw [triangleFactor_adj]
          constructor
          · intro heq
            have := congrArg triangleCoord heq
            simpa [canonicalOccurrenceTail, canonicalOccurrenceHead] using congrArg Prod.snd this
          · simp [canonicalOccurrenceTail, canonicalOccurrenceHead]

@[simp]
theorem occurrenceSupport_canonicalOccurrence_eq (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    occurrenceSupport (canonicalOccurrenceTail n triangleCoord)
        (canonicalOccurrenceHead n triangleCoord) =
      canonicalGraph n triangleCoord :=
  le_antisymm (occurrenceSupport_le_canonicalGraph n triangleCoord)
    (canonicalGraph_le_occurrenceSupport n triangleCoord)

/-- There is exactly one cycle occurrence and one triangle occurrence leaving each vertex. -/
lemma canonicalOccurrence_outdegree_two (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (v : Fin (3 * n)) :
    ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
      canonicalOccurrenceTail n triangleCoord a = v).card = 2 := by
  classical
  have hfilter :
      ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
          canonicalOccurrenceTail n triangleCoord a = v) =
        {Sum.inl v, Sum.inr (triangleCoord v)} := by
    apply Finset.ext
    intro a
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    cases a with
    | inl i =>
        simp [canonicalOccurrenceTail]
    | inr jk =>
        simpa [canonicalOccurrenceTail] using
          (triangleCoord.symm_apply_eq (x := jk) (y := v))
  rw [hfilter]
  simp

/-- Indexed-arcs formulation of `canonicalOccurrence_outdegree_two`, ready for the parity
coefficient identity. -/
lemma canonicalIndexedArcs_outdegree_two (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (v : Fin (3 * n)) :
    ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
      (canonicalIndexedArcs n triangleCoord).tail a = v).card = 2 := by
  have htail : (canonicalIndexedArcs n triangleCoord).tail =
      canonicalOccurrenceTail n triangleCoord := rfl
  rw [htail]
  exact canonicalOccurrence_outdegree_two n triangleCoord v

/-- Rotate each occurrence index once around its cycle or directed triangle. -/
def canonicalOccurrenceRotate (n : ℕ) : Equiv.Perm (CanonicalOccurrence n) :=
  (finRotate (3 * n)).sumCongr ((Equiv.refl (Fin n)).prodCongr (finRotate 3))

lemma finCyclicSucc_eq_finRotate (m : ℕ) (i : Fin m) :
    finCyclicSucc m i = finRotate m i := by
  cases m with
  | zero => exact i.elim0
  | succ m => simp [finCyclicSucc, finRotate_apply]

/-- Rotating an occurrence turns its tail into its head. -/
lemma canonicalOccurrenceTail_rotate (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (a : CanonicalOccurrence n) :
    canonicalOccurrenceTail n triangleCoord (canonicalOccurrenceRotate n a) =
      canonicalOccurrenceHead n triangleCoord a := by
  cases a with
  | inl i =>
      simpa [canonicalOccurrenceRotate, canonicalOccurrenceTail, canonicalOccurrenceHead,
        finCyclicSucc_eq_finRotate]
  | inr tj =>
      change triangleCoord.symm (tj.1, finRotate 3 tj.2) =
        triangleCoord.symm (tj.1, tj.2 + 1)
      rw [finRotate_apply]

/-- There is exactly one incoming cycle occurrence and one incoming triangle occurrence at every
canonical vertex. -/
lemma canonicalIndexedArcs_indegree_two (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (v : Fin (3 * n)) :
    ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
      (canonicalIndexedArcs n triangleCoord).head a = v).card = 2 := by
  classical
  let rotate := canonicalOccurrenceRotate n
  have hcard :
      ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
          (canonicalIndexedArcs n triangleCoord).head a = v).card =
        ((Finset.univ : Finset (CanonicalOccurrence n)).filter fun a ↦
          (canonicalIndexedArcs n triangleCoord).tail a = v).card := by
    apply Finset.card_bij (fun a _ ↦ rotate a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (canonicalOccurrenceTail_rotate n triangleCoord a).trans ha
    · intro a ha b hb hab
      exact rotate.injective hab
    · intro b hb
      refine ⟨rotate.symm b, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      have htail := canonicalOccurrenceTail_rotate n triangleCoord (rotate.symm b)
      change canonicalOccurrenceTail n triangleCoord b = v at hb
      change canonicalOccurrenceHead n triangleCoord (rotate.symm b) = v
      simp only [rotate, Equiv.apply_symm_apply] at htail
      rw [← htail]
      exact hb
  rw [hcard]
  exact canonicalIndexedArcs_outdegree_two n triangleCoord v

/-- The occurrence family has twice as many elements as the canonical vertex type. -/
lemma canonicalOccurrence_card (n : ℕ) :
    Fintype.card (CanonicalOccurrence n) = 2 * Fintype.card (Fin (3 * n)) := by
  simp [CanonicalOccurrence]
  omega

/-- The indexed-arcs polynomial is definitionally the occurrence polynomial used by the
Alon--Tarsi coloring interface. -/
lemma canonicalIndexedArcs_polynomial (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    (canonicalIndexedArcs n triangleCoord).polynomial =
      occurrencePolynomial (canonicalOccurrenceTail n triangleCoord)
        (canonicalOccurrenceHead n triangleCoord) := rfl

/-- The two central-exponent definitions used by the parity and coloring APIs agree. -/
lemma canonicalIndexedArcs_centralExponent (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    (canonicalIndexedArcs n triangleCoord).centralExponent =
      centralExponent (V := Fin (3 * n)) := rfl

end Erdos842

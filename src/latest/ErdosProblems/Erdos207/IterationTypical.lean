/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Vortex
import ErdosProblems.Erdos207.AbsorberWellSpread

/-!
# Exact finite iteration-typicality

This is the finite, quantified version of KSSS Definition 10.1.  It records
degree regularity between consecutive vortex levels and all bounded rooted
edge-pattern extension counts needed by the master iteration.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A nonnegative quantity lies in the multiplicative `1 ± ξ` window around
its target value.  Subtraction is the truncated subtraction of `ℝ≥0`. -/
def WithinMultiplicativeError (ξ actual target : ℝ≥0) : Prop :=
  (1 - ξ) * target ≤ actual ∧ actual ≤ (1 + ξ) * target

lemma WithinMultiplicativeError.mono
    {ξ ξ' actual target : ℝ≥0}
    (h : WithinMultiplicativeError ξ actual target) (hξ : ξ ≤ ξ') :
    WithinMultiplicativeError ξ' actual target := by
  constructor
  · calc
      (1 - ξ') * target ≤ (1 - ξ) * target := by
        gcongr
      _ ≤ actual := h.1
  · calc
      actual ≤ (1 + ξ) * target := h.2
      _ ≤ (1 + ξ') * target := by gcongr

/-- Neighbors of `v` which lie in a prescribed finite vertex set. -/
noncomputable def neighborsIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (v : V) : Finset V := by
  classical
  exact U.filter fun w ↦ G.Adj v w

@[simp]
lemma mem_neighborsIn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {v w : V} :
    w ∈ neighborsIn G U v ↔ w ∈ U ∧ G.Adj v w := by
  classical
  simp [neighborsIn]

/-- The edge set of a finite graph as an explicitly ambient finite set. -/
noncomputable def graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact univ.filter fun e ↦ e ∈ G.edgeSet

@[simp]
lemma mem_graphEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

/-- Vertices in `U` which extend every edge of `Q` to a triangle of `A`.
The formulation via `tripleEdgeFinset` avoids choosing an ordering of the
two endpoints of a `Sym2` edge. -/
noncomputable def iterationExtensionVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) : Finset V := by
  classical
  exact U.filter fun u ↦ ∀ e ∈ graphEdges Q,
    ∃ T ∈ A, u ∈ T.1 ∧ e ∈ tripleEdgeFinset T

@[simp]
lemma mem_iterationExtensionVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {Q : SimpleGraph V} {U : Finset V} {u : V} :
    u ∈ iterationExtensionVertices A Q U ↔
      u ∈ U ∧ ∀ e ∈ graphEdges Q,
        ∃ T ∈ A, u ∈ T.1 ∧ e ∈ tripleEdgeFinset T := by
  classical
  simp [iterationExtensionVertices]

lemma iterationExtensionVertices_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) :
    iterationExtensionVertices A Q U ⊆ U := by
  intro u hu
  exact (mem_iterationExtensionVertices_iff.mp hu).1

lemma iterationExtensionVertices_mono_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {A A' : TripleSystemOn V} (hAA' : A ⊆ A')
    (Q : SimpleGraph V) (U : Finset V) :
    iterationExtensionVertices A Q U ⊆
      iterationExtensionVertices A' Q U := by
  intro u hu
  rw [mem_iterationExtensionVertices_iff] at hu ⊢
  refine ⟨hu.1, ?_⟩
  intro e he
  obtain ⟨T, hTA, huT, heT⟩ := hu.2 e he
  exact ⟨T, hAA' hTA, huT, heT⟩

/-- Exact finite form of KSSS iteration-typicality from stage `k` onward.
The cutoff `h` bounds the number of vertices spanned by every tested edge
pattern. -/
def IsIterationTypical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1))
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (p eta ξ : ℝ≥0) (h : ℕ) : Prop :=
  (∀ i : Fin ell, k.val ≤ i.val →
    (∀ v ∈ W.U i.castSucc,
      WithinMultiplicativeError ξ
        ((neighborsIn G (W.U i.castSucc) v).card : ℝ≥0)
        (p * (W.U i.castSucc).card)) ∧
    (∀ v ∈ W.U i.castSucc,
      WithinMultiplicativeError ξ
        ((neighborsIn G (W.U i.succ) v).card : ℝ≥0)
        (p * (W.U i.succ).card))) ∧
  (∀ i : Fin ell, k.val ≤ i.val →
    ∀ iStar : Fin (ell + 1),
      (iStar = i.castSucc ∨ iStar = i.succ) →
    ∀ Q : SimpleGraph V, Q ≤ G →
      GraphSupportedOn Q (W.U i.castSucc : Set V) →
      (graphSupportFinset Q).card ≤ h →
      WithinMultiplicativeError ξ
        ((iterationExtensionVertices A Q (W.U iStar)).card : ℝ≥0)
        (p ^ (graphSupportFinset Q).card *
          eta ^ (graphEdges Q).card * (W.U iStar).card))

/-- Increasing the error tolerance preserves iteration-typicality. -/
theorem IsIterationTypical.mono_error
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ ξ' : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h) (hξ : ξ ≤ ξ') :
    IsIterationTypical W k G A p eta ξ' h := by
  refine ⟨?_, ?_⟩
  · intro i hki
    exact ⟨fun v hv ↦ (htyp.1 i hki).1 v hv |>.mono hξ,
      fun v hv ↦ (htyp.1 i hki).2 v hv |>.mono hξ⟩
  · intro i hki iStar hiStar Q hQG hQU hQcard
    exact (htyp.2 i hki iStar hiStar Q hQG hQU hQcard).mono hξ

/-- Decreasing the tested pattern-size cutoff preserves typicality. -/
theorem IsIterationTypical.mono_patternCutoff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h h' : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h) (hh : h' ≤ h) :
    IsIterationTypical W k G A p eta ξ h' := by
  refine ⟨htyp.1, ?_⟩
  intro i hki iStar hiStar Q hQG hQU hQcard
  exact htyp.2 i hki iStar hiStar Q hQG hQU (hQcard.trans hh)

end

end Erdos207

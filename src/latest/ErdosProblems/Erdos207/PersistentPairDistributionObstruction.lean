/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialSparsificationStrongLaw

/-! # A persistent prescribed pair obstructs a decaying all-pairs distribution bound

The older interfaces allow diagonal symmetric pairs. They also count edges
reserved outside the initial working graph. Neither kind has a decaying
survival probability. The obstruction below preserves the exact distinction
between that overly strong interface and the final existence problem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsInitialProductBound.persistent_pair_obstruction
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsInitialProductBound L selected p C b) (e : Sym2 V)
    (he : ∀ ω, e ∉ (coveredGraph (selected ω)).edgeSet) : 1 ≤ C * (p + b) := by
  classical
  have hraw := h ∅ {e}
  have hevent : (fun ω ↦ (∅ : TripleSystemOn V) ⊆ selected ω ∧
      ∀ e' ∈ ({e} : Finset (Sym2 V)), e' ∉ (coveredGraph (selected ω)).edgeSet) =
      (fun _ ↦ True) := by
    funext ω
    simp [he ω]
  rw [hevent, L.probability_true] at hraw
  simpa using hraw

theorem IsInitialProductBound.diagonal_obstruction
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsInitialProductBound L selected p C b) (v : V) : 1 ≤ C * (p + b) := by
  apply h.persistent_pair_obstruction s(v, v)
  intro ω he
  exact (coveredGraph (selected ω)).not_isDiag_of_mem_edgeSet he (by simp)

theorem IsStronglyWellDistributed.persistent_pair_obstruction
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b) (e : Sym2 V)
    (he : ∀ ω, e ∉ (coveredGraph (initial ω)).edgeSet) : 1 ≤ C * (p + b) := by
  classical
  have hraw := h ∅ ∅ {e} (by simp)
  have hevent : StrongDistributionEvent initial later ∅ ∅ {e} = (fun _ ↦ True) := by
    funext ω
    simp [StrongDistributionEvent, he ω]
  rw [hevent, L.probability_true] at hraw
  simpa using hraw

theorem not_initialProductBound_of_small_diagonal_budget
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (p C b : ℝ≥0)
    (v : V) (hsmall : C * (p + b) < 1) : ¬ IsInitialProductBound L selected p C b := by
  intro h
  exact (not_lt_of_ge (h.diagonal_obstruction v)) hsmall

end

end Erdos207

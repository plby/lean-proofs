/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTypical

/-!
# Strong well-distributedness for the master iteration

This file gives the exact finite-law version of KSSS Definition 10.2.  The
event simultaneously prescribes initial selected triangles, later selected
triangles, and edges left uncovered by the initial family.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The level of a triangle in the vortex truncated after stage `k`. -/
def Vortex.truncatedLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V) :
    Fin (ell + 1) := min (W.level T) k

lemma Vortex.truncatedLevel_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V) :
    W.truncatedLevel k T ≤ k := min_le_right _ _

lemma Vortex.truncatedLevel_eq_level_of_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V)
    (hTk : W.level T ≤ k) :
    W.truncatedLevel k T = W.level T := min_eq_left hTk

/-- Product scale for prescribed later-stage triangles in strong
well-distributedness. -/
def laterTriangleScale
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0)
    (Dfix : TripleSystemOn V) : ℝ≥0 :=
  ∏ T ∈ Dfix, p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0)

@[simp]
lemma laterTriangleScale_empty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0) :
    laterTriangleScale W k p ∅ = 1 := by
  simp [laterTriangleScale]

/-- The joint event in KSSS Definition 10.2. -/
def StrongDistributionEvent
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (ω : Ω) : Prop :=
  Ifix ⊆ initial ω ∧ Dfix ⊆ later ω ∧
    ∀ e ∈ Efix, e ∉ (coveredGraph (initial ω)).edgeSet

/-- Exact finite-law form of strong `(p,C,b)`-well-distributedness with
respect to the vortex truncated at `k`.  `Ifix` and `Dfix` are required to
be disjoint, encoding the paper's demand that all prescribed triangles are
distinct. -/
def IsStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1))
    (initial later : Ω → TripleSystemOn V)
    (p C b : ℝ≥0) : Prop :=
  ∀ (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)),
    Disjoint Ifix Dfix →
    L.probability (StrongDistributionEvent initial later Ifix Dfix Efix) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card) *
        (p ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b)

/-- Enlarging only the additive error preserves strong
well-distributedness. -/
theorem IsStronglyWellDistributed.mono_additiveError
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b b' : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    (hbb' : b ≤ b') :
    IsStronglyWellDistributed L W k initial later p C b' := by
  intro Ifix Dfix Efix hdisj
  exact (h Ifix Dfix Efix hdisj).trans (by gcongr)

/-- Enlarging the multiplicative error factor preserves strong
well-distributedness. -/
theorem IsStronglyWellDistributed.mono_factor
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C C' b : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    (hCC' : C ≤ C') :
    IsStronglyWellDistributed L W k initial later p C' b := by
  intro Ifix Dfix Efix hdisj
  exact (h Ifix Dfix Efix hdisj).trans (by gcongr)

/-- Combined monotonicity in both error parameters. -/
theorem IsStronglyWellDistributed.mono
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C C' b b' : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    (hCC' : C ≤ C') (hbb' : b ≤ b') :
    IsStronglyWellDistributed L W k initial later p C' b' :=
  (h.mono_factor hCC').mono_additiveError hbb'

/-- Specialization to prescribed initial triangles only. -/
theorem IsStronglyWellDistributed.probability_initial_subset_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    (Ifix : TripleSystemOn V) :
    L.probability (fun ω ↦ Ifix ⊆ initial ω) ≤
      C ^ Ifix.card *
        ((Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card + b) := by
  have hraw := h Ifix ∅ ∅ (by simp)
  have hevent :
      StrongDistributionEvent initial later Ifix ∅ ∅ =
        (fun ω ↦ Ifix ⊆ initial ω) := by
    funext ω
    simp [StrongDistributionEvent]
  rw [hevent] at hraw
  simpa [laterTriangleScale] using hraw

end

end Erdos207

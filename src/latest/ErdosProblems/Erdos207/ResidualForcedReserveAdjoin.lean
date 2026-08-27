/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualReserveAdjoin

/-! # The residual partition exposes reserve edges forced by new triangles -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

theorem FiniteLaw.jointBind_residual_forcedReserve_probability_le_on_support
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (G : SimpleGraph V) (initial later : Ω → TripleSystemOn V)
    (reserve : Ω → Finset (Sym2 V))
    (added : Ω → Ξ → TripleSystemOn V) (required : TripleSystemOn V → Finset (Sym2 V))
    (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω, 0 < L.mass ω → ∀ Q, (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (hrequired : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      ∀ Q, Q ⊆ added ω ξ → required Q ⊆ reserve ω)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset, if IsPackingOn (Dfix \ S) ∧
        (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
        addedBound (Dfix \ S) * L.probability
          (ResidualReserveDistributionEvent initial later reserve Ifix S
            (pendingSurvivalEdges (Dfix \ S) Efix) (required (Dfix \ S))) else 0 := by
  classical
  let Good := fun S : TripleSystemOn V ↦ IsPackingOn (Dfix \ S) ∧
    (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
    Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix
  let Old := fun S : TripleSystemOn V ↦
    ResidualReserveDistributionEvent initial later reserve Ifix S
      (pendingSurvivalEdges (Dfix \ S) Efix) (required (Dfix \ S))
  let Event := fun S : TripleSystemOn V ↦ fun z : Ω × Ξ ↦
    Good S ∧ Old S z.1 ∧ Dfix \ S ⊆ added z.1 z.2
  have hsupport := (show L.SupportedOn (fun ω ↦ 0 < L.mass ω) from fun _ h ↦ h).jointBind
    (Q := fun ω ξ ↦
      (IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
        Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
        ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G) ∧
      ∀ Q, Q ⊆ added ω ξ → required Q ⊆ reserve ω)
    (fun ω hω ξ hξ ↦ ⟨hstruct ω hω ξ hξ, hrequired ω hω ξ hξ⟩)
  have hcover : (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      (L.jointBind K).probability (fun z ↦ ∃ S ∈ Dfix.powerset, Event S z) := by
    apply (L.jointBind K).probability_mono_of_supported hsupport
    intro z hz hevent
    obtain ⟨S, hS, hQ, hG, hQE, hOld, hNew⟩ := residualDistributionEvent_adjoin_partition
      initial later added G Ifix Dfix Efix z hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2 hevent
    exact ⟨S, hS, ⟨hQ, hG, hQE⟩, ⟨hOld, hz.2.2 _ hNew⟩, hNew⟩
  apply hcover.trans ((L.jointBind K).probability_exists_le Dfix.powerset Event |>.trans _)
  apply sum_le_sum
  intro S hS
  change (L.jointBind K).probability (Event S) ≤ if Good S then _ else _
  by_cases hgood : Good S
  · rw [if_pos hgood]
    have hremove : Event S = (fun z ↦ Old S z.1 ∧ Dfix \ S ⊆ added z.1 z.2) := by
      funext z
      simp only [Event, hgood, true_and]
    rw [hremove]
    exact L.jointBind_probability_and_le_on_support K (Old S)
      (fun ω ξ ↦ Dfix \ S ⊆ added ω ξ) (addedBound (Dfix \ S))
      (fun ω hω _ ↦ hadded ω hω (Dfix \ S))
  · rw [if_neg hgood]
    have hzero : Event S = (fun _ ↦ False) := by
      funext z
      simp only [Event, hgood, false_and]
    rw [hzero, FiniteLaw.probability_false]

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedPreliminaryInternalStage

/-!
# A terminal no-op preliminary stage

At the last vortex step no later distribution estimate is needed.  The
preliminary family may therefore be empty: all residual crossing edges are
placed into the augmented reserve, and the internal/link stages do the actual
covering.  This file packages the elementary probability and support facts
for that specialization.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The deterministic one-point preliminary kernel. -/
def noopPreliminaryKernel (Omega : Type*) (_omega : Omega) :
    FiniteLaw PUnit :=
  FiniteLaw.pure PUnit.unit

/-- The no-op preliminary kernel selects no new triangle. -/
def noopPreliminaryAdded
    {Omega V : Type*} [DecidableEq V] (_omega : Omega) (_xi : PUnit) :
    TripleSystemOn V :=
  ∅

/-- Pointwise-good master support supplies all structural hypotheses for the
no-op preliminary kernel.  Its mixed inclusion estimate has bases one and
zero additive error. -/
theorem noopPreliminaryKernel_product_and_structure
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (hpoint : law.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (heven : law.SupportedOn fun omega ↦
      ∀ v, Even ((neighborsIn (G omega) univ v).card)) :
    let Kpre := noopPreliminaryKernel Omega
    let added := @noopPreliminaryAdded Omega V _
    (∀ omega, 0 < law.mass omega → ∀ Q E,
      (Kpre omega).probability (fun z ↦
        Q ⊆ added omega z ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) (W.U k)
          (added omega z)) ≤
        (1 : ℝ≥0) ^ Q.card * (1 : ℝ≥0) ^ E.card + 0) ∧
      (law.jointBind Kpre).SupportedOn (fun z ↦
        (∀ v, Even ((neighborsIn (G z.1) univ v).card)) ∧
        G z.1 ≤ leaveGraph (I z.1 ∪ D z.1) ∧
        ConsistsOfTriangles (G z.1) (A z.1) ∧
        added z.1 z.2 ⊆ A z.1 ∧
        Disjoint (I z.1) (D z.1 ∪ added z.1 z.2) ∧
        IsPackingOn (I z.1 ∪ (D z.1 ∪ added z.1 z.2))) ∧
      (law.jointBind Kpre).SupportedOn (fun z ↦
        AvoidsForbidden (I z.1 ∪ (D z.1 ∪ added z.1 z.2)) F) := by
  dsimp only
  let Kpre := noopPreliminaryKernel Omega
  let added := @noopPreliminaryAdded Omega V _
  refine ⟨?_, ?_, ?_⟩
  · intro omega _hmass Q E
    simpa only [one_pow, one_mul, add_zero] using
      (Kpre omega).probability_le_one (fun z ↦
        Q ⊆ added omega z ∧
          E ⊆ preliminaryResidualCrossingEdges (G omega) (W.U k)
            (added omega z))
  · intro z hz
    have hmasses :=
      (FiniteLaw.jointBind_mass_pos_iff law Kpre z.1 z.2).mp hz
    have hp := hpoint z.1 hmasses.1
    refine ⟨heven z.1 hmasses.1, hp.2.2.2.2.1,
      hp.2.2.2.2.2.1, ?_, ?_, ?_⟩
    · simp only [added, noopPreliminaryAdded, empty_subset]
    · simpa only [added, noopPreliminaryAdded, union_empty] using hp.1
    · simpa only [added, noopPreliminaryAdded, union_empty] using hp.2.1
  · intro z hz
    have hmasses :=
      (FiniteLaw.jointBind_mass_pos_iff law Kpre z.1 z.2).mp hz
    have hp := hpoint z.1 hmasses.1
    simpa only [added, noopPreliminaryAdded, union_empty] using hp.2.2.1

end

end Erdos207

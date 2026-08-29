/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# Final half-way conversion with a containing stopover

A linkage between the source and `C` only requires its terminal frontier to
be contained in `C`.  Exact equality is false for branching target geometry
and is not used to construct the stopover, target-link, or height witnesses.
This file exposes the corresponding source-faithful final conversion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open Blueprint LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Complete an edge-real blueprint by its disjoint reference remainder when
the resulting terminal frontier is merely contained in the chosen stopover.
This is exactly the boundary strength required by `IsLinkageBetween`. -/
theorem exists_halfwayStopover_of_terminalBlueprint_withReference_subset
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (R : Set Gamma.DPath)
    (hRwarp : Gamma.IsWarp R)
    (hcross : ∀ p ∈ U.paths, ∀ q ∈ R,
      Disjoint p.support q.support)
    {C A0 X : Set V}
    (hinitial : U.initialSet ∪ Gamma.initialSet R = Gamma.source)
    (hterminal : U.terminalSet ∪ Gamma.terminalFrontier R ⊆ C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ R, IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayStopover Gamma W C ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C kappa := by
  let W := U.completedFamily hreal R
  have hwarp : Gamma.IsWarp W :=
    U.isWarp_completedFamily hreal hRwarp hcross
  have hUfinite : ∀ p ∈ U.paths,
      ∃ q : DirectedPath.FinitePath
        (Blueprint.imaginaryGraph Gamma Y kappa), p = .inl q := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := hUpure p hp
    exact ⟨q, hpq⟩
  have hRfinite : Gamma.HasFiniteCharacter R := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := hRpure p hp
    exact ⟨q, hpq⟩
  have hfinite : Gamma.HasFiniteCharacter W :=
    U.finiteCharacter_completedFamily hreal hUfinite hRfinite
  have hinitial' : Gamma.initialSet W = Gamma.source := by
    rw [U.initialSet_completedFamily hreal R, hinitial]
  have hterminal' : Gamma.terminalFrontier W ⊆ C := by
    rw [U.terminalFrontier_completedFamily hreal R]
    exact hterminal
  have hlinkage : IsLinkageBetween Gamma Gamma.source C W :=
    ⟨hwarp, hfinite, hinitial', hterminal',
      U.endpointPure_completedFamily hreal hUpure hRpure⟩
  refine ⟨W, ⟨hlinkage, hessential, hunhindered⟩,
    U.linksToTarget_completedFamily hreal R hlinks, ?_⟩
  exact ⟨X, ⟨hXsource, Q, hQwave, hCroof⟩, hXcard⟩

/-- Separator-retaining form of the subset-boundary conversion. -/
theorem exists_separatingHalfwayStopover_of_terminalBlueprint_withReference_subset
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (R : Set Gamma.DPath)
    (hRwarp : Gamma.IsWarp R)
    (hcross : ∀ p ∈ U.paths, ∀ q ∈ R,
      Disjoint p.support q.support)
    {C A0 X : Set V}
    (hinitial : U.initialSet ∪ Gamma.initialSet R = Gamma.source)
    (hterminal : U.terminalSet ∪ Gamma.terminalFrontier R ⊆ C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ R, IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hseparator : IsSeparatorFrom Gamma Gamma.source C)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsSeparatingHalfwayStopover Gamma W C ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C kappa := by
  obtain ⟨W, hstop, htarget, hheight⟩ :=
    exists_halfwayStopover_of_terminalBlueprint_withReference_subset
      U hreal R hRwarp hcross hinitial hterminal hUpure hRpure hessential
      hunhindered hlinks hXsource Q hQwave hCroof hXcard
  exact ⟨W, ⟨hstop, hseparator⟩, htarget, hheight⟩

end CardinalInduction
end Erdos599

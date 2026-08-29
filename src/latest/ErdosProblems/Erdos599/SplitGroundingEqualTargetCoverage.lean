/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualMaximalSupply

/-!
# Target coverage alternatives for the split equal branch

Maximality is routing metadata; the elementary coverage trichotomy is valid
for every selected split auxiliary warp.  An essential terminal is already
rooted along an untouched grounded ladder component, is contacted by an
actual erased route, or belongs to an untouched hanging component.  On the
source-reachable boundary the last case also carries a concrete ambient
source path.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingRootedReachabilityWarp

variable {kappa : Cardinal.{u}}

private abbrev SplitCoverageInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- If no actual canonical route meets a limiting-ladder component, every
edge of that component survives the canonical repaired relation. -/
theorem splitLadderPath_edgeSet_subset_canonicalErasedRepairedEdges_of_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    (W : Popular.XSWarp
      (SplitCoverageInput L hL).lambda (SplitCoverageInput L hL).lambda.target)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (havoid : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet
        Y.support) :
    Y.edgeSet ⊆ canonicalErasedRepairedEdges (SplitCoverageInput L hL) W := by
  let J := SplitCoverageInput L hL
  intro e heY
  have heFamily : e ∈ J.familyEdges := by
    refine ⟨Y, ?_, heY⟩
    simpa only [J, SplitCoverageInput, KappaLadder.splitPopularAuxiliaryInput] using hY
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact heRepaired
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨r, hre⟩ := heBackward
    have hends := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J W r) hre
    exact False.elim <| Set.disjoint_left.1 (havoid r) hends.1
      (Y.edgeSet_subset_support_prod heY).1
  · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
      by_contra heNotConflict
      exact heRepaired (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
      obtain ⟨r, hrf⟩ := hfForward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W r) hrf
      exact False.elim <| Set.disjoint_left.1 (havoid r)
        (htail.symm ▸ hends.1) (Y.edgeSet_subset_support_prod heY).1
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
      obtain ⟨r, hrf⟩ := hfForward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W r) hrf
      exact False.elim <| Set.disjoint_left.1 (havoid r)
        (hhead.symm ▸ hends.2) (Y.edgeSet_subset_support_prod heY).2

/-- An untouched grounded component roots its terminal in the concrete
canonical repaired relation. -/
theorem splitGrounded_ladderPath_terminal_sourceRooted_of_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    (W : Popular.XSWarp
      (SplitCoverageInput L hL).lambda (SplitCoverageInput L hL).lambda.target)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (hgrounded : Y.initial ∈ Gamma.source)
    (havoid : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet
        Y.support)
    {b : V} (hterminal : Y.terminal? = some b) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (SplitCoverageInput L hL) W) a b := by
  have hsurvive :=
    splitLadderPath_edgeSet_subset_canonicalErasedRepairedEdges_of_disjoint
      W Y hY havoid
  cases hpath : Y with
  | inl p =>
      have hfinish : p.finish = b := by
        simpa only [hpath, Path.terminal?_finite, Option.some.injEq] using
          hterminal
      refine ⟨p.start, ?_, ?_⟩
      · simpa only [hpath, Path.initial] using hgrounded
      · have hreach := finitePath_start_reaches_of_mem_support p
          (by simpa only [hpath, Path.edgeSet] using hsurvive)
          p.finish_mem_support
        simpa only [hfinish] using hreach
  | inr r =>
      simp only [hpath, Path.terminal?_ray] at hterminal
      cases hterminal

/-- Exact target-only coverage trichotomy for one essential terminal.

The first case needs no active transaction.  The second case supplies an
actual erased-route contact, rather than a broad decoded-carrier contact.
The third case is the genuine untouched-hanging absorption obligation. -/
theorem splitTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    (W : Popular.XSWarp
      (SplitCoverageInput L hL).lambda (SplitCoverageInput L hL).lambda.target)
    {b : V} (hb : b ∈ (SplitCoverageInput L hL).terminalCut) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (SplitCoverageInput L hL) W) a b) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      ∃ r : WarpPath W,
        ((canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet ∩
          Y.support).Nonempty) ∨
    ∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      PopularAuxiliary.IsHangingPath Gamma Y ∧
      ∀ r : WarpPath W,
        Disjoint
          (canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet
          Y.support := by
  obtain ⟨Y, hYessential, hYterminal⟩ := hb
  by_cases hcontact : ∃ r : WarpPath W,
      ((canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet ∩
        Y.support).Nonempty
  · exact Or.inr <| Or.inl ⟨Y, hYessential, hYterminal, hcontact⟩
  have hdisjoint : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet
        Y.support := by
    intro r
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp (fun h ↦ hcontact ⟨r, h⟩)
  by_cases hgrounded : Y.initial ∈ Gamma.source
  · exact Or.inl <|
      splitGrounded_ladderPath_terminal_sourceRooted_of_disjoint
        W Y hYessential.1 hgrounded hdisjoint hYterminal
  · exact Or.inr <| Or.inr
      ⟨Y, hYessential, hYterminal, hgrounded, hdisjoint⟩


/-- Coverage alternatives on the sound source-reachable terminal boundary.
The untouched hanging case retains the ambient source path witnessing that
this terminal matters to separation. -/
theorem splitReachableTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    (W : Popular.XSWarp
      (SplitCoverageInput L hL).lambda
      (SplitCoverageInput L hL).lambda.target)
    {b : V} (hb : b ∈ splitReachableTerminalCut L hL) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitCoverageInput L hL) W) a b) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      ∃ r : WarpPath W,
        ((canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet ∩
          Y.support).Nonempty) ∨
    ∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      PopularAuxiliary.IsHangingPath Gamma Y ∧
      (∀ r : WarpPath W,
        Disjoint
          (canonicalErasedRoute (SplitCoverageInput L hL) W r).vertexSet
          Y.support) ∧
      ∃ p : FinitePath Gamma.graph,
        p.start ∈ Gamma.source ∧ p.finish = b := by
  rcases splitTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
      W hb.1 with hroot | hcontact | hhanging
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hcontact)
  · obtain ⟨Y, hY, hYterminal, hhang, hdisjoint⟩ := hhanging
    exact Or.inr <| Or.inr
      ⟨Y, hY, hYterminal, hhang, hdisjoint, hb.2⟩

end DWeb.KappaLadder
end Erdos599

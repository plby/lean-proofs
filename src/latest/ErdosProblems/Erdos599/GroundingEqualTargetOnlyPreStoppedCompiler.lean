/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply

/-!
# Target-only pre-stopped compiler for the equal branch

The collision hull is useful for choosing and ordering the maximal decoded
route family, but it is not a sound stopping boundary: a selected route can
have both endpoints in its collision hull.  The actual output boundary is
the essential terminal cut.  The canonical repaired relation is already
adjacent and bi-unique and has no edge leaving that cut.

This file isolates the exact remaining coverage alternatives.  An untouched
grounded limiting-ladder component is automatically rooted because all of
its edges survive.  Every other terminal is either met by an actual
canonical erased route, or is the terminal of an untouched hanging
component.  Thus the active closure has only two genuine transactions to
perform: absorb a route contact, and absorb an untouched hanging initial.
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

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

/-- If no actual canonical route meets a limiting-ladder component, every
edge of that component survives the canonical repaired relation. -/
theorem ladderPath_edgeSet_subset_canonicalErasedRepairedEdges_of_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (havoid : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (EqualInput L hL) W r).vertexSet
        Y.support) :
    Y.edgeSet ⊆ canonicalErasedRepairedEdges (EqualInput L hL) W := by
  let J := EqualInput L hL
  intro e heY
  have heFamily : e ∈ J.familyEdges := by
    refine ⟨Y, ?_, heY⟩
    simpa only [J, EqualInput, KappaLadder.popularAuxiliaryInput] using hY
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
theorem grounded_ladderPath_terminal_sourceRooted_of_disjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (hgrounded : Y.initial ∈ Gamma.source)
    (havoid : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (EqualInput L hL) W r).vertexSet
        Y.support)
    {b : V} (hterminal : Y.terminal? = some b) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (EqualInput L hL) W) a b := by
  have hsurvive :=
    ladderPath_edgeSet_subset_canonicalErasedRepairedEdges_of_disjoint
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
theorem terminalCut_sourceRooted_or_routeContact_or_untouchedHanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {b : V} (hb : b ∈ (EqualInput L hL).terminalCut) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (EqualInput L hL) W) a b) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      ∃ r : WarpPath W,
        ((canonicalErasedRoute (EqualInput L hL) W r).vertexSet ∩
          Y.support).Nonempty) ∨
    ∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      PopularAuxiliary.IsHangingPath Gamma Y ∧
      ∀ r : WarpPath W,
        Disjoint
          (canonicalErasedRoute (EqualInput L hL) W r).vertexSet
          Y.support := by
  obtain ⟨Y, hYessential, hYterminal⟩ := hb
  by_cases hcontact : ∃ r : WarpPath W,
      ((canonicalErasedRoute (EqualInput L hL) W r).vertexSet ∩
        Y.support).Nonempty
  · exact Or.inr <| Or.inl ⟨Y, hYessential, hYterminal, hcontact⟩
  have hdisjoint : ∀ r : WarpPath W,
      Disjoint
        (canonicalErasedRoute (EqualInput L hL) W r).vertexSet
        Y.support := by
    intro r
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp (fun h ↦ hcontact ⟨r, h⟩)
  by_cases hgrounded : Y.initial ∈ Gamma.source
  · exact Or.inl <|
      grounded_ladderPath_terminal_sourceRooted_of_disjoint
        W Y hYessential.1 hgrounded hdisjoint hYterminal
  · exact Or.inr <| Or.inr
      ⟨Y, hYessential, hYterminal, hgrounded, hdisjoint⟩

/-- Nearest target-only active-closure constructor.  Every structural fact
about the concrete maximal repaired relation, including omission of the
reserved source, is discharged internally.  Consumers only handle actual
route contacts and untouched hanging components. -/
theorem ReservedGroundedParent.equalActiveClosureOutput_of_targetOnlyCases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (absorbContact : ∀ (b : V), b ∈ (EqualInput L hL).terminalCut →
      ∀ (Y : Gamma.DPath),
      Y ∈ Gamma.essentialWarpPart L.limitWarp →
      Y.terminal? = some b →
      (∃ r : WarpPath (MaximalWarp M),
        ((canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).vertexSet
          ∩ Y.support).Nonempty) →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (MaximalWarp M)) a b)
    (absorbUntouchedHanging : ∀ (b : V),
      b ∈ (EqualInput L hL).terminalCut →
      ∀ (Y : Gamma.DPath),
      Y ∈ Gamma.essentialWarpPart L.limitWarp →
      Y.terminal? = some b →
      PopularAuxiliary.IsHangingPath Gamma Y →
      (∀ r : WarpPath (MaximalWarp M),
        Disjoint
          (canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).vertexSet
          Y.support) →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (MaximalWarp M)) a b) :
    Nonempty (L.EqualActiveClosureOutput hL) := by
  apply
    ReservedMaximalDecodedActiveSupply.ReservedGroundedParent.equalActiveClosureOutput_of_maximalDecoded_sourceRooted
      R M
  intro b hb
  rcases terminalCut_sourceRooted_or_routeContact_or_untouchedHanging
      (MaximalWarp M) hb with hroot | hcontact | hhanging
  · exact hroot
  · obtain ⟨Y, hY, hYterminal, hcontact⟩ := hcontact
    exact absorbContact b hb Y hY hYterminal hcontact
  · obtain ⟨Y, hY, hYterminal, hhang, hdisjoint⟩ := hhanging
    exact absorbUntouchedHanging b hb Y hY hYterminal hhang hdisjoint

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.ladderPath_edgeSet_subset_canonicalErasedRepairedEdges_of_disjoint
#print axioms Erdos599.DWeb.KappaLadder.terminalCut_sourceRooted_or_routeContact_or_untouchedHanging
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.equalActiveClosureOutput_of_targetOnlyCases

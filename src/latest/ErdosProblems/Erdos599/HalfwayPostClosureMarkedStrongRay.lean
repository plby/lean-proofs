/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureShortcutDegeneracy
import ErdosProblems.Erdos599.FiniteOwnerStrongRay

/-!
# Marked strong edges of the actual closed relation

The marked predicate retains a large roof-filtered hammock. It implies the
original strong-edge predicate, but its converse is neither needed nor
asserted. Once actual shortcut intervals are switching-safe, every unmarked
edge has one finite ambient-row owner. The finite-owner argument proves
infinitely many marked edges and hence the original strong-ray condition.

Reference owners may be rays; arbitrary-reference switching confinement is
used without assuming finite character of the limiting reference.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

def IsFilteredMarkedShortcut
    (A : PostClosureCompressorAssignment T) (x y : V) : Prop :=
  (x, y) ∈ A.actualPostClosureShortcutEdges ∧
    HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp x (.vertex y)
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
      (succ kappa)

theorem IsFilteredMarkedShortcut.isStrong
    {A : PostClosureCompressorAssignment T} {x y : V}
    (h : A.IsFilteredMarkedShortcut x y) :
    IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa x y := by
  obtain ⟨K, hK, hcard⟩ := h.2
  exact ⟨K, hK.1, hcard⟩

theorem actualClosedEdges_common_owner_of_not_marked
    (A : PostClosureCompressorAssignment T)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hswitch : ∀ e (he : e ∈ A.actualPostClosureShortcutEdges),
      IsSwitchingSafe C.ladder.limitWarp (A.actualShortcutIntervalWitness he).path)
    {x y : V} (he : (x, y) ∈ A.actualPostClosureClosedEdges)
    (hnot : ¬A.IsFilteredMarkedShortcut x y) :
    ∃ p ∈ T.interval.ambientInterval, x ∈ p.support ∧ y ∈ p.support := by
  rcases he with hinside | hshortcut
  · have hfamily := hinside.1
    simp only [familyEdges, Set.mem_iUnion] at hfamily
    obtain ⟨p, hp, he⟩ := hfamily
    exact ⟨p, hp, p.edgeSet_subset_support_prod he⟩
  · let W := A.actualShortcutIntervalWitness hshortcut
    have hdeg : IsDegenerate C.ladder.limitWarp W.path (.vertex y) := by
      rcases W.isDegenerate_or_filtered_large hfiltered with hdeg | hlarge
      · exact hdeg
      · exact (hnot ⟨hshortcut, hlarge⟩).elim
    exact W.common_interval_owner_of_degenerate_of_switchingSafe
      (hswitch (x, y) hshortcut) hdeg

theorem actualClosedEdges_filteredMarkedIndices_infinite
    (A : PostClosureCompressorAssignment T)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hswitch : ∀ e (he : e ∈ A.actualPostClosureShortcutEdges),
      IsSwitchingSafe C.ladder.limitWarp (A.actualShortcutIntervalWitness he).path)
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hr : r.edgeSet ⊆ A.actualPostClosureClosedEdges) :
    {n : ℕ | A.IsFilteredMarkedShortcut (r n) (r (n + 1))}.Infinite :=
  edgePredicateIndices_infinite_of_complement_common_finite_owner
    A.IsFilteredMarkedShortcut T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    (fun he hnot ↦ A.actualClosedEdges_common_owner_of_not_marked
      hfiltered hswitch he hnot) r hr

theorem actualClosedEdges_strongEdgeIndices_infinite
    (A : PostClosureCompressorAssignment T)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hswitch : ∀ e (he : e ∈ A.actualPostClosureShortcutEdges),
      IsSwitchingSafe C.ladder.limitWarp (A.actualShortcutIntervalWitness he).path)
    (r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa))
    (hr : r.edgeSet ⊆ A.actualPostClosureClosedEdges) :
    (strongEdgeIndices r).Infinite := by
  apply (A.actualClosedEdges_filteredMarkedIndices_infinite hfiltered hswitch r hr).mono
  intro n hn
  exact hn.isStrong

#print axioms actualClosedEdges_common_owner_of_not_marked
#print axioms actualClosedEdges_filteredMarkedIndices_infinite
#print axioms actualClosedEdges_strongEdgeIndices_infinite

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

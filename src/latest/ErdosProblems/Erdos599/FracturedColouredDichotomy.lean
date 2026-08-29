/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalSafeProjection
import ErdosProblems.Erdos599.OutsideFracturedCanonicalBoundary
import ErdosProblems.Erdos599.ColouredSafeIsolatedReduction

/-!
# Single-source occurrence dichotomy for the actual fractured family

The honest canonical lifts supply a word; literal connector contraction and
singleton-reference promotion give a safe word with its original forward
edges downstairs. Singleton fractured sources use the zero-transition word.
This is single-source existence, not simultaneous distinct-terminal choice
or conversion to the older link-compatible `AltPath` type.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedColouredDichotomy

open Set DirectedPath Alternating
open FracturedDuplication FracturedAssignmentPeel
open FracturedCanonicalBoundary FracturedCanonicalSafeProjection
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Every exposed source of a finite-character fractured family has an
actual fixed-forward safe word, finite to an exposed fractured terminal or
infinite. No distinctness across different source choices is asserted. -/
theorem exists_safe_occurrence_dichotomy
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    {s : V} (hs : s ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y) :
    (∃ Q : InfiniteColouredOccurrenceWord Z.edgeWarp Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) ∨
    (∃ t ∈ Gamma.terminalFrontier Z.paths \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord Z.edgeWarp Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s ∧
        Q.vertex (Fin.last Q.length) = t) := by
  classical
  have hsOff : s ∉ Gamma.vertexSet Y := hboundary.initial_outside hs
  by_cases hsSingleton : s ∈ singletonVertices Z
  · right
    refine ⟨s, ⟨?_, hsOff⟩, FiniteColouredOccurrenceWord.emptyAt s,
      FiniteColouredOccurrenceWord.emptyAt_isIntervalSafe s, rfl, rfl⟩
    exact ⟨Gamma.trivialPath s, hsSingleton, Gamma.terminal?_trivialPath s⟩
  have hsActive := activeInitial_of_not_singleton Z hZfinite hs.1 hsSingleton
  have hsLift := outgoing_mem_initialSet_canonicalActiveLift Z hZfinite hsActive
  have hsLiftOff : outgoing s ∉ (web Gamma Z).vertexSet
      (canonicalPeeledReferenceLift Z Y) := by
    intro hx
    have hproject := project_mem_vertexSet_activeReference_of_mem_canonicalLift Z Y hx
    obtain ⟨p, hp, hsp⟩ := hproject
    exact hsOff ⟨p, activeReference_subset Z Y hp, hsp⟩
  have hsLiftNotInitial : outgoing s ∉ (web Gamma Z).initialSet
      (canonicalPeeledReferenceLift Z Y) := by
    rintro ⟨p, hp, hps⟩
    exact hsLiftOff ⟨p, hp, hps ▸ p.initial_mem_support⟩
  have geometry := canonicalDichotomyGeometry Z hboundary hY
    hZfinite hYfinite hsource hnoJunction
  rcases exists_safe_occurrence_dichotomy_total geometry.forward_isWarp
    geometry.reference_isWarp geometry.forward_finite geometry.reference_finite
    geometry.source_subset geometry.boundary_aligned.1 geometry.boundary_aligned.2
    hsLift hsLiftOff with hInfinite | hFinite
  · obtain ⟨Q, hQ, hfirst, _⟩ := hInfinite
    left
    refine ⟨infiniteSafeProjection Z hY hYfinite Q, ?_, ?_⟩
    · apply infiniteSafeProjection_isIntervalSafe Z hboundary hY hYfinite
        hsource hnoJunction Q hQ
      · simpa only [hfirst] using hsLift
      · simpa only [hfirst] using hsLiftNotInitial
    · rw [infiniteSafeProjection_first, hfirst]
      rfl
  · obtain ⟨t, ht, Q, hQ, hfirst, hlast, _⟩ := hFinite
    have hlastForward : Q.vertex (Fin.last Q.length) ∈
        (web Gamma Z).terminalFrontier (canonicalActiveLift Z) := by
      simpa only [hlast] using ht.1
    have hlastReference : Q.vertex (Fin.last Q.length) ∉
        (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y) := by
      simpa only [hlast] using ht.2
    have hterminal := finiteSafeProjection_terminal_mem Z hboundary hY hYfinite
      hsource hnoJunction Q hlastForward hlastReference
    right
    refine ⟨project t, ⟨?_, ?_⟩, finiteSafeProjection Z hYfinite Q, ?_, ?_, ?_⟩
    · rw [finiteSafeProjection_last, hlast] at hterminal
      obtain ⟨p, hp, hpt⟩ := hterminal.1
      exact ⟨p, hp.1, hpt⟩
    · simpa only [finiteSafeProjection_last, hlast] using hterminal.2
    · apply finiteSafeProjection_isIntervalSafe Z hboundary hY hYfinite
        hsource hnoJunction Q hQ
      · simpa only [hfirst] using hsLift
      · simpa only [hfirst] using hsLiftNotInitial
      · exact hlastForward
      · exact hlastReference
    · rw [finiteSafeProjection_first, hfirst]
      rfl
    · rw [finiteSafeProjection_last, hlast]

/-- For the genuine outside cut, the needed peeled no-junction geometry is
proved from disjointness of the closing set and the reference carrier. -/
theorem exists_outside_safe_occurrence_dichotomy
    {W : Set Gamma.DPath} {X : Set V} (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths)
    (hdisjoint : Disjoint X (Gamma.vertexSet Y))
    {s : V} (hs : s ∈ Gamma.initialSet F.holes.paths \ Gamma.initialSet Y) :
    (∃ Q : InfiniteColouredOccurrenceWord F.holes.edgeWarp Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) ∨
    (∃ t ∈ Gamma.terminalFrontier F.holes.paths \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord F.holes.edgeWarp Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s ∧
        Q.vertex (Fin.last Q.length) = t) :=
  exists_safe_occurrence_dichotomy F.holes hboundary hY F.finiteCharacter
    hYfinite hsource (F.noJunctionOnPeeledReference hboundary hY hdisjoint) hs

#print axioms exists_safe_occurrence_dichotomy
#print axioms exists_outside_safe_occurrence_dichotomy

end Erdos599.Blueprint.LinkageBlueprint.FracturedColouredDichotomy

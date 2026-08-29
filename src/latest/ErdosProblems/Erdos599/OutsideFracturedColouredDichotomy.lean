/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OutsideFracturedCanonicalCutAvoidance
import ErdosProblems.Erdos599.ColouredSafeOccurrenceSemantics

/-!
# An actual outside-cut safe occurrence with its geometric certificates

The output is a finite or infinite coloured word, not an `AltPath`. It has
fixed original forward ownership, the literal endpoint boundary, no internal
cut vertices, and a vertex outside the cut. Distinct-terminal selection for
different sources remains a separate theorem.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp

open Set DirectedPath Alternating FracturedDuplication FracturedAssignmentPeel
open FracturedCanonicalBoundary FracturedCanonicalSafeProjection
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {X : Set V}

/-- Native single-source cut assignment, with every local geometric field
proved for the chosen word. No simultaneous selection is assumed. -/
theorem exists_safeOccurrence_avoiding_cut (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths)
    (hX : Disjoint X (Gamma.vertexSet Y))
    {s : V} (hs : s ∈ Gamma.initialSet F.holes.paths \ Gamma.initialSet Y) :
    ∃ A : CurrentSafeOccurrence F.holes.edgeWarp Y s,
      (∀ t, A.terminal? = some t →
        t ∈ Gamma.terminalFrontier F.holes.paths \ Gamma.vertexSet Y ∧
          A.vertexSet ∩ X ⊆ {s, t}) ∧
      (A.terminal? = none → A.vertexSet ∩ X ⊆ {s}) ∧
      ¬ A.vertexSet ⊆ X := by
  classical
  have hsOff : s ∉ Gamma.vertexSet Y := hboundary.initial_outside hs
  by_cases hsing : s ∈ singletonVertices F.holes
  · let Q : FiniteColouredOccurrenceWord F.holes.edgeWarp Y :=
      FiniteColouredOccurrenceWord.emptyAt s
    refine ⟨.finite s Q (FiniteColouredOccurrenceWord.emptyAt_isIntervalSafe s)
      rfl rfl, ?_, ?_, ?_⟩
    · intro t ht
      have hst : s = t := Option.some.inj ht
      subst t
      refine ⟨⟨⟨Gamma.trivialPath s, hsing, Gamma.terminal?_trivialPath s⟩, hsOff⟩, ?_⟩
      rintro x ⟨hxQ, _⟩
      change x ∈ Q.vertexSet at hxQ
      have hxs : x = s := by simpa [Q] using hxQ
      exact Or.inl hxs
    · simp [CurrentSafeOccurrence.terminal?]
    · intro hsub
      apply F.singleton_not_mem_cut hsing
      exact hsub (show s ∈ Q.vertexSet from ⟨0, rfl⟩)
  have hsActive := activeInitial_of_not_singleton F.holes F.finiteCharacter hs.1 hsing
  have hsLift := outgoing_mem_initialSet_canonicalActiveLift
    F.holes F.finiteCharacter hsActive
  have hsLiftOff : outgoing s ∉ (web Gamma F.holes).vertexSet
      (canonicalPeeledReferenceLift F.holes Y) := by
    intro hx
    obtain ⟨p, hp, hsp⟩ :=
      project_mem_vertexSet_activeReference_of_mem_canonicalLift F.holes Y hx
    exact hsOff ⟨p, activeReference_subset F.holes Y hp, hsp⟩
  have hsLiftNotInitial : outgoing s ∉ (web Gamma F.holes).initialSet
      (canonicalPeeledReferenceLift F.holes Y) := by
    rintro ⟨p, hp, hps⟩
    exact hsLiftOff ⟨p, hp, hps ▸ p.initial_mem_support⟩
  have hnoJunction : NoJunctionOnReference F.holes (activeReference F.holes Y) :=
    F.noJunctionOnPeeledReference hboundary hY hX
  have geometry := canonicalDichotomyGeometry F.holes hboundary hY
    F.finiteCharacter hYfinite hsource hnoJunction
  rcases exists_safe_occurrence_dichotomy_total geometry.forward_isWarp
    geometry.reference_isWarp geometry.forward_finite geometry.reference_finite
    geometry.source_subset geometry.boundary_aligned.1 geometry.boundary_aligned.2
    hsLift hsLiftOff with hInfinite | hFinite
  · obtain ⟨Q, hQ, hfirst, _⟩ := hInfinite
    let P := infiniteSafeProjection F.holes hY hYfinite Q
    have hP : P.IsIntervalSafe :=
      infiniteSafeProjection_isIntervalSafe F.holes hboundary hY hYfinite
        hsource hnoJunction Q hQ
        (by simpa only [hfirst] using hsLift)
        (by simpa only [hfirst] using hsLiftNotInitial)
    have hPfirst : P.vertex 0 = s := by
      rw [infiniteSafeProjection_first, hfirst]
      rfl
    refine ⟨.infinite P hP hPfirst, ?_, ?_, ?_⟩
    · simp [CurrentSafeOccurrence.terminal?]
    · intro _
      change P.vertexSet ∩ X ⊆ {s}
      have hcut := F.infiniteSafeProjection_inter_cut_subset_initial hY hYfinite hX Q
      simpa only [hfirst, project_outgoing] using hcut
    · exact F.infiniteWord_not_vertexSet_subset_cut hX P
  · obtain ⟨t, ht, Q, hQ, hfirst, hlast, _⟩ := hFinite
    have hfirstForward : Q.vertex 0 ∈
        (web Gamma F.holes).initialSet (canonicalActiveLift F.holes) := by
      simpa only [hfirst] using hsLift
    have hlastForward : Q.vertex (Fin.last Q.length) ∈
        (web Gamma F.holes).terminalFrontier (canonicalActiveLift F.holes) := by
      simpa only [hlast] using ht.1
    have hlastReference : Q.vertex (Fin.last Q.length) ∉
        (web Gamma F.holes).vertexSet (canonicalPeeledReferenceLift F.holes Y) := by
      simpa only [hlast] using ht.2
    let P := finiteSafeProjection F.holes hYfinite Q
    have hP : P.IsIntervalSafe :=
      finiteSafeProjection_isIntervalSafe F.holes hboundary hY hYfinite
        hsource hnoJunction Q hQ hfirstForward
        (by simpa only [hfirst] using hsLiftNotInitial)
        hlastForward hlastReference
    have hPfirst : P.vertex 0 = s := by
      rw [finiteSafeProjection_first, hfirst]
      rfl
    have hPlast : P.vertex (Fin.last P.length) = project t := by
      rw [finiteSafeProjection_last, hlast]
    have hterminal := finiteSafeProjection_terminal_mem F.holes hboundary hY hYfinite
      hsource hnoJunction Q hlastForward hlastReference
    refine ⟨.finite (project t) P hP hPfirst hPlast, ?_, ?_, ?_⟩
    · intro v hv
      have htv : project t = v := Option.some.inj hv
      subst v
      have hterm : project t ∈
          Gamma.terminalFrontier (activePaths F.holes) \ Gamma.vertexSet Y := by
        simpa only [finiteSafeProjection_last, hlast] using hterminal
      refine ⟨⟨?_, hterm.2⟩, ?_⟩
      · obtain ⟨p, hp, hpt⟩ := hterm.1
        exact ⟨p, hp.1, hpt⟩
      · have hcut := F.finiteSafeProjection_inter_cut_subset_endpoints hYfinite hX Q
          hfirstForward
        change P.vertexSet ∩ X ⊆ {s, project t}
        simpa only [hfirst, hlast, project_outgoing] using hcut
    · simp [CurrentSafeOccurrence.terminal?]
    · exact F.finiteSafeProjection_not_vertexSet_subset_cut hYfinite hX Q
        hfirstForward (by simpa only [hfirst] using hsLiftOff) hlastForward

#print axioms exists_safeOccurrence_avoiding_cut

end Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp

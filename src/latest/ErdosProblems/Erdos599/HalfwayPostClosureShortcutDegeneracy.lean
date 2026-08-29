/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureShortcutClosedCarrier
import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedRoof
import ErdosProblems.Erdos599.HalfwayCausalLargeNondegenerateHammockRows
import ErdosProblems.Erdos599.SafeSwitchingDegenerateEndpoints

/-!
# Actual shortcut witnesses and their filtered degeneracy alternative

The chosen per-source segmentation now retains its literal interval
certificates. This module assembles them with the actual interval-row and
captured-roof geometry. Every chosen shortcut has a particular safe outside
interval; filtered closure proves that interval degenerate unless a filtered
large witness exists. The common-owner consequence additionally requires
switching-ready safeness, which is not inferred from ordinary safeness.
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

/-- Geometry of the actual contributing interval, retained separately from
the endpoint-only imaginary-edge proposition. -/
structure ShortcutIntervalWitness
    (A : PostClosureCompressorAssignment T) (e : V × V) where
  source : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
    Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}
  path : AltPath Gamma.graph
  initial_eq : path.initial = e.1
  terminal_eq : path.terminal? = some e.2
  distinct : e.1 ≠ e.2
  initial_off : e.1 ∉ Gamma.vertexSet C.ladder.limitWarp
  terminal_off : e.2 ∉ Gamma.vertexSet C.ladder.limitWarp
  subset_assigned : path.vertexSet ⊆
    (A.assignment.produced.bracket.assignment.assigned source).vertexSet
  forwardEdges_subset : path.directionEdges .forward ⊆
    familyEdges T.interval.ambientInterval
  safe : IsSafe C.ladder.limitWarp path
  captured : CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder path
  eligible : HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
    C.ladder.limitRoof e.1 (.vertex e.2)
  interior_disjoint : Disjoint (hammockInterior e.1 (.vertex e.2) path)
    Rlimit.closedSet
  outside : ¬path.vertexSet ⊆ Rlimit.closedSet

theorem exists_shortcutIntervalWitness
    (A : PostClosureCompressorAssignment T) {e : V × V}
    (he : e ∈ A.actualPostClosureShortcutEdges) :
    Nonempty (ShortcutIntervalWitness A e) := by
  obtain ⟨s, hs⟩ := A.mem_actualPostClosureShortcutEdges_iff.mp he
  obtain ⟨Q, hstart, hend, hne, huOff, hvOff, hsub, hfwd, _hedges,
      hsafe, helig, hdisj, houtside⟩ :=
    A.actualClosedClassifiedContactSegmentation_shortcut_certificate s e hs
  refine ⟨{
    source := s
    path := Q
    initial_eq := hstart
    terminal_eq := hend
    distinct := hne
    initial_off := huOff
    terminal_off := hvOff
    subset_assigned := hsub
    forwardEdges_subset := ?_
    safe := hsafe
    captured := ⟨Rlimit.later.stage,
      hsub.trans (A.assigned_vertices_subset_capturedRoof s)⟩
    eligible := helig
    interior_disjoint := hdisj
    outside := houtside }⟩
  intro f hf
  have hparent := hfwd hf
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hparent
  obtain ⟨l, hl, hdir, hel⟩ := hparent
  exact A.toPostClosureProducedAssignment
    |>.assigned_forwardLink_edges_subset_intervalFamily s l hl hdir hel

def actualShortcutIntervalWitness
    (A : PostClosureCompressorAssignment T) {e : V × V}
    (he : e ∈ A.actualPostClosureShortcutEdges) : ShortcutIntervalWitness A e :=
  (A.exists_shortcutIntervalWitness he).some

namespace ShortcutIntervalWitness

variable {A : PostClosureCompressorAssignment T} {e : V × V}

theorem filtered_large_of_not_isDegenerate
    (W : ShortcutIntervalWitness A e)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hnondeg : ¬IsDegenerate C.ladder.limitWarp W.path (.vertex e.2)) :
    HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp e.1 (.vertex e.2)
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
      (succ kappa) := by
  obtain ⟨H, hH, hHX⟩ := hfiltered _ _ W.distinct W.eligible
  exact hH.exists_filteredCard_succ_of_outside hHX W.safe W.initial_eq W.terminal_eq
    hnondeg W.captured W.interior_disjoint W.outside

theorem isDegenerate_or_filtered_large
    (W : ShortcutIntervalWitness A e)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa) :
    IsDegenerate C.ladder.limitWarp W.path (.vertex e.2) ∨
      HasFilteredNondegenerateHammockCard Gamma C.ladder.limitWarp e.1 (.vertex e.2)
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder)
        (succ kappa) := by
  by_cases hdeg : IsDegenerate C.ladder.limitWarp W.path (.vertex e.2)
  · exact Or.inl hdeg
  · exact Or.inr (W.filtered_large_of_not_isDegenerate hfiltered hdeg)

theorem isDegenerate_of_not_strong
    (W : ShortcutIntervalWitness A e)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (hnot : ¬IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa e.1 e.2) :
    IsDegenerate C.ladder.limitWarp W.path (.vertex e.2) :=
  hfiltered.isDegenerate_of_not_strong W.distinct W.eligible W.safe W.initial_eq
    W.terminal_eq W.captured W.interior_disjoint W.outside hnot

/-- The arbitrary-reference common-owner consequence. Switching safeness
is still required; finite character of the limiting reference is not. -/
theorem common_interval_owner_of_degenerate_of_switchingSafe
    (W : ShortcutIntervalWitness A e)
    (hswitch : IsSwitchingSafe C.ladder.limitWarp W.path)
    (hdeg : IsDegenerate C.ladder.limitWarp W.path (.vertex e.2)) :
    ∃ p ∈ T.interval.ambientInterval, e.1 ∈ p.support ∧ e.2 ∈ p.support := by
  obtain ⟨p, hp, hstart, hend⟩ :=
    SwitchingCore.exists_common_forward_owner_of_isDegenerate
      T.interval.ambientInterval_linkage.isWarp hswitch W.forwardEdges_subset
      (by simpa only [W.initial_eq] using W.distinct)
      (by simpa only [W.initial_eq] using W.initial_off) W.terminal_off hdeg
  exact ⟨p, hp, by simpa only [W.initial_eq] using hstart, hend⟩

end ShortcutIntervalWitness

#print axioms exists_shortcutIntervalWitness
#print axioms ShortcutIntervalWitness.filtered_large_of_not_isDegenerate
#print axioms ShortcutIntervalWitness.isDegenerate_of_not_strong
#print axioms ShortcutIntervalWitness.common_interval_owner_of_degenerate_of_switchingSafe

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

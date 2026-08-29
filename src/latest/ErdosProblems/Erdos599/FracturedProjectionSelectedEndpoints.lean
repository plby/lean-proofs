/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionEndpoints
import ErdosProblems.Erdos599.FracturedProjectionTrivial

/-!
# Endpoint data for a selected active lifted assignment

These lemmas turn the endpoint clauses of the peeled bracket assignment into
the exact projected endpoint facts used by both the finite and infinite
connector-deletion compilers.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication
open FracturedProjectionEndpoints

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Promote a bracket-safe path along an inclusion of reference warps once
the two exposed endpoints are known to avoid the larger reference.  Forward
provenance is unchanged. -/
theorem IsBracketSafe.of_reference_subwarp
    {U Y₀ Y₁ : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsBracketSafe U Y₀ Q)
    (hY₁ : Gamma.IsWarp Y₁) (hsub : Y₀ ⊆ Y₁)
    (hinitial : ∀ _hfirst : Q.firstDirection? = some .forward,
      Q.initial ∉ Gamma.vertexSet Y₁)
    (hterminal : ∀ t, Q.terminal? = some t →
      Q.lastDirection? = some .forward → t ∉ Gamma.vertexSet Y₁) :
    IsBracketSafe U Y₁ Q := by
  have hsafe : IsSafe Y₁ Q :=
    hQ.isSafe.of_subwarp hY₁ hsub hinitial hterminal
  exact ⟨hsafe, hsafe.isAlternating, hQ.isBracketAlternating.2⟩

theorem selected_project_initial
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    project (B.assigned (toLiftedSource Z hYfinite z)).initial = z.1 := by
  rw [B.starts_at (toLiftedSource Z hYfinite z)]
  exact project_toLiftedSource Z hYfinite z

/-- Boundary alignment promotes the uncovered-source condition from
reference initials to the full reference carrier. -/
theorem selected_project_initial_outside
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    project (B.assigned (toLiftedSource Z hYfinite z)).initial ∉
      Gamma.vertexSet Y := by
  rw [selected_project_initial Z hYfinite B z]
  apply hboundary.initial_outside
  refine ⟨?_, z.property.2⟩
  rcases z.property.1 with ⟨p, hp, hpz⟩
  exact ⟨p, hp.1, hpz⟩

/-- A selected finite upstairs endpoint projects to an active fractured
terminal outside the whole reference warp, not merely outside the peeled
reference. -/
theorem selected_finite_terminal_data
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) {w : Vertex V}
    (hw : (B.assigned (toLiftedSource Z hYfinite z)).terminal? = some w) :
    w ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z) ∧
      project w ∈
        Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y := by
  have hwSelected := B.toSimultaneousAssignment.finite_terminal_mem
    (toLiftedSource Z hYfinite z) hw
  have hprojectFrontier :
      project w ∈ Gamma.terminalFrontier (activePaths Z) :=
    project_mem_terminalFrontier_activePaths Z hwSelected.1
  have hprojectOutsideActive :
      project w ∉ Gamma.vertexSet (activeReference Z Y) := by
    intro hproject
    apply hwSelected.2
    exact (mem_vertexSet_liftedReference_iff_project Z
      (activeReference_hasFiniteCharacter Z hYfinite)).2 hproject
  have hactive :
      project w ∈ Gamma.terminalFrontier (activePaths Z) \
        Gamma.vertexSet (activeReference Z Y) :=
    ⟨hprojectFrontier, hprojectOutsideActive⟩
  rw [active_terminal_difference_eq (Y := Y) Z] at hactive
  exact ⟨hwSelected.1, hactive⟩

/-- In the finite selected branch the final upstairs link points forward.
A backward final link would put its exit, hence the selected terminal, on
the expanded reference warp, contradicting maximality. -/
theorem selected_finite_last_direction_forward
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : B.assigned (toLiftedSource Z hYfinite z) = .finite Q) :
    Q.lastLink.direction = .forward := by
  have hterminal :
      (B.assigned (toLiftedSource Z hYfinite z)).terminal? =
        some Q.terminal := by
    simp [hQ, AltPath.terminal?]
  have houtside := (B.toSimultaneousAssignment.finite_terminal_mem
    (toLiftedSource Z hYfinite z) hterminal).2
  have hbracket := B.bracket_safe (toLiftedSource Z hYfinite z)
  rw [hQ] at hbracket
  cases hdir : Q.lastLink.direction with
  | forward => rfl
  | backward =>
      exfalso
      apply houtside
      have hlast : Q.lastLink ∈ (AltPath.finite Q).links := by
        exact Q.lastLink_mem_links
      rcases hbracket.isAlternating.2.1 Q.lastLink hlast hdir with
        ⟨P, hP, hsub⟩
      refine ⟨P, hP, ?_⟩
      exact hsub.1 Q.lastLink.exit_mem_support

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599

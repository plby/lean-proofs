/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentPeel

/-!
# Endpoint bookkeeping for fractured-warp projection

The active (non-singleton) holes have a particularly rigid occurrence lift:
their sources are outgoing copies and their finite terminals are incoming
copies.  The expanded reference, on the other hand, contains the entire
three-element fibre over each of its vertices.  This file records the exact
source, terminal, and reference-carrier equivalences used by the projection
compiler.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open FracturedDuplication FracturedAssignmentPeel

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}

namespace FracturedProjectionEndpoints

/-- A finite terminal of an occurrence-lifted active hole is its incoming
copy.  In particular projection is injective on this terminal frontier. -/
theorem eq_terminalCopy_of_mem_terminalFrontier_activeLifted
    (Z : FracturedWarp Gamma) {z : Vertex V}
    (hz : z ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z)) :
    z = terminalCopy Z (project z) := by
  rcases hz with ⟨P, ⟨p, hp, rfl⟩, hpterm⟩
  have hptermOriginal : Gamma.terminal? p = some (project z) := by
    have hmap := congrArg (Option.map project) hpterm
    rw [terminal_liftPath_projected] at hmap
    simpa only [Option.map_some] using hmap
  have hne : project z ≠ p.initial :=
    (initial_ne_terminal_of_nontrivial hp.2 hptermOriginal).symm
  have hptermPath : p.terminal? = some (project z) := by
    simpa [DWeb.terminal?] using hptermOriginal
  have hoccurrence : occurrence Z p (project z) = z := by
    change (liftPath Z p).terminal? = some z at hpterm
    rw [terminal_liftPath, hptermPath] at hpterm
    simpa only [Option.map_some, Option.some.injEq] using hpterm
  rw [← hoccurrence]
  simp [terminalCopy, occurrence, hne, hptermOriginal]

/-- Two active lifted terminals with the same projection are equal. -/
theorem project_injective_on_terminalFrontier_activeLifted
    (Z : FracturedWarp Gamma) {z w : Vertex V}
    (hz : z ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z))
    (hw : w ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z))
    (hproject : project z = project w) : z = w := by
  rw [eq_terminalCopy_of_mem_terminalFrontier_activeLifted Z hz,
    eq_terminalCopy_of_mem_terminalFrontier_activeLifted Z hw, hproject]

/-- Projection sends the active lifted terminal frontier into the original
active terminal frontier. -/
theorem project_mem_terminalFrontier_activePaths
    (Z : FracturedWarp Gamma) {z : Vertex V}
    (hz : z ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z)) :
    project z ∈ Gamma.terminalFrontier (activePaths Z) := by
  rcases hz with ⟨P, ⟨p, hp, rfl⟩, hpterm⟩
  refine ⟨p, hp, ?_⟩
  have hmap := congrArg (Option.map project) hpterm
  rw [terminal_liftPath_projected] at hmap
  simpa only [Option.map_some] using hmap

/-- Every active finite terminal has its incoming copy in the lifted
terminal frontier. -/
theorem terminalCopy_mem_terminalFrontier_activeLifted
    (Z : FracturedWarp Gamma) {x : V}
    (hx : x ∈ Gamma.terminalFrontier (activePaths Z)) :
    terminalCopy Z x ∈
      (web Gamma Z).terminalFrontier (activeLiftedPaths Z) := by
  rcases hx with ⟨p, hp, hpterm⟩
  refine ⟨liftPath Z p, ⟨p, hp, rfl⟩, ?_⟩
  change (liftPath Z p).terminal? = some (terminalCopy Z x)
  have hptermPath : p.terminal? = some x := by
    simpa [DWeb.terminal?] using hpterm
  rw [terminal_liftPath, hptermPath]
  have hne : x ≠ p.initial :=
    (initial_ne_terminal_of_nontrivial hp.2 hpterm).symm
  simp [terminalCopy, occurrence, hne, hpterm]

/-- The source-copy map identifies the active source set with the active
lifted source set. -/
theorem sourceCopy_mem_initialSet_activeLifted_iff
    (Z : FracturedWarp Gamma) {x : V} :
    sourceCopy Z x ∈ (web Gamma Z).initialSet (activeLiftedPaths Z) ↔
      x ∈ Gamma.initialSet (activePaths Z) := by
  rw [initialSet_activeLiftedPaths]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := sourceCopy_injective Z hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Expanded reference membership is fibrewise: it is equivalent to
membership of the projected vertex in the original active reference. -/
theorem mem_vertexSet_liftedReference_iff_project
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y) {z : Vertex V} :
    z ∈ (web Gamma Z).vertexSet (liftedReference Z Y) ↔
      project z ∈ Gamma.vertexSet Y := by
  rw [vertexSet_liftedReference Z hYfinite]
  constructor
  · rintro ⟨x, hx, hzx⟩
    rwa [mem_vertexBlock_project Z hzx]
  · intro hz
    exact ⟨project z, hz, by
      rcases z with ⟨x, r⟩
      rcases r <;> simp [project, vertexBlock, plain, incoming, outgoing]⟩

/-- Expanded reference initials are precisely outgoing copies of original
reference initials. -/
theorem sourceCopy_mem_initialSet_liftedReference_iff
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y) {x : V} :
    sourceCopy Z x ∈
        (web Gamma Z).initialSet (liftedReference Z Y) ↔
      x ∈ Gamma.initialSet Y := by
  rw [initialSet_liftedReference Z hYfinite]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := sourceCopy_injective Z hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end FracturedProjectionEndpoints
end LinkageBlueprint
end Blueprint
end Erdos599

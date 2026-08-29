/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OutsideFracturedColouredDichotomy
import ErdosProblems.Erdos599.ColouredSafeHammockClosure

/-!
# Native hammock classification for outside-cut occurrences

The local cut certificates feed the native closure argument directly. In
the finite non-strong case the degenerate switched path has both endpoints
on one member of the ORIGINAL uncut forward warp, not merely the recombined
outside family. Global closure and distinct-terminal selection are separate.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp

open Set Cardinal DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath} {X : Set V}
variable {s t : V} {rho : Cardinal.{u}}

/-- Every forward edge of an outside occurrence was an edge of the
original uncut warp. This is stronger than current-iteration weak provenance. -/
theorem occurrence_forwardEdges_subset_original (F : OutsideFracturedWarp W X)
    (A : CurrentSafeOccurrence F.holes.edgeWarp Y s) :
    A.forwardEdges ⊆ familyEdges W := by
  intro e he
  have hOutside := A.forwardEdges_subset_current he
  rw [F.edgeWarp_familyEdges] at hOutside
  exact hOutside.1

/-- Literal insertion into the native maximal family classifies an outside
occurrence without producing an `AltPath` or assuming its collision rules. -/
theorem hasNativeHammock_of_occurrence (F : OutsideFracturedWarp W X)
    (A : CurrentSafeOccurrence F.holes.edgeWarp Y s)
    (hs : s ∉ Gamma.vertexSet Y)
    (hfinite : ∀ t, A.terminal? = some t → t ∉ Gamma.vertexSet Y)
    (hclosed : ColouredSafeHammock.ClosedAt Y s A.terminal?
      (fun _ ↦ True) rho X)
    (hcap : A.vertexSet ∩ X ⊆ ColouredSafeHammock.endpoints s A.terminal?)
    (hout : ¬ A.vertexSet ⊆ X) :
    ColouredSafeHammock.HasCard Y s A.terminal? (fun _ ↦ True) (Order.succ rho) := by
  apply ColouredSafeHammock.hasCard_of_external hclosed
    (A := toAmbient A) ?_ (by simpa using hcap) (by simpa using hout)
  refine ⟨toAmbient_valid A F.holes.edgeWarp_isWarp F.edgeWarpFiniteCharacter,
    by simp, hs, hfinite, trivial⟩

/-- The native weak-shortcut endpoint theorem retains the actual original
finite-row owner. No source-history pullback theorem is used. -/
theorem native_nonstrong_endpoints_same_original_owner (F : OutsideFracturedWarp W X)
    (A : CurrentSafeOccurrence F.holes.edgeWarp Y s)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hclosed : ColouredSafeHammock.ClosedAt Y s (some t)
      (fun B ↦ ¬B.HasFiniteSwitchedPathTo t) rho X)
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X)
    (hnotLarge : ¬ ColouredSafeHammock.HasCard Y s (some t)
      (fun B ↦ ¬B.HasFiniteSwitchedPathTo t) (Order.succ rho)) :
    ∃ p ∈ W, s ∈ p.support ∧ t ∈ p.support := by
  let B : CurrentSafeOccurrence W Y s :=
    A.retypeForward (F.occurrence_forwardEdges_subset_original A)
  exact ColouredSafeHammock.endpoints_same_forward_owner_of_not_large_nondegenerate
    B hW hWfinite hY (by simpa [B] using hend) hne hs ht hclosed
    (by simpa [B] using hcap) (by simpa [B] using hout) hnotLarge

#print axioms occurrence_forwardEdges_subset_original
#print axioms hasNativeHammock_of_occurrence
#print axioms native_nonstrong_endpoints_same_original_owner

end Erdos599.Blueprint.LinkageBlueprint.OutsideFracturedWarp

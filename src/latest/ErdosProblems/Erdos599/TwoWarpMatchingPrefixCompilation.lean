/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingForwardOrbit
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Alternating-path compilation of an internal matching prefix

This file packages the exact facts which survive identity contraction, loop
erasure, and maximal-run compression of a finite first-return prefix.  It
deliberately stops short of claiming contact coverage or switching safeness:
those require a contact-complete occurrence construction, not merely the
ordinary two-matching orbit.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

namespace FinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- The finite alternating path compiled from a projected-root-simple port
prefix. -/
noncomputable def altPath (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    AltPath Gamma.graph :=
  .finite (P.compiledRunWalk hrootUnique).toFiniteTrace

@[simp] theorem altPath_initial (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.altPath hrootUnique).initial = root := by
  change (P.compiledRunWalk hrootUnique).toFiniteTrace.initial = root
  rw [FiniteRunWalk.toFiniteTrace_initial]
  exact P.compiledRunWalk_initial hrootUnique

@[simp] theorem altPath_terminal (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.altPath hrootUnique).terminal? = some
      (P.projectedVertex ⟨P.lastIndex, Nat.lt_succ_self _⟩) := by
  change some (P.compiledRunWalk hrootUnique).toFiniteTrace.terminal = _
  rw [FiniteRunWalk.toFiniteTrace_terminal]
  exact congrArg some (P.compiledRunWalk_terminal hrootUnique)

/-- Compiled forward links stay literal fragments of the forward warp. -/
theorem altPath_forwardLinksOn (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (hW : Gamma.IsWarp W) :
    ∀ l ∈ (P.altPath hrootUnique).links, l.direction = .forward →
      IsFragmentOf l.path W := by
  intro l hl hdir
  change l ∈ (P.compiledRunWalk hrootUnique).toFiniteTrace.links at hl
  rw [FiniteRunWalk.toFiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hW _ ((P.compiledRunWalk hrootUnique).run i).link.nontrivial
    (P.compiledRunWalk_forward_edge_mem hrootUnique i hdir)

/-- Compiled forward links avoid every reference-warp edge. -/
theorem altPath_forwardLinksOff (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    ForwardLinksOff Y (P.altPath hrootUnique) := by
  intro l hl hdir
  change l ∈ (P.compiledRunWalk hrootUnique).toFiniteTrace.links at hl
  rw [FiniteRunWalk.toFiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact P.compiledRunWalk_forward_edge_not_mem_reference hrootUnique i hdir

/-- Compiled backward links remain literal fragments of the reference warp. -/
theorem altPath_backwardLinksOn (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (hY : Gamma.IsWarp Y) :
    BackwardLinksOn Y (P.altPath hrootUnique) := by
  intro l hl hdir
  change l ∈ (P.compiledRunWalk hrootUnique).toFiniteTrace.links at hl
  rw [FiniteRunWalk.toFiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hY _ ((P.compiledRunWalk hrootUnique).run i).link.nontrivial
    (P.compiledRunWalk_backward_edge_mem hrootUnique i hdir)

end FinitePortPrefix

end

end TwoWarpMatchingTraversal
end Erdos599

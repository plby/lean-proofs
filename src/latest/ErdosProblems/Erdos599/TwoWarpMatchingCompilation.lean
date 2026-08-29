/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingProjection
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Compiling a rooted two-warp matching component

This file packages the contact-marked matching component constructed in
`TwoWarpMatchingTraversal` after identity contraction, chronological loop
erasure, and maximal-run compression.  The finite and infinite outcomes stay
separate.  In particular, the finite outcome retains the terminal of the
actual maximal bipartite component, while the infinite outcome is represented
by a genuine infinite alternating trace.

This compiler does not identify its output with the older lazy macro
assignment.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

namespace FiniteTraversal

/-- A rooted maximal finite matching component begins with a literal edge
whenever the forward warp has an actual edge leaving the normalized source. -/
theorem first_project_ne_of_source_edge
    {W Y : Set Gamma.DPath} {root y : V}
    (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hW : Gamma.IsWarp W)
    (hsource : root ∈ Gamma.source)
    (hforward : (root, y) ∈ familyEdges W) :
    T.projectedVertex 0 ≠
      T.projectedVertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
  let i : Fin T.lastIndex := ⟨0, T.positive⟩
  have hcast : i.castSucc = (0 : Fin (T.lastIndex + 1)) := Fin.ext rfl
  have hsucc : i.succ =
      (⟨1, Nat.succ_lt_succ T.positive⟩ : Fin (T.lastIndex + 1)) :=
    Fin.ext rfl
  have hleft : T.port i.castSucc = .inl root := by
    rw [hcast]
    exact T.starts
  have hstep := T.steps i
  rcases step_cases hstep with
    ⟨x, z, hxi, hzr, hxz⟩ | ⟨x, z, hzi, hxr, hzx⟩
  · have hx : x = root := Sum.inl.inj (hxi.symm.trans hleft)
    subst x
    have hz : z = y :=
      (matchingEdge_biUnique hW).2 hxz.1 (matchingEdge_actual hforward)
    subst z
    intro heq
    have hterminalPort :
        T.port ⟨1, Nat.succ_lt_succ T.positive⟩ = .inr y := by
      rw [← hsucc]
      exact hzr
    have hry : root = y := by
      simpa [projectedVertex, T.starts, hterminalPort] using heq
    subst y
    exact (hGamma (familyEdges_subset_adj W hforward)).1 hsource
  · exact False.elim (Sum.inl_ne_inr (hleft.symm.trans hzi))

end FiniteTraversal

namespace InfiniteTraversal

/-- Infinite analogue of `FiniteTraversal.first_project_ne_of_source_edge`. -/
theorem first_project_ne_of_source_edge
    {W Y : Set Gamma.DPath} {root y : V}
    (T : InfiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hW : Gamma.IsWarp W)
    (hsource : root ∈ Gamma.source)
    (hforward : (root, y) ∈ familyEdges W) :
    T.projectedVertex 0 ≠ T.projectedVertex 1 := by
  have hstep := T.steps 0
  have hleft : T.port 0 = .inl root := T.starts
  rcases step_cases hstep with
    ⟨x, z, hxi, hzr, hxz⟩ | ⟨x, z, hzi, hxr, hzx⟩
  · have hx : x = root := Sum.inl.inj (hxi.symm.trans hleft)
    subst x
    have hz : z = y :=
      (matchingEdge_biUnique hW).2 hxz.1 (matchingEdge_actual hforward)
    subst z
    intro heq
    have hry : root = y := by
      simpa [projectedVertex, hleft, hzr] using heq
    subst y
    exact (hGamma (familyEdges_subset_adj W hforward)).1 hsource
  · exact False.elim (Sum.inl_ne_inr (hleft.symm.trans hzi))

end InfiniteTraversal

/-- The two genuinely compiled shapes of a rooted symmetric-difference
component.  Storing the original component keeps all occurrence-level contact
labels available to downstream consumers. -/
inductive CompiledSourceComponent
    (W Y : Set Gamma.DPath) (root : V) : Type u
  | finite (T : FiniteTraversal W Y root)
      (first_literal : T.projectedVertex 0 ≠
        T.projectedVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
  | infinite (T : InfiniteTraversal W Y root)
      (first_literal : T.projectedVertex 0 ≠ T.projectedVertex 1)

namespace CompiledSourceComponent

variable {W Y : Set Gamma.DPath} {root : V}

/-- Compile the stored matching component to a finite or infinite alternating
path. -/
noncomputable def altPath (C : CompiledSourceComponent W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) : AltPath Gamma.graph :=
  match C with
  | .finite T _ => .finite (T.compiledRunWalk hGamma hsource).toFiniteTrace
  | .infinite T hfirst =>
      .infinite (T.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace

/-- The compiled path starts at the source that selected the matching
component. -/
@[simp] theorem altPath_initial (C : CompiledSourceComponent W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    (C.altPath hGamma hsource hW hWfinite hY).initial = root := by
  cases C with
  | finite T hfirst =>
      change (T.compiledRunWalk hGamma hsource).toFiniteTrace.initial = root
      rw [FiniteRunWalk.toFiniteTrace_initial]
      exact T.compiledRunWalk_initial hGamma hsource
  | infinite T hfirst =>
      change (T.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace.initial =
        root
      rw [InfiniteRunWalk.toInfiniteTrace_initial]
      exact T.runWalk_initial_of_source hfirst
        (T.compressorInput_changes hfirst hW hWfinite hY) hGamma hsource

/-- The finite compiled branch ends at the projected terminal of the actual
maximal matching component. -/
theorem altPath_terminal_of_finite
    (T : FiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠
      T.projectedVertex ⟨1, Nat.succ_lt_succ T.positive⟩)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ((CompiledSourceComponent.finite T hfirst).altPath
      hGamma hsource hW hWfinite hY).terminal? =
        some (T.projectedVertex ⟨T.lastIndex, Nat.lt_succ_self _⟩) := by
  change some ((T.compiledRunWalk hGamma hsource).toFiniteTrace.terminal) = _
  rw [FiniteRunWalk.toFiniteTrace_terminal]
  exact congrArg some (T.compiledRunWalk_terminal hGamma hsource)

/-- The infinite compiled branch has no terminal. -/
@[simp] theorem altPath_terminal_of_infinite
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ((CompiledSourceComponent.infinite T hfirst).altPath
      hGamma hsource hW hWfinite hY).terminal? = none := rfl

/-- Every forward link of the compiled matching component avoids the
reference edge set.  This is an unconditional consequence of using the
literal symmetric difference before projection. -/
theorem altPath_forwardLinksOff (C : CompiledSourceComponent W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ForwardLinksOff Y (C.altPath hGamma hsource hW hWfinite hY) := by
  cases C with
  | finite T hfirst =>
      intro l hl hdir
      change l ∈ (T.compiledRunWalk hGamma hsource).toFiniteTrace.links at hl
      rw [FiniteRunWalk.toFiniteTrace_links] at hl
      rcases hl with ⟨i, rfl⟩
      exact T.compiledRunWalk_forward_edge_not_mem_reference
        hGamma hsource i hdir
  | infinite T hfirst =>
      intro l hl hdir
      change l ∈
        (T.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace.links at hl
      rcases hl with ⟨i, rfl⟩
      exact T.compiledRunWalk_forward_edge_not_mem_reference
        hfirst hW hWfinite hY i hdir

/-- Every backward link of the compiled matching component is a literal
fragment of one reference-warp member. -/
theorem altPath_backwardLinksOn (C : CompiledSourceComponent W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    BackwardLinksOn Y (C.altPath hGamma hsource hW hWfinite hY) := by
  cases C with
  | finite T hfirst =>
      intro l hl hdir
      change l ∈ (T.compiledRunWalk hGamma hsource).toFiniteTrace.links at hl
      rw [FiniteRunWalk.toFiniteTrace_links] at hl
      rcases hl with ⟨i, rfl⟩
      exact SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
        hY _ ((T.compiledRunWalk hGamma hsource).run i).link.nontrivial
        (T.compiledRunWalk_backward_edge_mem hGamma hsource i hdir)
  | infinite T hfirst =>
      intro l hl hdir
      change l ∈
        (T.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace.links at hl
      rcases hl with ⟨i, rfl⟩
      exact SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
        hY _
        ((T.compiledRunWalk hfirst hW hWfinite hY).run i).link.nontrivial
        (T.runWalk_backward_edge_mem hfirst
          (T.compressorInput_changes hfirst hW hWfinite hY) i hdir)

end CompiledSourceComponent

/-- Construct and compile the actual maximal matching component selected by a
normalized source edge. -/
theorem exists_compiledSourceComponent_of_source
    {W Y : Set Gamma.DPath} (hGamma : Gamma.IsNormalized)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {root y : V} (hsource : root ∈ Gamma.source)
    (hrootY : root ∉ Gamma.vertexSet Y)
    (hforward : (root, y) ∈ familyEdges W) :
    Nonempty (CompiledSourceComponent W Y root) := by
  rcases exists_traversal_of_source hW hY hsource hrootY hforward with ⟨T⟩
  cases T with
  | finite T =>
      exact ⟨.finite T
        (T.first_project_ne_of_source_edge hGamma hW hsource hforward)⟩
  | infinite T =>
      exact ⟨.infinite T
        (T.first_project_ne_of_source_edge hGamma hW hsource hforward)⟩

end

end TwoWarpMatchingTraversal
end Erdos599

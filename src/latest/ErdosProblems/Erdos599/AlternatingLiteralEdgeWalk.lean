/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingEdgeWalk

/-!
# Literal labels for compressed alternating walks

The source definition of an alternating path only asks backward links to lie
on the reference warp and bracket-forward links to lie on the forward warp.
It does not require forward links to avoid the reference warp.  These label
records expose precisely that literal interface for the macro compiler.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

structure InfiniteRunWalk.LiteralBracketLabels
    (W : InfiniteRunWalk Γ.graph) (U Y : Set Γ.DPath) : Prop where
  reference_isWarp : Γ.IsWarp Y
  backward_on : ∀ i, (W.run i).link.direction = .backward →
    IsFragmentOf (W.run i).link.path Y
  forward_on : ∀ i, (W.run i).link.direction = .forward →
    IsFragmentOf (W.run i).link.path U
  initial_outside : (W.run 0).link.direction = .forward →
    W.vertex 0 ∉ Γ.vertexSet Y

namespace InfiniteRunWalk

theorem isLiteralBracketAlternating (W : InfiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (h : W.LiteralBracketLabels U Y) :
    IsBracketAlternating U Y (.infinite W.toInfiniteTrace) := by
  refine ⟨⟨h.reference_isWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hdir
    rcases hl with ⟨i, rfl⟩
    exact h.backward_on i hdir
  · intro hfirst
    rw [show (AltPath.infinite W.toInfiniteTrace).initial = W.vertex 0 from
      W.toInfiniteTrace_initial]
    apply h.initial_outside
    simpa [AltPath.firstDirection?, toInfiniteTrace] using hfirst
  · intro t ht
    simp [AltPath.terminal?] at ht
  · intro l hl hdir
    rcases hl with ⟨i, rfl⟩
    exact h.forward_on i hdir

end InfiniteRunWalk

structure FiniteRunWalk.LiteralBracketLabels
    (W : FiniteRunWalk Γ.graph) (U Y : Set Γ.DPath) : Prop where
  reference_isWarp : Γ.IsWarp Y
  backward_on : ∀ i, (W.run i).link.direction = .backward →
    IsFragmentOf (W.run i).link.path Y
  forward_on : ∀ i, (W.run i).link.direction = .forward →
    IsFragmentOf (W.run i).link.path U
  initial_outside :
    (W.run ⟨0, Nat.zero_lt_succ _⟩).link.direction = .forward →
    W.vertex 0 ∉ Γ.vertexSet Y
  terminal_outside : (W.run W.lastRunIndex).link.direction = .forward →
    W.vertex (W.run W.lastRunIndex).last ∉ Γ.vertexSet Y

namespace FiniteRunWalk

theorem isLiteralBracketAlternating (W : FiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (h : W.LiteralBracketLabels U Y) :
    IsBracketAlternating U Y (.finite W.toFiniteTrace) := by
  refine ⟨⟨h.reference_isWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hdir
    change l ∈ W.toFiniteTrace.links at hl
    rw [W.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    exact h.backward_on i hdir
  · intro hfirst
    rw [show (AltPath.finite W.toFiniteTrace).initial = W.vertex 0 from
      W.toFiniteTrace_initial]
    apply h.initial_outside
    simpa [AltPath.firstDirection?, FiniteTrace.firstLink, toFiniteTrace] using hfirst
  · intro t ht hlast
    have ht' : t = W.vertex (W.run W.lastRunIndex).last := by
      change some W.toFiniteTrace.terminal = some t at ht
      have heq : W.toFiniteTrace.terminal = t := Option.some.inj ht
      rw [W.toFiniteTrace_terminal] at heq
      exact heq.symm
    subst t
    apply h.terminal_outside
    simpa [AltPath.lastDirection?, FiniteTrace.lastLink, toFiniteTrace,
      lastRunIndex] using hlast
  · intro l hl hdir
    change l ∈ W.toFiniteTrace.links at hl
    rw [W.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    exact h.forward_on i hdir

end FiniteRunWalk

end Alternating
end Erdos599

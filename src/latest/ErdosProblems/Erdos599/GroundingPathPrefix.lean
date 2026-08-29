/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Finite initial prefixes of finite paths and rays

The component geometry in Assertion 8.22 repeatedly starts with a point on
one member of the limiting ladder warp.  Even when that member is a ray, the
part between its initial vertex and the chosen point is finite.  This file
packages that elementary fact with the exact support and edge-set inclusions
needed by the switched-relation argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPathPrefix

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Every vertex on a finite path or ray is reached by a finite initial
prefix using only vertices and edges of the original path. -/
theorem exists_initialFinitePrefix
    (p : Gamma.DPath) {x : V} (hx : x ∈ p.support) :
    ∃ q : FinitePath Gamma.graph,
      q.start = p.initial ∧ q.finish = x ∧
        q.support ⊆ p.support ∧ q.edgeSet ⊆ p.edgeSet := by
  rcases p with p | r
  · let hmeet : p.walk.Meets ({x} : Set V) :=
      ⟨x, hx, Set.mem_singleton x⟩
    let q := p.firstHit ({x} : Set V) hmeet
    refine ⟨q, rfl, ?_, p.firstHit_support_subset {x} hmeet,
      p.firstHit_edgeSet_subset {x} hmeet⟩
    exact Set.mem_singleton_iff.mp (p.firstHit_finish_mem {x} hmeet)
  · obtain ⟨n, rfl⟩ := hx
    let q := Alternating.SwitchingCore.rayPrefixPath r n
    refine ⟨q, rfl, rfl, ?_, ?_⟩
    · intro y hy
      change y ∈ (Alternating.SwitchingCore.rayPrefixWalk r n).support at hy
      rw [Alternating.SwitchingCore.rayPrefixWalk_support,
        List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      exact ⟨i, rfl⟩
    · intro e he
      rw [Alternating.SwitchingCore.rayPrefixPath_edgeSet] at he
      obtain ⟨k, _hk, rfl⟩ := he
      exact ⟨k, rfl⟩

end GroundingPathPrefix
end Erdos599


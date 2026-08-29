/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930FreshPath

/-!
# Exact finite-diamond boundary bookkeeping

Replacing one finite member by its fresh finite continuation leaves the
initial set and the ray members unchanged. The terminal set can only gain
the new endpoint, and the path-cardinality bound is preserved at infinite
capacity. These facts do not assert source coverage: a newly touched retained
reference component still requires the global assignment construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem initialSet_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    (W.diamond q hq P hstart hfresh).initialSet = W.initialSet := by
  let hqfresh : q.support ∩ P.support ⊆ {q.finish} :=
    fun _ hx ↦ hfresh ⟨⟨.inl q, hq, hx.1⟩, hx.2⟩
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    change p ∈ (W.paths \ {(.inl q : Path _)}) ∪
      {(.inl (diamondPath q P hstart hqfresh) : Path _)} at hp
    rcases hp with hp | hp
    · exact ⟨p, hp.1, hpx⟩
    · have hpeq := Set.mem_singleton_iff.1 hp
      subst p
      refine ⟨.inl q, hq, ?_⟩
      simpa only [Path.initial, diamondPath_start] using hpx
  · rintro ⟨p, hp, hpx⟩
    by_cases hpq : p = (.inl q : Path _)
    · subst p
      refine ⟨.inl (diamondPath q P hstart hqfresh), ?_, ?_⟩
      · exact Or.inr (Set.mem_singleton_iff.mpr rfl)
      · simpa only [Path.initial, diamondPath_start] using hpx
    · exact ⟨p, Or.inl ⟨hp, hpq⟩, hpx⟩

theorem ray_mem_diamond_iff
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish})
    (r : Ray (imaginaryGraph Gamma Y kappa)) :
    (.inr r : Path _) ∈ (W.diamond q hq P hstart hfresh).paths ↔
      (.inr r : Path _) ∈ W.paths := by
  simp [diamond, diamondPaths]

theorem infinitelyManyStrongEdges_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish})
    (hstrong : W.InfinitelyManyStrongEdges) :
    (W.diamond q hq P hstart hfresh).InfinitelyManyStrongEdges := by
  intro r hr
  exact hstrong r ((ray_mem_diamond_iff W q hq P hstart hfresh r).1 hr)

theorem terminalSet_diamond_subset
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    (W.diamond q hq P hstart hfresh).terminalSet ⊆
      W.terminalSet ∪ {P.finish} := by
  rintro x ⟨p, hp, hpx⟩
  change p ∈ (W.paths \ {(.inl q : Path _)}) ∪ {_} at hp
  rcases hp with hp | hp
  · exact Or.inl ⟨p, hp.1, hpx⟩
  · have hpeq := Set.mem_singleton_iff.1 hp
    subst p
    right
    change some (diamondPath q P hstart _).finish = some x at hpx
    exact (Option.some.inj hpx).symm.trans (diamondPath_finish q P hstart _)

theorem mk_paths_diamond_le
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish})
    (hkappa : aleph0 ≤ kappa) (hcard : #W.paths ≤ kappa) :
    #(W.diamond q hq P hstart hfresh).paths ≤ kappa := by
  change #((W.paths \ {(.inl q : Path _)}) ∪ {_} : Set (Path _)) ≤ kappa
  refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hkappa ?_ ?_)
  · exact (Cardinal.mk_subtype_mono Set.sdiff_subset).trans hcard
  · simpa only [Cardinal.mk_singleton] using
      (Cardinal.one_le_aleph0.trans hkappa)

#print axioms initialSet_diamond
#print axioms infinitelyManyStrongEdges_diamond
#print axioms terminalSet_diamond_subset
#print axioms mk_paths_diamond_le

end Erdos599.Blueprint.LinkageBlueprint

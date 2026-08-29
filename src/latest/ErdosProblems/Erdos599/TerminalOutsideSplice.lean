/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintSplice
import ErdosProblems.Erdos599.HalfwayContinuationRepair

/-!
# The terminal-outside-slice splice in Assertion 9.30

This file records the two exact carrier formulas for the paper's `diamond`
operation: replacing one finite blueprint member by its splice with a fresh
real path adds precisely that path's vertices and edges.  These formulas are
the foundational bookkeeping needed by any terminal-outside-slice splice
certificate; construction of a whole coupled replacement remains a separate
global assignment obligation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace LinkageBlueprint

/-- The vertices of a one-path diamond splice are exactly the old vertices
together with the vertices of the appended real path. -/
theorem vertexSet_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    (W.diamond q hq P hstart hfresh).vertexSet =
      W.vertexSet ∪ P.support := by
  let hqfresh : q.support ∩ P.support ⊆ {q.finish} :=
    fun _ hx => hfresh ⟨⟨.inl q, hq, hx.1⟩, hx.2⟩
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    simp only [diamond, diamondPaths, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨p, hp.1, hxp⟩
    · subst p
      change x ∈ (diamondPath q P hstart _).support at hxp
      unfold diamondPath at hxp
      rw [FinitePath.support_appendFinite_eq_union,
        liftOriginal_support] at hxp
      rcases hxp with hxq | hxP
      · exact Or.inl ⟨.inl q, hq, hxq⟩
      · exact Or.inr hxP
  · intro hx
    rcases hx with hxW | hxP
    · obtain ⟨p, hpW, hxp⟩ := hxW
      by_cases hpq : p = (.inl q : Path _)
      · subst p
        refine ⟨.inl (diamondPath q P hstart hqfresh), ?_, ?_⟩
        · change (.inl (diamondPath q P hstart hqfresh) : Path _) ∈
            diamondPaths W q P hstart _
          exact Or.inr (Set.mem_singleton_iff.mpr (by congr))
        · change x ∈ (diamondPath q P hstart _).support
          unfold diamondPath
          rw [FinitePath.support_appendFinite_eq_union,
            liftOriginal_support]
          exact Or.inl hxp
      · refine ⟨p, ?_, hxp⟩
        change p ∈ diamondPaths W q P hstart _
        exact Or.inl ⟨hpW, hpq⟩
    · refine ⟨.inl (diamondPath q P hstart hqfresh), ?_, ?_⟩
      · change (.inl (diamondPath q P hstart hqfresh) : Path _) ∈
          diamondPaths W q P hstart _
        exact Or.inr (Set.mem_singleton_iff.mpr (by congr))
      · change x ∈ (diamondPath q P hstart _).support
        unfold diamondPath
        rw [FinitePath.support_appendFinite_eq_union,
          liftOriginal_support]
        exact Or.inr hxP

/-- The edge set of a diamond splice is the old edge set together with the
edges of the appended real path. -/
theorem edgeSet_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    (W.diamond q hq P hstart hfresh).edgeSet =
      W.edgeSet ∪ P.edgeSet := by
  let hqfresh : q.support ∩ P.support ⊆ {q.finish} :=
    fun _ hx => hfresh ⟨⟨.inl q, hq, hx.1⟩, hx.2⟩
  ext e
  constructor
  · intro he
    rcases Set.mem_iUnion.1 he with ⟨p, he⟩
    rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
    simp only [diamond, diamondPaths, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff] at hp
    rcases hp with hp | hp
    · exact Or.inl <| Set.mem_iUnion.2 ⟨p,
        Set.mem_iUnion.2 ⟨hp.1, hep⟩⟩
    · subst p
      change e ∈ (diamondPath q P hstart _).edgeSet at hep
      unfold diamondPath at hep
      rw [FinitePath.edgeSet_appendFinite, liftOriginal_edgeSet] at hep
      rcases hep with heq | heP
      · exact Or.inl <| Set.mem_iUnion.2 ⟨.inl q,
          Set.mem_iUnion.2 ⟨hq, heq⟩⟩
      · exact Or.inr heP
  · intro he
    rcases he with heW | heP
    · rcases Set.mem_iUnion.1 heW with ⟨p, heW⟩
      rcases Set.mem_iUnion.1 heW with ⟨hpW, hep⟩
      by_cases hpq : p = (.inl q : Path _)
      · subst p
        refine Set.mem_iUnion.2 ⟨.inl (diamondPath q P hstart hqfresh),
          Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
        · simp [diamond, diamondPaths, hqfresh]
        · change e ∈ (diamondPath q P hstart _).edgeSet
          unfold diamondPath
          rw [FinitePath.edgeSet_appendFinite, liftOriginal_edgeSet]
          exact Or.inl hep
      · refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨?_, hep⟩⟩
        change p ∈ diamondPaths W q P hstart _
        exact Or.inl ⟨hpW, hpq⟩
    · refine Set.mem_iUnion.2 ⟨.inl (diamondPath q P hstart hqfresh),
        Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · simp [diamond, diamondPaths, hqfresh]
      · change e ∈ (diamondPath q P hstart _).edgeSet
        unfold diamondPath
        rw [FinitePath.edgeSet_appendFinite, liftOriginal_edgeSet]
        exact Or.inr heP

end LinkageBlueprint
end Blueprint
end Erdos599

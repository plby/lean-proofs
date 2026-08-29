/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Source-rooted finite path selection without an auxiliary-component limit

In a left-unique relation, finite paths from distinct no-incoming roots are
disjoint. Thus finite target reachability of every prescribed root gives an
actual finite-character warp covering exactly those roots. Neither right
uniqueness nor a global prohibition of reverse rays is needed.
-/

namespace Erdos599.SourceRootedPathSelection

open Set DirectedPath Alternating GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Choose one finite target path for each prescribed source. All returned
paths lie in the given carrier and use the given relation literally. -/
theorem exists_finiteWarp
    {E : Set (V × V)} {A B C : Set V}
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hleft : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hA : A ⊆ C) (hEvertices : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C)
    (hroots : ∀ a ∈ A, ¬HasIncoming E a)
    (hreach : ∀ a ∈ A, ∃ b ∈ B,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = A ∧ Gamma.terminalFrontier P ⊆ B ∧
      familyEdges P ⊆ E ∧ Gamma.vertexSet P ⊆ C := by
  classical
  have hpath (a : A) : ∃ p : FinitePath Gamma.graph,
      p.start = a.1 ∧ p.finish ∈ B ∧ p.edgeSet ⊆ E := by
    obtain ⟨b, hb, hab⟩ := hreach a.1 a.2
    obtain ⟨p⟩ := exists_rootedPath_of_reflTransGen hEadj
      (A := {a.1}) ⟨a.1, Set.mem_singleton _, hab⟩
    exact ⟨p.path, Set.mem_singleton_iff.mp p.start_mem,
      by rw [p.finish_eq]; exact hb, p.edgeSet_subset⟩
  choose route hstart hfinish hedges using hpath
  let P : Set Gamma.DPath := Set.range fun a : A ↦ (Sum.inl (route a) : Gamma.DPath)
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hne
    change Disjoint (route a).support (route b).support
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hax := finitePath_start_reaches_of_mem_support (route a) (hedges a) hxa
    have hbx := finitePath_start_reaches_of_mem_support (route b) (hedges b) hxb
    rw [hstart a] at hax
    rw [hstart b] at hbx
    have hab : a = b := Subtype.ext
      (root_eq_of_reaches_common hleft hax hbx (hroots a.1 a.2) (hroots b.1 b.2))
    subst b
    exact hne rfl
  · rintro p ⟨a, rfl⟩
    exact ⟨route a, rfl⟩
  · ext a
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, hpa⟩
      have hba : b.1 = a := (hstart b).symm.trans hpa
      exact hba ▸ b.2
    · intro ha
      exact ⟨Sum.inl (route ⟨a, ha⟩), ⟨⟨a, ha⟩, rfl⟩, hstart ⟨a, ha⟩⟩
  · rintro b ⟨p, ⟨a, rfl⟩, hpb⟩
    have hpb' : (route a).finish = b := Option.some.inj hpb
    exact hpb' ▸ hfinish a
  · intro e he
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp he
    obtain ⟨⟨a, rfl⟩, he⟩ := Set.mem_iUnion.mp hp
    exact hedges a he
  · rintro x ⟨p, ⟨a, rfl⟩, hxp⟩
    by_cases hxs : x = (route a).start
    · exact (hxs.trans (hstart a)).symm ▸ hA a.2
    · obtain ⟨y, hy⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start (route a) hxp hxs
      exact (hEvertices _ (hedges a hy)).2

#print axioms exists_finiteWarp

end Erdos599.SourceRootedPathSelection

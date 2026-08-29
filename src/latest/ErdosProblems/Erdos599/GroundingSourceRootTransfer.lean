/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPointwiseSwitch

/-!
# Root transfer for realized path relations

This file isolates the relation-theoretic step used by the grounding
switch.  A directed relation chain from a vertex with no predecessor to a
vertex of a realized component identifies the initial vertex of that
component.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Following relation edges backwards from a vertex of one member of a
warp never leaves that member. -/
theorem mem_support_of_reflTransGen_to_mem
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {a x : V}
    (hax : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ familyEdges W) a x)
    {p : Gamma.DPath} (hp : p ∈ W) (hx : x ∈ p.support) :
    a ∈ p.support := by
  induction hax with
  | refl => exact hx
  | @tail b c hab hbc ih =>
      simp only [familyEdges, Set.mem_iUnion] at hbc
      obtain ⟨q, hq, hbc⟩ := hbc
      have hcq : c ∈ q.support := (q.edgeSet_subset_support_prod hbc).2
      have hpq : p = q :=
        DWeb.IsWarp.eq_of_mem_support hW hp hq hx hcq
      apply ih
      rw [hpq]
      exact (q.edgeSet_subset_support_prod hbc).1

/-- A vertex of a warp member with no incoming family edge is that member's
initial vertex. -/
theorem initial_eq_of_mem_support_of_noIncoming
    {W : Set Gamma.DPath}
    {p : Gamma.DPath} (hp : p ∈ W) {a : V}
    (ha : a ∈ p.support) (hno : ¬ HasIncoming (familyEdges W) a) :
    p.initial = a := by
  by_contra hne
  have hane : a ≠ p.initial := fun h ↦ hne h.symm
  apply hno
  rcases p with p | r
  · obtain ⟨y, hy⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        p ha hane
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩
  · obtain ⟨y, hy⟩ :=
      Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial r ha hane
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩

/-- Generic root-transfer lemma for exact relation realizations.  To prove
that every realized component meeting `B` starts in `A`, it is enough to
exhibit, for each vertex of `B`, a directed relation chain from a vertex of
`A` having no incoming relation edge. -/
theorem SwitchData.component_initial_mem_of_rooted_reachability
    (S : SwitchData Gamma) {W : Set Gamma.DPath}
    (hR : S.RealizedBy W) (A B : Set V)
    (hroot : ∀ x ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ S.edges) a x ∧
        ¬ HasIncoming S.edges a)
    {p : Gamma.DPath} (hp : p ∈ W)
    (hmeet : ∃ x ∈ p.support, x ∈ B) :
    p.initial ∈ A := by
  obtain ⟨x, hxp, hxB⟩ := hmeet
  obtain ⟨a, haA, hax, hno⟩ := hroot x hxB
  have haxW : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ familyEdges W) a x := by
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ S.edges)
      (p := fun u v ↦ (u, v) ∈ familyEdges W) (by
        intro u v huv
        rw [hR.2.1]
        exact huv) a x hax
  have haSupport : a ∈ p.support :=
    mem_support_of_reflTransGen_to_mem hR.1 haxW hp hxp
  have hnoW : ¬ HasIncoming (familyEdges W) a := by
    rw [hR.2.1]
    exact hno
  have hinitial : p.initial = a :=
    initial_eq_of_mem_support_of_noIncoming hp haSupport hnoW
  exact hinitial ▸ haA

end Erdos599.Alternating

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp
import ErdosProblems.Erdos599.RootReachableRelation
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# The warp carried by the source-reachable sink components of a relation

A simultaneous switch need not root every point of the bookkeeping frontier:
an old component can be diverted at a selected forward edge and its discarded
tail can become a nonstarting component.  The actual path family is instead
the family of source-reachable components of the switched relation.  Its
terminal frontier is the set of source-reachable sinks.

This file performs that relation-to-warp compilation.  It does not assert
that the resulting sink boundary separates the ambient source and target;
that is the remaining grounding geometry, and must be proved for the concrete
selected relation.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingSourceReachableSinkWarp

open DirectedPath Alternating GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The sinks of `E` which are reached by a finite relation chain from an
allowed root in `A`. -/
def sourceReachableSinkBoundary (E : Set (V × V)) (A : Set V) : Set V :=
  {b | (∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) ∧
    ¬ HasOutgoing E b}

theorem sourceReachableSinkBoundary_rooted
    (E : Set (V × V)) (A : Set V) {b : V}
    (hb : b ∈ sourceReachableSinkBoundary E A) :
    ∃ a ∈ A, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b :=
  hb.1

theorem sourceReachableSinkBoundary_noOutgoing
    (E : Set (V × V)) (A : Set V) {b : V}
    (hb : b ∈ sourceReachableSinkBoundary E A) :
    ¬ HasOutgoing E b :=
  hb.2

/-- A relation chain beginning at a reachable sink is necessarily
reflexive.  Hence the reachable-sink boundary is a reachability antichain,
without any acyclicity or reverse-ray premise on the rest of the relation. -/
theorem sourceReachableSinkBoundary_isReachabilityAntichain
    (E : Set (V × V)) (A : Set V) :
    IsReachabilityAntichain E (sourceReachableSinkBoundary E A) := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim (hb.2 ⟨x, hbx⟩)

/-- A finite level in the root-reachable relation is the same positive data
as a finite relation-reachability witness from one of the prescribed roots. -/
theorem exists_root_reaches_of_atLevel
    (E : Set (V × V)) (A : Set V) {n : Nat} {x : V}
    (hx : RootReachableRelation.AtLevel E A n x) :
    ∃ a ∈ A, Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  induction n generalizing x with
  | zero => exact ⟨x, hx, .refl⟩
  | succ n ih =>
      obtain ⟨y, hy, hyx⟩ := hx
      obtain ⟨a, ha, hay⟩ := ih hy
      exact ⟨a, ha, hay.tail hyx⟩

/-- The source-reachable sink components of any adjacent bi-unique relation
compile to a genuine finite warp.  Its edge set is a subrelation of `E`, its
initials lie in the ambient source, and its terminal frontier is exactly the
dynamic sink boundary. -/
theorem exists_sourceReachableSinkWarp
    (E : Set (V × V)) (A : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hAsource : A ⊆ Gamma.source) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W ⊆ E ∧
        Gamma.initialSet W ⊆ A ∧
        Gamma.initialSet W ⊆ Gamma.source ∧
        Gamma.terminalFrontier W = sourceReachableSinkBoundary E A := by
  let B := sourceReachableSinkBoundary E A
  obtain ⟨P, hcover, hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi hAsource
      (sourceReachableSinkBoundary_isReachabilityAntichain E A)
      (fun b hb ↦ hb.1)
  let W := PopularSwitching.pathFamily P
  refine ⟨W, PopularSwitching.pathFamily_isWarp P, ?_, ?_,
    PopularSwitching.pathFamily_initialSet_subset P,
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover⟩
  · rintro e he
    simp only [familyEdges, W, PopularSwitching.pathFamily,
      Set.mem_iUnion, Set.mem_image] at he
    obtain ⟨p, ⟨q, hq, hp⟩, hep⟩ := he
    subst p
    exact (hpaths q hq).1 hep
  · rintro x ⟨p, ⟨q, hq, hpq⟩, hpx⟩
    subst p
    exact hpx ▸ (hpaths q hq).2.1

/-- Full source-reachable component realization.  In contrast to
`exists_sourceReachableSinkWarp`, this retains a source-reachable forward
ray as a ray member of the output warp.  The relation outside the reachable
carrier may still contain cycles or reverse rays: the natural-number level
on the reachable restriction excludes both internally. -/
theorem exists_sourceReachableComponentWarp
    (E : Set (V × V)) (A : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ A, ¬ HasIncoming E x) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        familyEdges W = RootReachableRelation.edges E A ∧
        Gamma.vertexSet W = RootReachableRelation.carrier E A ∧
        Gamma.initialSet W = A ∧
        Gamma.terminalFrontier W = sourceReachableSinkBoundary E A := by
  let F := RootReachableRelation.edges E A
  let I : Set V := {a | a ∈ A ∧ ¬ HasOutgoing E a}
  have hFadj : F ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    (RootReachableRelation.edges_subset E A).trans hEadj
  have hFbi : Relator.BiUnique fun x y ↦ (x, y) ∈ F :=
    RootReachableRelation.biUnique E A hbi
  have hFcycle : ¬ ContainsDirectedCycle F :=
    RootReachableRelation.no_directed_cycle E A hbi.1 hroots
  have hFreverse : ¬ ContainsReverseDirectedRay F :=
    RootReachableRelation.no_reverse_ray E A hbi.1 hroots
  have hI : ∀ x ∈ I, ∀ y, (x, y) ∉ F ∧ (y, x) ∉ F := by
    intro x hx y
    constructor
    · intro hxy
      exact hx.2 ⟨y, (RootReachableRelation.edges_subset E A) hxy⟩
    · intro hyx
      exact hroots x hx.1
        ⟨y, (RootReachableRelation.edges_subset E A) hyx⟩
  obtain ⟨W, hW, hWE, hWI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma F I hFadj hFbi hFcycle hFreverse hI
  have hvertex : Gamma.vertexSet W = RootReachableRelation.carrier E A := by
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hW,
      hWI, hWE]
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hxI | hxIncident)
      · exact RootReachableRelation.roots_subset_carrier E A hxI.1
      · rcases hxIncident with ⟨y, hyx⟩ | ⟨y, hxy⟩
        · exact (RootReachableRelation.endpoints_mem E A hyx).2
        · exact (RootReachableRelation.endpoints_mem E A hxy).1
    · rintro hxCarrier
      obtain ⟨n, hn⟩ := hxCarrier
      cases n with
      | zero =>
          by_cases hout : HasOutgoing E x
          · right
            right
            obtain ⟨y, hxy⟩ := hout
            exact ⟨y, hxy,
              RootReachableRelation.roots_subset_carrier E A hn⟩
          · exact Or.inl ⟨hn, hout⟩
      | succ n =>
          right
          left
          obtain ⟨y, hy, hyx⟩ := hn
          exact ⟨y, hyx, ⟨n, hy⟩⟩
  have hinitial : Gamma.initialSet W = A := by
    rw [Blueprint.LinkageBlueprint.isWarp_initialSet_eq_noIncoming hW,
      hvertex, hWE]
    ext x
    exact RootReachableRelation.root_iff E A hroots
  have hterminal : Gamma.terminalFrontier W =
      sourceReachableSinkBoundary E A := by
    rw [Blueprint.LinkageBlueprint.isWarp_terminalFrontier_eq_noOutgoing hW,
      hvertex, hWE]
    ext x
    constructor
    · rintro ⟨hxCarrier, hxNo⟩
      obtain ⟨n, hn⟩ := hxCarrier
      refine ⟨exists_root_reaches_of_atLevel E A hn, ?_⟩
      rintro ⟨y, hxy⟩
      exact hxNo ⟨y, hxy, ⟨n, hn⟩⟩
    · rintro ⟨⟨a, ha, hax⟩, hxNo⟩
      have hxCarrier :=
        RootReachableRelation.carrier_of_reflTransGen E A ha hax
      refine ⟨hxCarrier, ?_⟩
      rintro ⟨y, hxy⟩
      exact hxNo ⟨y, (RootReachableRelation.edges_subset E A) hxy⟩
  exact ⟨W, hW, hWE, hvertex, hinitial, hterminal⟩

end GroundingSourceReachableSinkWarp
end Erdos599

#print axioms
  Erdos599.GroundingSourceReachableSinkWarp.exists_sourceReachableSinkWarp
#print axioms
  Erdos599.GroundingSourceReachableSinkWarp.exists_sourceReachableComponentWarp

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActivatedReferencePrefixes
import ErdosProblems.Erdos599.RootReachableBlueprint

/-!
# The source-prefix seed preceding the post-closure diamond

Before attaching the later closed relation, retain every activated finite
reference prefix as a new source-rooted component.  These prefixes are
vertex-disjoint from the current blueprint, so their literal edge union is
already biunique.  Root-reachable realization gives an actual blueprint
which retains both families, including singleton components.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}

/-- Literal old-plus-activated-prefix edge relation. -/
def referencePrefixSeedEdges
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (X : Set V) : Set (V × V) :=
  current.edgeSet ∪ familyEdges (activatedReferencePrefixes C current X)

/-- The genuine roots of the two disjoint input families. -/
def referencePrefixSeedRoots
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (X : Set V) : Set V :=
  current.initialSet ∪
    Gamma.initialSet (activatedReferencePrefixes C current X)

namespace referencePrefixSeed

variable {current : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
variable {X : Set V}

theorem vertexSets_disjoint :
    Disjoint current.vertexSet
      (Gamma.vertexSet (activatedReferencePrefixes C current X)) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hxp⟩ ⟨q, hq, hxq⟩
  exact Set.disjoint_left.1
    (activatedReferencePrefixes.disjoint_current p hp q hq) hxp hxq

theorem edges_subset_imaginaryGraph :
    referencePrefixSeedEdges current X ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · change e ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at he
    exact familyEdges_subset_adj
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths he
  · exact original_adj_imaginaryGraph
      (familyEdges_subset_adj (activatedReferencePrefixes C current X) he)

private theorem no_common_head
    {a b y : V} (hay : (a, y) ∈ current.edgeSet)
    (hby : (b, y) ∈ familyEdges
      (activatedReferencePrefixes C current X)) : False := by
  apply Set.disjoint_left.1 vertexSets_disjoint
  · change (a, y) ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hay
    exact (familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
      current.paths hay).2
  · exact (familyEdges_subset_vertexSet_prod
      (activatedReferencePrefixes C current X) hby).2

private theorem no_common_tail
    {x b c : V} (hxb : (x, b) ∈ current.edgeSet)
    (hxc : (x, c) ∈ familyEdges
      (activatedReferencePrefixes C current X)) : False := by
  apply Set.disjoint_left.1 vertexSets_disjoint
  · change (x, b) ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hxb
    exact (familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
      current.paths hxb).1
  · exact (familyEdges_subset_vertexSet_prod
      (activatedReferencePrefixes C current X) hxc).1

theorem edges_biUnique :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ referencePrefixSeedEdges current X) := by
  have hold : Relator.BiUnique (fun x y ↦ (x, y) ∈ current.edgeSet) :=
    _root_.Erdos599.Alternating.IsWarp.familyEdges_biUnique current.isWarp
  have hpref : Relator.BiUnique (fun x y ↦
      (x, y) ∈ familyEdges (activatedReferencePrefixes C current X)) :=
    _root_.Erdos599.Alternating.IsWarp.familyEdges_biUnique
      activatedReferencePrefixes.isWarp
  constructor
  · intro x w y hxy hwy
    rcases hxy with hxy | hxy <;> rcases hwy with hwy | hwy
    · exact hold.1 hxy hwy
    · exact False.elim (no_common_head hxy hwy)
    · exact False.elim (no_common_head hwy hxy)
    · exact hpref.1 hxy hwy
  · intro x y w hxy hxw
    rcases hxy with hxy | hxy <;> rcases hxw with hxw | hxw
    · exact hold.2 hxy hxw
    · exact False.elim (no_common_tail hxy hxw)
    · exact False.elim (no_common_tail hxw hxy)
    · exact hpref.2 hxy hxw

private theorem prefix_noIncoming
    {x : V}
    (hx : x ∈ Gamma.initialSet
      (activatedReferencePrefixes C current X)) :
    ¬ ∃ y, (y, x) ∈ familyEdges
      (activatedReferencePrefixes C current X) := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hp, rfl⟩ := hx
  simp only [familyEdges, Set.mem_iUnion] at hyx
  obtain ⟨q, hq, hyxq⟩ := hyx
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support
    activatedReferencePrefixes.isWarp hp hq p.initial_mem_support
      (q.edgeSet_subset_support_prod hyxq).2
  subst q
  rcases p with p | r
  · exact Alternating.FinitePath.no_incoming_edge_at_start p y hyxq
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

private theorem current_noIncoming
    {x : V} (hx : x ∈ current.initialSet) :
    ¬ ∃ y, (y, x) ∈ current.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hp, rfl⟩ := hx
  change (y, p.initial) ∈ familyEdges
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
    current.paths at hyx
  simp only [familyEdges, Set.mem_iUnion] at hyx
  obtain ⟨q, hq, hyxq⟩ := hyx
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support
    current.isWarp hp hq p.initial_mem_support
      (q.edgeSet_subset_support_prod hyxq).2
  subst q
  rcases p with p | r
  · exact Alternating.FinitePath.no_incoming_edge_at_start p y hyxq
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

theorem roots_noIncoming :
    ∀ x ∈ referencePrefixSeedRoots current X,
      ¬ ∃ y, (y, x) ∈ referencePrefixSeedEdges current X := by
  intro x hx
  rcases hx with hxCurrent | hxPrefix
  · have hxVertex : x ∈ current.vertexSet := by
      obtain ⟨p, hp, rfl⟩ := hxCurrent
      exact ⟨p, hp, p.initial_mem_support⟩
    have hnoCurrent : ¬ ∃ y, (y, x) ∈ current.edgeSet :=
      current_noIncoming hxCurrent
    rintro ⟨y, hyx | hyx⟩
    · exact hnoCurrent ⟨y, hyx⟩
    · have hxPrefixVertex :=
        (familyEdges_subset_vertexSet_prod
          (activatedReferencePrefixes C current X) hyx).2
      exact Set.disjoint_left.1 vertexSets_disjoint hxVertex hxPrefixVertex
  · have hxPrefixVertex :
        x ∈ Gamma.vertexSet (activatedReferencePrefixes C current X) := by
      obtain ⟨p, hp, rfl⟩ := hxPrefix
      exact ⟨p, hp, p.initial_mem_support⟩
    have hnoPrefix : ¬ ∃ y,
        (y, x) ∈ familyEdges (activatedReferencePrefixes C current X) :=
      prefix_noIncoming hxPrefix
    rintro ⟨y, hyx | hyx⟩
    · have hxCurrent := by
        change (y, x) ∈ familyEdges
          (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
          current.paths at hyx
        exact (familyEdges_subset_vertexSet_prod
          (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
          current.paths hyx).2
      exact Set.disjoint_left.1 vertexSets_disjoint hxCurrent hxPrefixVertex
    · exact hnoPrefix ⟨y, hyx⟩

theorem current_initialSet_subset_roots :
    current.initialSet ⊆ referencePrefixSeedRoots current X :=
  Set.subset_union_left

/-- The activated-prefix seed has an actual root-reachable orientation and
retains the whole current blueprint. -/
theorem exists_blueprint :
    ∃ A : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      current.OrdinaryExtends A ∧
      A.edgeSet = RootReachableRelation.edges
        (referencePrefixSeedEdges current X)
        (referencePrefixSeedRoots current X) ∧
      A.vertexSet = RootReachableRelation.carrier
        (referencePrefixSeedEdges current X)
        (referencePrefixSeedRoots current X) ∧
      A.initialSet = referencePrefixSeedRoots current X := by
  obtain ⟨A, hext, hE, hV, hI, _hT⟩ :=
    exists_rootReachableBlueprint_extending current
      (referencePrefixSeedEdges current X)
      (referencePrefixSeedRoots current X)
      edges_subset_imaginaryGraph edges_biUnique roots_noIncoming
      Set.subset_union_left current_initialSet_subset_roots
  exact ⟨A, hext, hE, hV, hI⟩

/-- The reachable restriction discards nothing from the two rooted input
families, so the seed has their exact edge and vertex unions. -/
theorem exists_blueprint_exact :
    ∃ A : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      current.OrdinaryExtends A ∧
      A.edgeSet = referencePrefixSeedEdges current X ∧
      A.vertexSet = current.vertexSet ∪
        Gamma.vertexSet (activatedReferencePrefixes C current X) ∧
      A.initialSet = referencePrefixSeedRoots current X := by
  obtain ⟨A, hext, hAE, hAV, hAI⟩ := exists_blueprint
    (C := C) (current := current) (X := X)
  let E := referencePrefixSeedEdges current X
  let R := referencePrefixSeedRoots current X
  have hpInitialCarrier :
      Gamma.initialSet (activatedReferencePrefixes C current X) ⊆
        RootReachableRelation.carrier E R := by
    intro x hx
    apply RootReachableRelation.roots_subset_carrier E R
    exact Or.inr hx
  have hpEdges : familyEdges (activatedReferencePrefixes C current X) ⊆
      RootReachableRelation.edges E R := by
    apply RootReachableRelation.family_edges_retained E R
    · exact Set.subset_union_right
    · exact hpInitialCarrier
  have hpVertices :
      Gamma.vertexSet (activatedReferencePrefixes C current X) ⊆
        RootReachableRelation.carrier E R := by
    apply RootReachableRelation.family_vertices_retained E R
    · exact Set.subset_union_right
    · exact hpInitialCarrier
  have hEdgeEq : A.edgeSet = E := by
    apply Set.Subset.antisymm
    · rw [hAE]
      exact RootReachableRelation.edges_subset E R
    · rintro e (he | he)
      · exact hext.2 he
      · rw [hAE]
        exact hpEdges he
  have hRootUnion : R ⊆ current.vertexSet ∪
      Gamma.vertexSet (activatedReferencePrefixes C current X) := by
    intro x hx
    rcases hx with hx | hx
    · left
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨p, hp, p.initial_mem_support⟩
    · right
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨p, hp, p.initial_mem_support⟩
  have hEUnion : ∀ e ∈ E,
      e.1 ∈ current.vertexSet ∪
          Gamma.vertexSet (activatedReferencePrefixes C current X) ∧
        e.2 ∈ current.vertexSet ∪
          Gamma.vertexSet (activatedReferencePrefixes C current X) := by
    intro e he
    rcases he with he | he
    · change e ∈ familyEdges
        (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
        current.paths at he
      have hend := familyEdges_subset_vertexSet_prod
        (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
        current.paths he
      exact ⟨Or.inl hend.1, Or.inl hend.2⟩
    · have hend := familyEdges_subset_vertexSet_prod
        (activatedReferencePrefixes C current X) he
      exact ⟨Or.inr hend.1, Or.inr hend.2⟩
  have hVertexEq : A.vertexSet = current.vertexSet ∪
      Gamma.vertexSet (activatedReferencePrefixes C current X) := by
    apply Set.Subset.antisymm
    · rw [hAV]
      exact RootReachableRelation.carrier_subset E R hRootUnion hEUnion
    · intro x hx
      rcases hx with hx | hx
      · exact hext.1 hx
      · rw [hAV]
        exact hpVertices hx
  exact ⟨A, hext, hEdgeEq, hVertexEq, hAI⟩

/-- Every seed vertex remains under the old displayed roof. -/
theorem blueprint_vertices_roofed
    {A : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hAV : A.vertexSet = current.vertexSet ∪
      Gamma.vertexSet (activatedReferencePrefixes C current X)) :
    A.vertexSet ⊆ Gamma.roof C.newSlice := by
  rw [hAV]
  apply Set.union_subset
  · exact hcurrent.vertices_roofed
  · rintro x ⟨p, hp, hxp⟩
    exact ladderReference.vertexSet_subset_roof C.legal
      (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
        C.legal C.newStage) ⟨p, hp.1.1, hxp⟩

#print axioms edges_biUnique
#print axioms roots_noIncoming
#print axioms exists_blueprint
#print axioms exists_blueprint_exact
#print axioms blueprint_vertices_roofed

end referencePrefixSeed
end Erdos599.Blueprint.LinkageBlueprint

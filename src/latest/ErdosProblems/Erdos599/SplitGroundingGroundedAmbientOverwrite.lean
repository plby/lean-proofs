/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableRootDefect

/-!
# Local ambient-prefix exchange for grounded split root defects

An ambient source prefix need not lie in the limiting-ladder family.  In the
external last-deleted-edge branch, the honest local repair removes every old
edge incident with that finite prefix and inserts the prefix edges.  This
module proves that the resulting relation is still a bi-unique subrelation
of the ambient graph, roots the displayed endpoint, and damages only finitely
many old edges.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Replace all old incidence on a finite path by the directed path itself. -/
def splitGroundedAmbientPrefixOverwriteEdges
    (E : Set (V × V)) (p : FinitePath Gamma.graph) : Set (V × V) :=
  (E \ (p.support ×ˢ (Set.univ : Set V) ∪
    (Set.univ : Set V) ×ˢ p.support)) ∪ p.edgeSet

/-- Old relation edges removed by the prefix overwrite. -/
def splitGroundedAmbientPrefixDamagedEdges
    (E : Set (V × V)) (p : FinitePath Gamma.graph) : Set (V × V) :=
  E \ splitGroundedAmbientPrefixOverwriteEdges E p

theorem FinitePath.edgeSet_subset_splitGroundedAmbientPrefixOverwriteEdges
    (p : FinitePath Gamma.graph) (E : Set (V × V)) :
    p.edgeSet ⊆ splitGroundedAmbientPrefixOverwriteEdges E p :=
  Set.subset_union_right

theorem mem_splitGroundedAmbientPrefixOverwriteEdges_of_disjoint_endpoints
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ E) (hx : x ∉ p.support) (hy : y ∉ p.support) :
    (x, y) ∈ splitGroundedAmbientPrefixOverwriteEdges E p := by
  left
  refine ⟨hxy, ?_⟩
  rintro (hleft | hright)
  · exact hx hleft.1
  · exact hy hright.2

private theorem finite_oldEdges_with_tail_in_prefix
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.RightUnique (fun x y ↦ (x, y) ∈ E)) :
    {e | e ∈ E ∧ e.1 ∈ p.support}.Finite := by
  apply Set.Finite.of_finite_image
  · apply p.support_finite.subset
    rintro x ⟨e, he, rfl⟩
    exact he.2
  · intro e he f hf hefst
    apply Prod.ext hefst
    apply hE he.1
    rw [hefst]
    exact hf.1

private theorem finite_oldEdges_with_head_in_prefix
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.LeftUnique (fun x y ↦ (x, y) ∈ E)) :
    {e | e ∈ E ∧ e.2 ∈ p.support}.Finite := by
  apply Set.Finite.of_finite_image
  · apply p.support_finite.subset
    rintro x ⟨e, he, rfl⟩
    exact he.2
  · intro e he f hf hefsnd
    apply Prod.ext
    · apply hE he.1
      rw [hefsnd]
      exact hf.1
    · exact hefsnd

/-- A finite prefix damages only finitely many edges of a bi-unique old
relation. -/
theorem splitGroundedAmbientPrefixDamagedEdges_finite
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    (splitGroundedAmbientPrefixDamagedEdges E p).Finite := by
  apply (finite_oldEdges_with_tail_in_prefix hE.2 |>.union
    (finite_oldEdges_with_head_in_prefix hE.1)).subset
  rintro ⟨x, y⟩ hxy
  by_cases hx : x ∈ p.support
  · exact Or.inl ⟨hxy.1, hx⟩
  · by_cases hy : y ∈ p.support
    · exact Or.inr ⟨hxy.1, hy⟩
    · exact False.elim (hxy.2
        (mem_splitGroundedAmbientPrefixOverwriteEdges_of_disjoint_endpoints
          hxy.1 hx hy))

/-- The overwrite stays inside the ambient digraph. -/
theorem splitGroundedAmbientPrefixOverwriteEdges_subset_adj
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : E ⊆ {e | Gamma.graph.Adj e.1 e.2}) :
    splitGroundedAmbientPrefixOverwriteEdges E p ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact hE he.1
  · exact p.edgeSet_subset_adj he

/-- Overwriting a bi-unique relation by a finite simple path is bi-unique. -/
theorem splitGroundedAmbientPrefixOverwriteEdges_biUnique
    {E : Set (V × V)} {p : FinitePath Gamma.graph}
    (hE : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈
        splitGroundedAmbientPrefixOverwriteEdges E p) := by
  have hp : Relator.BiUnique (fun x y ↦ (x, y) ∈ p.edgeSet) :=
    Alternating.Path.edgeSet_biUnique (.inl p)
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hE.1 hxz.1 hyz.1
    · have hz : z ∈ p.support :=
        (p.edgeSet_subset_support_prod hyz).2
      exact False.elim (hxz.2 (Or.inr ⟨Set.mem_univ x, hz⟩))
    · have hz : z ∈ p.support :=
        (p.edgeSet_subset_support_prod hxz).2
      exact False.elim (hyz.2 (Or.inr ⟨Set.mem_univ y, hz⟩))
    · exact hp.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hE.2 hxy.1 hxz.1
    · have hx : x ∈ p.support :=
        (p.edgeSet_subset_support_prod hxz).1
      exact False.elim (hxy.2 (Or.inl ⟨hx, Set.mem_univ y⟩))
    · have hx : x ∈ p.support :=
        (p.edgeSet_subset_support_prod hxy).1
      exact False.elim (hxz.2 (Or.inl ⟨hx, Set.mem_univ z⟩))
    · exact hp.2 hxy hxz

/-- The inserted prefix is a literal reachability chain in the overwrite. -/
theorem FinitePath.start_reaches_finish_splitGroundedAmbientPrefixOverwriteEdges
    (p : FinitePath Gamma.graph) (E : Set (V × V)) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        splitGroundedAmbientPrefixOverwriteEdges E p)
      p.start p.finish := by
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ p.edgeSet)
    (p := fun x y ↦ (x, y) ∈
      splitGroundedAmbientPrefixOverwriteEdges E p)
  · intro x y hxy
    exact Set.subset_union_right hxy
  · exact Alternating.Walk.reflTransGen_edgeSet p.walk

/-- Every overwrite edge stays entirely inside or entirely outside the
inserted prefix carrier. -/
theorem splitGroundedAmbientPrefixOverwriteEdges_mem_support_iff
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ splitGroundedAmbientPrefixOverwriteEdges E p) :
    x ∈ p.support ↔ y ∈ p.support := by
  rcases hxy with hold | hpath
  · have hx : x ∉ p.support := by
      intro hx
      exact hold.2 (Or.inl ⟨hx, Set.mem_univ y⟩)
    have hy : y ∉ p.support := by
      intro hy
      exact hold.2 (Or.inr ⟨Set.mem_univ x, hy⟩)
    exact iff_of_false hx hy
  · have hend := p.edgeSet_subset_support_prod hpath
    exact iff_of_true hend.1 hend.2

/-- Reachability in the overwrite cannot cross the inserted carrier. -/
theorem reflTransGen_splitGroundedAmbientPrefixOverwriteEdges_mem_support_iff
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ splitGroundedAmbientPrefixOverwriteEdges E p)
      x y) :
    x ∈ p.support ↔ y ∈ p.support := by
  induction hxy with
  | refl => exact Iff.rfl
  | tail hxy hyz ih =>
      exact ih.trans
        (splitGroundedAmbientPrefixOverwriteEdges_mem_support_iff hyz)

/-- A chain starting outside the inserted carrier uses only old edges. -/
theorem reflTransGen_old_of_splitGroundedAmbientPrefixOverwriteEdges
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {x y : V}
    (hxy : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ splitGroundedAmbientPrefixOverwriteEdges E p)
      x y)
    (hx : x ∉ p.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) x y := by
  induction hxy with
  | refl => exact .refl
  | @tail y z hxy hyz ih =>
      have hy : y ∉ p.support := by
        intro hyMem
        exact hx
          ((reflTransGen_splitGroundedAmbientPrefixOverwriteEdges_mem_support_iff
            hxy).mpr hyMem)
      have hyzOld : (y, z) ∈ E := by
        rcases hyz with hold | hpath
        · exact hold.1
        · exact False.elim
            (hy (p.edgeSet_subset_support_prod hpath).1)
      exact .tail ih hyzOld

/-- An old reachability antichain stays an antichain when the inserted
prefix contains no other displayed boundary point. -/
theorem isReachabilityAntichain_splitGroundedAmbientPrefixOverwriteEdges
    {E : Set (V × V)} {p : FinitePath Gamma.graph} {B : Set V}
    (hanti : IsReachabilityAntichain E B)
    (hfirst : p.support ∩ B ⊆ {p.finish}) :
    IsReachabilityAntichain
      (splitGroundedAmbientPrefixOverwriteEdges E p) B := by
  intro b hb c hc hbc
  by_cases hbPath : b ∈ p.support
  · have hcPath : c ∈ p.support :=
      (reflTransGen_splitGroundedAmbientPrefixOverwriteEdges_mem_support_iff
        hbc).mp hbPath
    have hbf : b = p.finish := by
      simpa only [Set.mem_singleton_iff] using hfirst ⟨hbPath, hb⟩
    have hcf : c = p.finish := by
      simpa only [Set.mem_singleton_iff] using hfirst ⟨hcPath, hc⟩
    exact hbf.trans hcf.symm
  · exact hanti hb hc
      (reflTransGen_old_of_splitGroundedAmbientPrefixOverwriteEdges
        hbc hbPath)

/-- A previously available finite root path survives if none of its edges
is incident with the inserted carrier. -/
theorem FinitePath.start_reaches_finish_splitGroundedAmbientPrefixOverwriteEdges_of_avoids
    {E : Set (V × V)} {p q : FinitePath Gamma.graph}
    (hqE : q.edgeSet ⊆ E)
    (havoid : ∀ e ∈ q.edgeSet,
      e.1 ∉ p.support ∧ e.2 ∉ p.support) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ splitGroundedAmbientPrefixOverwriteEdges E p)
      q.start q.finish := by
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ q.edgeSet)
    (p := fun x y ↦ (x, y) ∈
      splitGroundedAmbientPrefixOverwriteEdges E p)
  · intro x y hxy
    exact mem_splitGroundedAmbientPrefixOverwriteEdges_of_disjoint_endpoints
      (hqE hxy) (havoid (x, y) hxy).1 (havoid (x, y) hxy).2
  · exact Alternating.Walk.reflTransGen_edgeSet q.walk

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

/-- Concrete relation-level exchange in the external whole-source branch. -/
structure SplitGroundedWholeSourceExternalAmbientPrefixExchange
    (O : L.SplitGroundedReachableWholeSourceRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)) where
  data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O
  edge_not_family : (data.tail, data.deleted.head) ∉
    (L.splitGroundedPopularAuxiliaryInput hL.legal).familyEdges

namespace SplitGroundedWholeSourceExternalAmbientPrefixExchange

def edges
    (X : L.SplitGroundedWholeSourceExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) : Set (V × V) :=
  splitGroundedAmbientPrefixOverwriteEdges
    (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅) X.data.path

theorem edges_subset_adj
    (X : L.SplitGroundedWholeSourceExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    X.edges ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  splitGroundedAmbientPrefixOverwriteEdges_subset_adj
    (L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj hL hground S ∅)

theorem edges_biUnique
    (X : L.SplitGroundedWholeSourceExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ X.edges) :=
  splitGroundedAmbientPrefixOverwriteEdges_biUnique
    (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique hL hground S ∅)

theorem source_reaches_boundary
    (X : L.SplitGroundedWholeSourceExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ X.edges) a O.boundary := by
  refine ⟨X.data.path.start, X.data.path_start_source, ?_⟩
  rw [← X.data.path_finish_boundary]
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ X.data.path.edgeSet)
    (p := fun x y ↦ (x, y) ∈ X.edges)
  · intro x y hxy
    exact Set.subset_union_right hxy
  · exact Alternating.Walk.reflTransGen_edgeSet X.data.path.walk

theorem damaged_finite
    (X : L.SplitGroundedWholeSourceExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    (splitGroundedAmbientPrefixDamagedEdges
      (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅)
      X.data.path).Finite :=
  splitGroundedAmbientPrefixDamagedEdges_finite
    (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique hL hground S ∅)

end SplitGroundedWholeSourceExternalAmbientPrefixExchange

/-- Build the exact local exchange certificate from the external constructor
payload. -/
def SplitGroundedWholeSourceAmbientLastDeletedHeadData.externalExchange
    {O : L.SplitGroundedReachableWholeSourceRootObstruction
      (L.splitGroundedCanonicalUnusedRecord hL hground S)}
    (data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O)
    (edge_not_family : (data.tail, data.deleted.head) ∉
      (L.splitGroundedPopularAuxiliaryInput hL.legal).familyEdges) :
    L.SplitGroundedWholeSourceExternalAmbientPrefixExchange O :=
  { data := data, edge_not_family := edge_not_family }

/-- The analogous local overwrite for an allowed-source ambient prefix in
the essential reserved-root branch. -/
structure SplitGroundedEssentialExternalAmbientPrefixExchange
    (O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)) where
  data : L.SplitGroundedEssentialAllowedAmbientLastDeletedHeadData O
  edge_not_family : (data.tail, data.deleted.head) ∉
    (L.splitGroundedPopularAuxiliaryInput hL.legal).familyEdges

namespace SplitGroundedEssentialExternalAmbientPrefixExchange

def edges
    (X : L.SplitGroundedEssentialExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) : Set (V × V) :=
  splitGroundedAmbientPrefixOverwriteEdges
    (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅) X.data.path

theorem edges_subset_adj
    (X : L.SplitGroundedEssentialExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    X.edges ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  splitGroundedAmbientPrefixOverwriteEdges_subset_adj
    (L.splitGroundedCanonicalSwitchedEdgesAt_subset_adj hL hground S ∅)

theorem edges_biUnique
    (X : L.SplitGroundedEssentialExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ X.edges) :=
  splitGroundedAmbientPrefixOverwriteEdges_biUnique
    (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique hL hground S ∅)

theorem allowed_source_reaches_boundary
    (X : L.SplitGroundedEssentialExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    ∃ a ∈ Gamma.source \ {
        (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ X.edges)
        a O.obstruction.boundary := by
  refine ⟨X.data.path.start, X.data.path_start_allowed, ?_⟩
  rw [← X.data.path_finish_boundary]
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ X.data.path.edgeSet)
    (p := fun x y ↦ (x, y) ∈ X.edges)
  · intro x y hxy
    exact Set.subset_union_right hxy
  · exact Alternating.Walk.reflTransGen_edgeSet X.data.path.walk

theorem damaged_finite
    (X : L.SplitGroundedEssentialExternalAmbientPrefixExchange
      (hL := hL) (hground := hground) (S := S) O) :
    (splitGroundedAmbientPrefixDamagedEdges
      (L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅)
      X.data.path).Finite :=
  splitGroundedAmbientPrefixDamagedEdges_finite
    (L.splitGroundedCanonicalSwitchedEdgesAt_biUnique hL hground S ∅)

end SplitGroundedEssentialExternalAmbientPrefixExchange

def SplitGroundedEssentialAllowedAmbientLastDeletedHeadData.externalExchange
    {O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)}
    (data : L.SplitGroundedEssentialAllowedAmbientLastDeletedHeadData O)
    (edge_not_family : (data.tail, data.deleted.head) ∉
      (L.splitGroundedPopularAuxiliaryInput hL.legal).familyEdges) :
    L.SplitGroundedEssentialExternalAmbientPrefixExchange O :=
  { data := data, edge_not_family := edge_not_family }

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.splitGroundedAmbientPrefixOverwriteEdges_biUnique
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedWholeSourceExternalAmbientPrefixExchange.source_reaches_boundary
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedEssentialExternalAmbientPrefixExchange.allowed_source_reaches_boundary

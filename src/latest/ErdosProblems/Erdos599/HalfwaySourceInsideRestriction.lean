/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompleteInsideFamily
import ErdosProblems.Erdos599.PathFilterComponents

/-!
# The literal inside restriction `W[X]`

Notation 2.2 defines `W[X]` to have carrier `X ∩ V[W]` and exactly those
edges of `W` whose two endpoints lie in `X`.  This is the later-row input to
the diamond `A \diamond W[X]` in Assertion 9.31.

The existing canonical cut family has a different, later purpose: it also
inserts uncovered outside-fragment endpoints so that the compressed
assignment edges have a carrier.  It therefore must not be identified with
the literal `W[X]`.  Here we construct the exact source restriction first.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The edge relation of the source notation `W[X]`. -/
def sourceInsideEdges (W : Set Gamma.DPath) (X : Set V) : Set (V × V) :=
  familyEdges W ∩ (X ×ˢ X)

/-- The exact carrier of the source notation `W[X]`. -/
def sourceInsideCarrier (W : Set Gamma.DPath) (X : Set V) : Set V :=
  Gamma.vertexSet W ∩ X

/-- An honest finite-character path-family realization of `W[X]`. -/
structure SourceInsideRestriction (W : Set Gamma.DPath) (X : Set V) where
  family : LinkageBlueprint Gamma Y kappa
  finiteCharacter :
    (imaginaryWeb Gamma Y kappa).HasFiniteCharacter family.paths
  edgeSet_eq : family.edgeSet = sourceInsideEdges W X
  vertexSet_eq : family.vertexSet = sourceInsideCarrier W X

namespace SourceInsideRestriction

variable {W : Set Gamma.DPath} {X : Set V}

@[simp] theorem family_edgeSet (I : SourceInsideRestriction
    (Y := Y) (kappa := kappa) W X) :
    I.family.edgeSet = familyEdges W ∩ (X ×ˢ X) :=
  I.edgeSet_eq

@[simp] theorem family_vertexSet (I : SourceInsideRestriction
    (Y := Y) (kappa := kappa) W X) :
    I.family.vertexSet = Gamma.vertexSet W ∩ X :=
  I.vertexSet_eq

theorem edges_subset_row (I : SourceInsideRestriction
    (Y := Y) (kappa := kappa) W X) :
    I.family.edgeSet ⊆ familyEdges W := by
  rw [I.family_edgeSet]
  exact Set.inter_subset_left

theorem vertices_subset_row (I : SourceInsideRestriction
    (Y := Y) (kappa := kappa) W X) :
    I.family.vertexSet ⊆ Gamma.vertexSet W := by
  rw [I.family_vertexSet]
  exact Set.inter_subset_left

theorem vertices_subset_closure (I : SourceInsideRestriction
    (Y := Y) (kappa := kappa) W X) :
    I.family.vertexSet ⊆ X := by
  rw [I.family_vertexSet]
  exact Set.inter_subset_right

end SourceInsideRestriction

private theorem sourceInsideEdges_endpoints
    (W : Set Gamma.DPath) (X : Set V) {e : V × V}
    (he : e ∈ sourceInsideEdges W X) :
    e.1 ∈ sourceInsideCarrier W X ∧
      e.2 ∈ sourceInsideCarrier W X := by
  have hend := familyEdges_subset_vertexSet_prod W he.1
  exact ⟨⟨hend.1, he.2.1⟩, ⟨hend.2, he.2.2⟩⟩

/-- The literal source restriction exists for every finite-character warp.
The forward orientation is only a path decomposition of the already fixed
relation; the two exact equations retain the definition of `W[X]`. -/
theorem exists_sourceInsideRestriction
    (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (SourceInsideRestriction (Y := Y) (kappa := kappa) W X) := by
  let E : Set (V × V) := sourceInsideEdges W X
  let C : Set V := sourceInsideCarrier W X
  have hgraph : E ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
    intro e he
    exact original_adj_imaginaryGraph (familyEdges_subset_adj W he.1)
  have hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    exact sourceInsideEdges_endpoints W X he
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    have hfamily := Alternating.IsWarp.familyEdges_biUnique hW
    constructor
    · intro x y z hxz hyz
      exact hfamily.1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact hfamily.2 hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨K, hK⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      hW ⟨K, hK.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hW ⟨R, fun n ↦ (hR n).1⟩
  have hforward : ¬ ContainsDirectedRay E := by
    rintro ⟨R, hR⟩
    exact Alternating.familyEdges_not_containsDirectedRay hW hfinite
      ⟨R, hR.trans (fun _ he ↦ he.1)⟩
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    E C hgraph hendpoints hunique hcycle hreverse
  let F : LinkageBlueprint Gamma Y kappa := orientationBlueprint O
  have hFfinite :
      (imaginaryWeb Gamma Y kappa).HasFiniteCharacter F.paths := by
    change (imaginaryWeb Gamma Y kappa).HasFiniteCharacter O.rootPaths
    apply DWeb.forwardOrientation_rootPaths_finite_of_noRay
      (imaginaryWeb Gamma Y kappa) O
    rwa [hOE]
  refine ⟨{
    family := F
    finiteCharacter := hFfinite
    edgeSet_eq := ?_
    vertexSet_eq := ?_ }⟩
  · change (orientationBlueprint O).edgeSet = E
    rw [orientationBlueprint_edgeSet, hOE]
  · change (orientationBlueprint O).vertexSet = C
    rw [orientationBlueprint_vertexSet, hOC]

#print axioms exists_sourceInsideRestriction
#print axioms SourceInsideRestriction.family_edgeSet
#print axioms SourceInsideRestriction.family_vertexSet

end Erdos599.Blueprint.LinkageBlueprint

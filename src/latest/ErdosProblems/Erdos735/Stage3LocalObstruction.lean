/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.BadNeighborLocal

/-!
# Exact local obstruction interface for Stage 3

The four constructors below are precisely the negations of the four local
non-exceptional inputs in `ReducedStage3Geometry` after the donation-edge
freeness field has been discharged by `BadNeighborLocal`.
-/

open Classical
noncomputable section

namespace Erdos735.ABKPR.Data

universe uV uE uF

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

/-- A completely explicit witness to one of the four remaining local
failures in the Stage-3 donation packing. -/
inductive Stage3LocalObstruction : Prop
  | triangleTwoBad
      (t : Face) (ht : C.faceDegree t = 3)
      (i j : Fin (C.faceDegree t)) (hij : i ≠ j)
      (hi : i ∈ A.badNeighborIndices t)
      (hj : j ∈ A.badNeighborIndices t)
  | donationEdgeCollision
      (f : Face) (x y : A.donationRecipients f) (hxy : x ≠ y)
      (hedge : A.donationEdgeOfGeometry f x = A.donationEdgeOfGeometry f y)
  | donationVertexCollision
      (f : Face) (x y : A.donationRecipients f) (hxy : x ≠ y)
      (hvertex : A.donationVertexOfGeometry f x = A.donationVertexOfGeometry f y)
  | twoBadAtDonationVertex
      (f : Face) (x : A.donationRecipients f)
      (i : Fin (C.faceDegree f))
      (hvertex : A.donationVertexOfGeometry f x = ABKPR.faceSucc C f i)
      (hi : i ∈ A.badNeighborIndices f)
      (hsucc : ABKPR.faceSucc C f i ∈ A.badNeighborIndices f)

/-- A finite set has cardinality at most one exactly when it has no two
distinct members, specialized to bad-neighbour indices. -/
theorem badNeighborCount_le_one_of_pairwise_eq
    (t : Face)
    (hpair : ∀ i j, i ∈ A.badNeighborIndices t →
      j ∈ A.badNeighborIndices t → i = j) :
    A.badNeighborCount t ≤ 1 := by
  rw [ABKPR.Data.badNeighborCount]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact hpair i j hi hj

/-- If there is no explicit local obstruction, the four nontrivial fields
needed for the reduced Stage-3 package all hold. -/
noncomputable def reducedStage3Geometry_of_no_localObstruction
    (hrest : A.EndpointRestriction)
    (hno : ¬ A.Stage3LocalObstruction) :
    A.ReducedStage3Geometry := by
  apply ReducedStage3Geometry.ofDonationGeometry A
  · intro t ht
    apply A.badNeighborCount_le_one_of_pairwise_eq
    intro i j hi hj
    by_contra hij
    exact hno (.triangleTwoBad t ht i j hij hi hj)
  · intro f x y hedge
    by_contra hxy
    exact hno (.donationEdgeCollision f x y hxy hedge)
  · exact A.donationEdgeOfGeometry_free hrest
  · intro f x y hvertex
    by_contra hxy
    exact hno (.donationVertexCollision f x y hxy hvertex)
  · intro f x i hvertex hi hsucc
    exact hno (.twoBadAtDonationVertex f x i hvertex hi hsucc)

/-- Pure logic packages the local geometry problem in its final exact form:
either one of the four explicit configurations occurs, or all of Stage 3 is
available. -/
theorem localObstruction_or_reducedStage3Geometry
    (hrest : A.EndpointRestriction) :
    A.Stage3LocalObstruction ∨ Nonempty A.ReducedStage3Geometry := by
  classical
  by_cases h : A.Stage3LocalObstruction
  · exact Or.inl h
  · exact Or.inr ⟨A.reducedStage3Geometry_of_no_localObstruction hrest h⟩

/-- Once every explicit local obstruction is recognized as exceptional,
the desired exceptional-or-Stage-3 conclusion follows without any remaining
combinatorial assumptions. -/
theorem exceptional_or_reducedStage3Geometry
    {Exceptional : Prop} (hrest : A.EndpointRestriction)
    (hexceptional : A.Stage3LocalObstruction → Exceptional) :
    Exceptional ∨ Nonempty A.ReducedStage3Geometry := by
  rcases A.localObstruction_or_reducedStage3Geometry hrest with h | h
  · exact Or.inl (hexceptional h)
  · exact Or.inr h

end Erdos735.ABKPR.Data

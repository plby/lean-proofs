/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.PolarBoundaryAcross
import ErdosProblems.Erdos735.ProjectiveBoundaryExtraction

/-!
# Globally oriented vertices of the concrete polar boundary

The supporting covector at a corner of a polar face polygon is a nonzero
homogeneous representative of a projective arrangement vertex.  A generic
projective chart gives that representative a canonical sheet.  This file
therefore maps every indexed polar corner into the one global type
`projectiveVertices B × Bool` and proves the basic incidence and
nondegeneracy facts needed to identify corners across adjacent faces.
-/

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.ConcretePolarOrientedVertex

open ProjectiveArrangement SignVector
open SignVector.PolarFace SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryAcross
open ProjectiveBoundaryExtraction ChartOrder

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := {b // b ∈ B}
abbrev Vertex (B : Finset Point) := {v // v ∈ projectiveVertices B}
abbrev OrientedVertex (B : Finset Point) := Vertex B × Bool

variable {B : Finset Point} [Nonempty (Line B)]

theorem normal_cross (i j : Line B) (hij : i ≠ j) :
    normals B i ⨯₃ normals B j ≠ 0 := by
  apply normalVec_cross_ne_zero
  intro h
  exact hij (Subtype.ext h)

variable (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)

/-- Homogeneous covector at the projective vertex immediately before edge `i`. -/
noncomputable def boundaryCornerVector
    (f : StrictFace (normals B))
    (i : BoundaryIndex (normals B) f) : Vec3 :=
  cornerVector f (faceWitness_realizes (normals B) f) normal_cross hspan
    ((finRotate _).symm i)

theorem boundaryCornerVector_ne_zero
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    boundaryCornerVector hspan f i ≠ 0 := by
  exact cornerVector_ne_zero f (faceWitness_realizes (normals B) f)
    normal_cross hspan ((finRotate _).symm i)

theorem boundaryCorner_projectivization
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    Projectivization.mk ℝ (boundaryCornerVector hspan f i)
        (boundaryCornerVector_ne_zero hspan f i) =
      boundaryVertex (normals B) normal_cross hspan f i := by
  exact cornerProjectiveVertex_eq_boundaryProjectiveVertex f
    (faceWitness_realizes (normals B) f) normal_cross hspan ((finRotate _).symm i)

theorem boundaryVertex_mem_projectiveVertices
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    boundaryVertex (normals B) normal_cross hspan f i ∈ projectiveVertices B := by
  let t := (finRotate _).symm i
  let a : Line B := boundaryOwner f (faceWitness_realizes (normals B) f)
    normal_cross hspan t
  let b : Line B := boundaryOwner f (faceWitness_realizes (normals B) f)
    normal_cross hspan (Erdos957.cyclicSucc t)
  have hab : a ≠ b := boundaryOwner_ne_succ f
    (faceWitness_realizes (normals B) f) normal_cross hspan t
  let pq : DistinctPointPair B := ⟨(a, b), hab⟩
  have hv : boundaryVertex (normals B) normal_cross hspan f i =
      indexedIntersection B pq := by
    rfl
  rw [hv]
  exact indexedIntersection_mem_projectiveVertices B pq

theorem chart_boundaryCornerVector_ne_zero
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    chartF B (boundaryCornerVector hspan f i) ≠ 0 := by
  intro hzero
  let y := boundaryCornerVector hspan f i
  have hy0 : y ≠ 0 := boundaryCornerVector_ne_zero hspan f i
  have hrepZero : chartF B (Projectivization.mk ℝ y hy0).rep = 0 :=
    (apply_rep_mk_eq_zero_iff (chartF B) y hy0).2 hzero
  rw [boundaryCorner_projectivization hspan f i] at hrepZero
  exact (chart_spec B).1 _ (boundaryVertex_mem_projectiveVertices hspan f i) hrepZero

/-- The sheet selected by the generic chart functional. -/
def boundarySheet (f : StrictFace (normals B))
    (i : BoundaryIndex (normals B) f) : Bool :=
  decide (0 < chartF B (boundaryCornerVector hspan f i))

/-- A boundary corner in the global oriented vertex type. -/
noncomputable def boundaryOrientedVertex
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    OrientedVertex B :=
  (⟨boundaryVertex (normals B) normal_cross hspan f i,
      boundaryVertex_mem_projectiveVertices hspan f i⟩,
    boundarySheet hspan f i)

@[simp] theorem boundaryOrientedVertex_projective
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    (boundaryOrientedVertex hspan f i).1.1 =
      boundaryVertex (normals B) normal_cross hspan f i := rfl

theorem boundaryVertex_ne_succ
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    boundaryVertex (normals B) normal_cross hspan f i ≠
      boundaryVertex (normals B) normal_cross hspan f (Erdos957.cyclicSucc i) := by
  have hs : Erdos957.cyclicSucc ((finRotate _).symm i) = i :=
    (finRotate _).apply_symm_apply i
  have hs' : (finRotate _).symm (Erdos957.cyclicSucc i) = i :=
    (finRotate _).symm_apply_apply i
  change boundaryProjectiveVertex f (faceWitness_realizes (normals B) f)
      normal_cross hspan ((finRotate _).symm i) ≠
    boundaryProjectiveVertex f (faceWitness_realizes (normals B) f)
      normal_cross hspan ((finRotate _).symm (Erdos957.cyclicSucc i))
  simpa only [hs, hs'] using
    boundaryProjectiveVertex_ne_succ f (faceWitness_realizes (normals B) f)
      normal_cross hspan ((finRotate _).symm i)

theorem boundaryOrientedVertex_ne_succ
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    boundaryOrientedVertex hspan f i ≠
      boundaryOrientedVertex hspan f (Erdos957.cyclicSucc i) := by
  intro h
  exact boundaryVertex_ne_succ hspan f i
    (congrArg (fun v : OrientedVertex B ↦ v.1.1) h)

theorem chartF_vertex_rep_ne_zero (v : Vertex B) : chartF B v.1.rep ≠ 0 :=
  (chart_spec B).1 v.1 v.2

/-- Canonical homogeneous representative of a global oriented vertex.  The
`true` sheet is the chart-height-one representative and `false` its negative. -/
noncomputable def orientedRep (v : OrientedVertex B) : Vec3 :=
  if v.2 then chartRep (chartF B) v.1.1 else -chartRep (chartF B) v.1.1

theorem orientedRep_ne_zero (v : OrientedVertex B) : orientedRep v ≠ 0 := by
  unfold orientedRep
  split
  · exact chartRep_nonzero (chartF B) v.1.1 (chartF_vertex_rep_ne_zero v.1)
  · exact neg_ne_zero.mpr
      (chartRep_nonzero (chartF B) v.1.1 (chartF_vertex_rep_ne_zero v.1))

@[simp] theorem chartF_orientedRep (v : OrientedVertex B) :
    chartF B (orientedRep v) = if v.2 then 1 else -1 := by
  unfold orientedRep
  split <;> simp [apply_chartRep, chartF_vertex_rep_ne_zero]

theorem orientedRep_projectivization (v : OrientedVertex B) :
    Projectivization.mk ℝ (orientedRep v) (orientedRep_ne_zero v) = v.1.1 := by
  let p := v.1.1
  let hp := chartF_vertex_rep_ne_zero v.1
  let hrep := chartRep_nonzero (chartF B) p hp
  calc
    Projectivization.mk ℝ (orientedRep v) (orientedRep_ne_zero v) =
        Projectivization.mk ℝ (chartRep (chartF B) p) hrep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      cases hv : v.2
      · exact ⟨-1, by simp [orientedRep, hv, p]⟩
      · exact ⟨1, by simp [orientedRep, hv, p]⟩
    _ = p := mk_chartRep (chartF B) p hp

@[simp] theorem orientedRep_sheet (v : OrientedVertex B) :
    decide (0 < chartF B (orientedRep v)) = v.2 := by
  rw [chartF_orientedRep]
  cases v.2 <;> norm_num

theorem orientedRep_injective : Function.Injective (orientedRep (B := B)) := by
  intro v w h
  apply Prod.ext
  · apply Subtype.ext
    calc
      v.1.1 = Projectivization.mk ℝ (orientedRep v) (orientedRep_ne_zero v) :=
        (orientedRep_projectivization v).symm
      _ = Projectivization.mk ℝ (orientedRep w) (orientedRep_ne_zero w) := by
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
        exact ⟨1, by simpa using h.symm⟩
      _ = w.1.1 := orientedRep_projectivization w
  · calc
      v.2 = decide (0 < chartF B (orientedRep v)) := (orientedRep_sheet v).symm
      _ = decide (0 < chartF B (orientedRep w)) := by rw [h]
      _ = w.2 := orientedRep_sheet w

end Erdos735.ConcretePolarOrientedVertex

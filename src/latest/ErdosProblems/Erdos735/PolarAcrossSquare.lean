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

import ErdosProblems.Erdos735.PolarBoundaryAcross

/-!
# Commuting crossings at two boundary owners

Crossing a literal sign-vector face boundary toggles precisely its owner
coordinate.  Hence crossings at two distinct owners commute whenever both
continuation edges occur on the intermediate faces.
-/

open Classical
noncomputable section
open scoped Matrix

namespace Erdos735.SignVector.PolarBoundaryAcross

open ProjectiveArrangement
open Erdos735.ChartOrder SignVector
open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.PolarBoundaryOrder

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
variable (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
variable (hspan : Submodule.span ℝ (Set.range n) = ⊤)

/-- The face across a literal boundary edge differs at exactly the edge's
owner coordinate. -/
theorem across_face_sign
    (f : StrictFace n) (i : BoundaryIndex n f) (x : I) :
    (across n hn hcross hspan ⟨f, i⟩).1.1 x =
      if x = (boundaryEdge n hcross hspan f i).1.1 then
        !(f.1 x) else f.1 x := by
  let e := boundaryEdge n hcross hspan f i
  rw [across_face_eq_edgeFace_flip n hn hcross hspan ⟨f, i⟩]
  simp only [edgeFace_sign]
  by_cases hx : x = e.1.1
  · subst x
    simp only [e, extendEdgeSign_support, ↓reduceIte]
  · rw [extendEdgeSign_other e.1 _ hx]
    have hinc : FaceEdgeIncident n f e :=
      (mem_faceEdges_iff n f e).mp
        (boundaryEdge_mem n hcross hspan f i)
    rw [← hinc ⟨x, hx⟩]
    simp only [e, hx, ↓reduceIte]

/-- Crossing two distinct boundary owners of one face gives two distinct
opposite faces. -/
theorem across_faces_ne
    (q : StrictFace n) (k j : BoundaryIndex n q) (hkj : k ≠ j) :
    (across n hn hcross hspan ⟨q, k⟩).1 ≠
      (across n hn hcross hspan ⟨q, j⟩).1 := by
  intro hfaces
  let ok := (boundaryEdge n hcross hspan q k).1.1
  let oj := (boundaryEdge n hcross hspan q j).1.1
  have hokj : ok ≠ oj := by
    intro h
    apply hkj
    apply (boundaryOwnerEquiv q (faceWitness_realizes n q)
      hcross hspan).injective
    exact Subtype.ext h
  have hsign := congrArg (fun f : StrictFace n ↦ f.1 ok) hfaces
  rw [across_face_sign n hn hcross hspan,
    across_face_sign n hn hcross hspan] at hsign
  simp only [ok, if_pos, oj, if_neg hokj] at hsign
  exact (Bool.not_eq_self _).mp hsign

/-- The fourth face at a pair of distinct owner crossings is independent
of the order in which the two boundary edges are crossed. -/
theorem across_square_face
    (q : StrictFace n) (k j : BoundaryIndex n q)
    (hkj : k ≠ j)
    (u : BoundaryIndex n (across n hn hcross hspan ⟨q, k⟩).1)
    (i : BoundaryIndex n (across n hn hcross hspan ⟨q, j⟩).1)
    (huowner :
      (boundaryEdge n hcross hspan
        (across n hn hcross hspan ⟨q, k⟩).1 u).1.1 =
          (boundaryEdge n hcross hspan q j).1.1)
    (hiowner :
      (boundaryEdge n hcross hspan
        (across n hn hcross hspan ⟨q, j⟩).1 i).1.1 =
          (boundaryEdge n hcross hspan q k).1.1) :
    (across n hn hcross hspan
      ⟨(across n hn hcross hspan ⟨q, k⟩).1, u⟩).1 =
    (across n hn hcross hspan
      ⟨(across n hn hcross hspan ⟨q, j⟩).1, i⟩).1 := by
  let ok := (boundaryEdge n hcross hspan q k).1.1
  let oj := (boundaryEdge n hcross hspan q j).1.1
  have hokj : ok ≠ oj := by
    intro h
    apply hkj
    apply (boundaryOwnerEquiv q (faceWitness_realizes n q)
      hcross hspan).injective
    exact Subtype.ext h
  apply Subtype.ext
  funext x
  rw [across_face_sign n hn hcross hspan,
    across_face_sign n hn hcross hspan,
    across_face_sign n hn hcross hspan,
    across_face_sign n hn hcross hspan]
  rw [huowner, hiowner]
  change (if x = oj then
      !(if x = ok then !(q.1 x) else q.1 x)
    else if x = ok then !(q.1 x) else q.1 x) =
    (if x = ok then
      !(if x = oj then !(q.1 x) else q.1 x)
    else if x = oj then !(q.1 x) else q.1 x)
  · by_cases hxk : x = ok
    · have hxj : x ≠ oj := by simpa [hxk] using hokj
      simp [hxk, hxj, hokj]
    · by_cases hxj : x = oj
      · simp [hxk, hxj, hokj.symm]
      · simp [hxk, hxj]

end Erdos735.SignVector.PolarBoundaryAcross

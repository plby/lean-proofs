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

import ErdosProblems.Erdos735.PolarAcrossSquare
import ErdosProblems.Erdos735.ConcretePolarABKPRData

open Classical
noncomputable section
open scoped Matrix

namespace Erdos735.ConcretePolarABKPRData

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross
open ConcretePolarOrientedVertex

abbrev AcrossSquarePoint := ProjectiveArrangement.Point

variable {P : Finset AcrossSquarePoint} {w : AcrossSquarePoint → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : AcrossSquarePoint}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

/-- Reindexed concrete form of the literal across-face sign formula. -/
theorem concreteData_across_face_sign
    (q : StrictFace (normals (nonordinaryPoints P)))
    (k : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree q))
    (x : ProjectiveBoundaryExtraction.Line (nonordinaryPoints P)) :
    ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1.1 x =
      if x = ((concreteData hred ha hb hd hncol).boundaryEdge q k).1.1 then
        !(q.1 x) else q.1 x := by
  let E := indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol
  exact SignVector.PolarBoundaryAcross.across_face_sign
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
    normal_cross (hspan ha hb hd hncol) q (E q k) x

/-- Face-level form of the concrete sign formula: crossing a reindexed
boundary edge gives the other canonical `edgeFace` of that strict edge. -/
theorem concreteData_across_face_eq_edgeFace_flip
    (q : StrictFace (normals (nonordinaryPoints P)))
    (k : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree q)) :
    ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1 =
      edgeFace (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P))
        ((concreteData hred ha hb hd hncol).boundaryEdge q k)
        (!(q.1 ((concreteData hred ha hb hd hncol).boundaryEdge q k).1.1)) := by
  let DD := concreteData hred ha hb hd hncol
  let e := DD.boundaryEdge q k
  apply Subtype.ext
  funext x
  rw [concreteData_across_face_sign hred ha hb hd hncol]
  change (if x = e.1.1 then !(q.1 x) else q.1 x) =
    extendEdgeSign e.1 (!(q.1 e.1.1)) x
  by_cases hx : x = e.1.1
  · subst x
    simp
  · rw [if_neg hx, extendEdgeSign_other _ _ hx]
    have heinc : FaceEdgeIncident (normals (nonordinaryPoints P)) q e := by
      rw [← mem_faceEdges_iff]
      rw [← (ConcretePolarCellulation.boundaryExtraction
        (nonordinaryPoints P) ha hb hd hncol).faceBoundary_toFinset]
      exact List.mem_toFinset.mpr (DD.boundaryEdge_mem q k)
    exact (heinc ⟨x, hx⟩).symm

/-- Distinct reindexed boundary positions lead to distinct opposite literal
polar faces. -/
theorem concreteData_across_faces_ne
    (q : StrictFace (normals (nonordinaryPoints P)))
    (k j : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree q))
    (hkj : k ≠ j) :
    ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1 ≠
      ((concreteData hred ha hb hd hncol).across ⟨q, j⟩).1 := by
  let E := indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol
  apply SignVector.PolarBoundaryAcross.across_faces_ne
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hspan ha hb hd hncol) q (E q k) (E q j)
  exact fun h ↦ hkj ((E q).injective h)

/-- Reindexed concrete form of commuting two distinct literal polar
crossings. -/
theorem concreteData_across_square_face
    (q : StrictFace (normals (nonordinaryPoints P)))
    (k j : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree q))
    (hkj : k ≠ j)
    (u : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree
        ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1))
    (i : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree
        ((concreteData hred ha hb hd hncol).across ⟨q, j⟩).1))
    (huowner :
      ((concreteData hred ha hb hd hncol).boundaryEdge
        ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1 u).1.1 =
      ((concreteData hred ha hb hd hncol).boundaryEdge q j).1.1)
    (hiowner :
      ((concreteData hred ha hb hd hncol).boundaryEdge
        ((concreteData hred ha hb hd hncol).across ⟨q, j⟩).1 i).1.1 =
      ((concreteData hred ha hb hd hncol).boundaryEdge q k).1.1) :
    ((concreteData hred ha hb hd hncol).across
      ⟨((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1, u⟩).1 =
    ((concreteData hred ha hb hd hncol).across
      ⟨((concreteData hred ha hb hd hncol).across ⟨q, j⟩).1, i⟩).1 := by
  let E := indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol
  let pa := PolarBoundaryAcross.across
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hspan ha hb hd hncol)
  have hkj' : E q k ≠ E q j := fun h ↦ hkj ((E q).injective h)
  have hsquare := SignVector.PolarBoundaryAcross.across_square_face
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
    normal_cross (hspan ha hb hd hncol)
    q (E q k) (E q j) hkj'
    (E ((concreteData hred ha hb hd hncol).across ⟨q, k⟩).1 u)
    (E ((concreteData hred ha hb hd hncol).across ⟨q, j⟩).1 i)
    huowner hiowner
  exact hsquare

end Erdos735.ConcretePolarABKPRData

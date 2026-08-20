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

import ErdosProblems.Erdos735.PolarRedChordExtraction

/-!
# Identifying a red chord across two polar faces

At a blue arrangement vertex there is at most one ordinary (red) primal
point.  Thus chord occurrences in different faces whose endpoint projective
vertices agree necessarily come from the same red point.
-/

open Classical
noncomputable section

namespace Erdos735.PolarRedChordExtraction

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector
open SignVector.PolarBoundaryAcross
open ConcretePolarOrientedVertex

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable [Nonempty (BlueLine P)]
variable (hspan : Submodule.span ℝ
  (Set.range (normals (nonordinaryPoints P))) = ⊤)

include hred in
/-- Chords in possibly different polar faces which end at the same concrete
projective blue vertex have the same underlying ordinary point. -/
theorem chordPoint_eq_of_boundaryVertex_eq
    {f g : StrictFace (normals (nonordinaryPoints P))}
    (r : ChordLine (P := P) f) (s : ChordLine (P := P) g)
    {i : BoundaryIndex (normals (nonordinaryPoints P)) f}
    {j : BoundaryIndex (normals (nonordinaryPoints P)) g}
    (hi : i ∈ endpointIndices hspan f r.1)
    (hj : j ∈ endpointIndices hspan g s.1)
    (hv : boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i =
      boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan g j) :
    r.1.1 = s.1.1 := by
  by_contra hrs
  have hrInc : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i) r.1.1 :=
    (Finset.mem_filter.mp hi).2
  have hsInc : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i) s.1.1 := by
    have := (Finset.mem_filter.mp hj).2
    rw [hv]
    exact this
  let v : ProjectiveBoundaryExtraction.Vertex (nonordinaryPoints P) :=
    ⟨boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i,
      boundaryVertex_mem_projectiveVertices hspan f i⟩
  exact RedChordIncidence.no_common_blueVertex_of_distinct_red hred
    r.1.2 s.1.2 hrs v hrInc hsInc

include hred in
/-- Subtype form: the two chord labels themselves agree as ordinary-point
subtypes. -/
theorem chordRedLine_eq_of_boundaryVertex_eq
    {f g : StrictFace (normals (nonordinaryPoints P))}
    (r : ChordLine (P := P) f) (s : ChordLine (P := P) g)
    {i : BoundaryIndex (normals (nonordinaryPoints P)) f}
    {j : BoundaryIndex (normals (nonordinaryPoints P)) g}
    (hi : i ∈ endpointIndices hspan f r.1)
    (hj : j ∈ endpointIndices hspan g s.1)
    (hv : boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i =
      boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan g j) :
    r.1 = s.1 := by
  apply Subtype.ext
  exact chordPoint_eq_of_boundaryVertex_eq hred hspan r s hi hj hv

end Erdos735.PolarRedChordExtraction

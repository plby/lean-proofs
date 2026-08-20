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

import ErdosProblems.Erdos735.RedChordExtraction
import ErdosProblems.Erdos735.RedChordIncidence

/-!
# Reduced-magic specialization of red-chord extraction

For a reduced magic configuration, ordinary dual lines cannot share a blue
arrangement vertex.  This discharges the red-red incidence field of
`RedChordExtraction.Geometry`; only the chamber-intersection and
boundary-owner geometry remain.
-/

open Classical
noncomputable section

namespace Erdos735.RedChordExtraction

open ProjectiveArrangement SignVector
open SignVector.RotationRealization

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable {G : SimpleGraph (BlueVertex (nonordinaryPoints P))}
variable [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (X : RotationRealization (G := G) (blueNormals (nonordinaryPoints P))
  (blueNormals_ne_zero (nonordinaryPoints P)))

theorem no_two_red_at_blueVertex_of_reducedMagic
    (hred : IsReducedMagic P w c)
    (a b : RedLine (ordinaryPoints P)) (hab : a ≠ b)
    (v : BlueVertex (nonordinaryPoints P)) :
    ¬ (Incident v.1 a.1 ∧ Incident v.1 b.1) := by
  rintro ⟨hva, hvb⟩
  exact RedChordIncidence.no_common_blueVertex_of_distinct_red hred
    a.2 b.2 (fun h ↦ hab (Subtype.ext h)) v hva hvb

/-- Build the red-chord geometry for a reduced magic configuration.  The
ordinary-line theorem supplies endpoint disjointness automatically. -/
def Geometry.ofReducedMagic
    (hred : IsReducedMagic P w c)
    (endpoint_card : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (a : RedLine (ordinaryPoints P)),
      a ∈ redChordLines (A := ordinaryPoints P) f →
      (redEndpointIndices (A := ordinaryPoints P) X f a).card = 2)
    (boundary_start_on_owner : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (i : Fin (X.strictC.faceDegree f)),
      Incident (X.boundaryVertex f i).1
        (strictEdgeOwner (X.boundaryEdge f i)).1)
    (boundary_finish_on_owner : ∀
      (f : StrictFace (blueNormals (nonordinaryPoints P)))
      (i : Fin (X.strictC.faceDegree f)),
      Incident (X.boundaryVertex f (X.strictFaceSucc f i)).1
        (strictEdgeOwner (X.boundaryEdge f i)).1) :
    Geometry (A := ordinaryPoints P) (B := nonordinaryPoints P) X where
  endpoint_card := endpoint_card
  boundary_start_on_owner := boundary_start_on_owner
  boundary_finish_on_owner := boundary_finish_on_owner
  no_two_red_at_blueVertex := no_two_red_at_blueVertex_of_reducedMagic hred

end Erdos735.RedChordExtraction

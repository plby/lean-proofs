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

import ErdosProblems.Erdos735.ConcreteStage4FlankExistence
import ErdosProblems.Erdos735.Stage4TriangleFlankRecognition

/-!
# Complete construction of the literal Stage-4 flank graph

The only remaining branch in flank existence is when both cyclic flank
faces of an evil triangle are triangular.  Those two faces occur across
opposite edges of its bad quadrangle, so the concrete opposite-triangle
recognition theorem gives failed Fano.  Outside that exception the geometric
flank bounds, and hence the complete flank lookup system, are unconditional.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4FlankComplete

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

/-- Outside failed Fano, every evil triangle has a literal geometric
helping flank. -/
theorem evil_has_geometric_flank
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :
    ∀ e : (D hred ha hb hd hncol).EvilFace,
      ((D hred ha hb hd hncol).geometricFlanks
        ConcretePolarFlankBounds.edgeLine e).Nonempty := by
  exact ConcreteStage4FlankExistence.evil_has_geometric_flank_of_both_triangles_failedFano
      hred ha hb hd hncol hAcard hnotFF
      (Stage4TriangleFlankRecognition.isFailedFano_of_both_triangle_flanks
        hred ha hb hd hncol hAcard)

/-- All concrete Stage-4 degree bounds with existence included. -/
noncomputable def geometricFlankBounds
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :
    (D hred ha hb hd hncol).GeometricFlankBounds
      (ProjectiveBoundaryExtraction.Line (B (P := P))) :=
  ConcretePolarFlankBounds.geometricFlankBounds hred ha hb hd hncol
    (evil_has_geometric_flank hred ha hb hd hncol hAcard hnotFF)

/-- The complete concrete helping graph lookup system used in Stage 4. -/
noncomputable def flankSystem
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :
    (D hred ha hb hd hncol).FlankSystem
      (ProjectiveBoundaryExtraction.Line (B (P := P))) :=
  (geometricFlankBounds hred ha hb hd hncol hAcard hnotFF).toFlankSystem

@[simp] theorem flankSystem_edgeLine
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :
    (flankSystem hred ha hb hd hncol hAcard hnotFF).edgeLine =
      ConcretePolarFlankBounds.edgeLine := rfl

end Erdos735.ConcreteStage4FlankComplete

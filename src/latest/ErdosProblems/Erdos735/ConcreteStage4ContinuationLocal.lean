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

import ErdosProblems.Erdos735.OppositeTriangleRecognition
import ErdosProblems.Erdos735.Stage4OppositeLine

/-!
# Local exclusions along the Stage-4 opposite line

Across the path edge of an evil bad quadrangle lies the evil triangle.
Consequently a triangle across the opposite edge is exactly the concrete
opposite-triangles failed-Fano obstruction.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4ContinuationLocal

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

/-- Outside failed Fano, the face across the edge opposite an evil path
edge is not triangular. -/
theorem evilBadOpposite_across_not_triangle
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (e : (D hred ha hb hd hncol).EvilFace) :
    (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilBadOppositeDart e)).1 ≠ 3 := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let opposite := ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 bad.2)
  intro htriOpp
  apply hnotFF
  apply OppositeTriangleRecognition.isFailedFano_of_badQuadrangle_opposite_triangles
    hred ha hb hd hncol hAcard bad.1 (DD.evilDart_across_bad e)
    bad.2 opposite
  · have hinv := DD.across_involutive (DD.evilDart e)
    change CC.faceDegree (DD.across ⟨bad.1, bad.2⟩).1 = 3
    have hbadDart : (⟨bad.1, bad.2⟩ : ABKPR.FaceDart CC) = bad := by
      rcases bad with ⟨f, i⟩
      rfl
    rw [hbadDart, hinv]
    exact e.2.1.1
  · exact htriOpp
  · rfl

end Erdos735.ConcreteStage4ContinuationLocal

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

/-!
# Recognition when both flanks of an evil triangle are triangular

The two cyclic neighbours of the evil edge in its bad quadrangle are
opposite edges of that quadrangle.  Thus, if both faces across those edges
are triangles, the opposite-triangles recognition theorem gives failed
Fano.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace Erdos735.Stage4TriangleFlankRecognition

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

/-- If both cyclic flanks of an evil triangle are triangular, their two
edges on the evil bad quadrangle are opposite.  Hence the concrete
opposite-triangles recognition theorem forces failed Fano. -/
theorem isFailedFano_of_both_triangle_flanks
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (e : (D hred ha hb hd hncol).EvilFace)
    (htriNext :
      let bad := (D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)
      let jNext := ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2
      (C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across ⟨bad.1, jNext⟩).1 = 3)
    (htriPrev :
      let bad := (D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)
      let jPrev := ABKPR.faceSucc (C ha hb hd hncol) bad.1
        (ABKPR.faceSucc (C ha hb hd hncol) bad.1
          (ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2))
      (C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across ⟨bad.1, jPrev⟩).1 = 3) :
    IsFailedFano P := by
  let CC := C ha hb hd hncol
  let DD := D hred ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let jNext := ABKPR.faceSucc CC bad.1 bad.2
  let jPrev := ABKPR.faceSucc CC bad.1
    (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 bad.2))
  have hopposite :
      jPrev = ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 jNext) := by
    rfl
  have hop : ConcreteDonationPacking.OppositeTrianglesAtBadQuadrangle DD :=
    .intro bad.1 (DD.evilDart_across_bad e) jNext jPrev
      htriNext htriPrev hopposite
  exact OppositeTriangleRecognition.isFailedFano_of_oppositeTrianglesAtBadQuadrangle
    hred ha hb hd hncol hAcard hop

end Erdos735.Stage4TriangleFlankRecognition

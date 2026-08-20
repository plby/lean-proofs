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

import ErdosProblems.Erdos735.ConcreteDonationNoTwoBad
import ErdosProblems.Erdos735.OppositeTriangleRecognition
import ErdosProblems.Erdos735.TriangleExceptionCardinality

/-!
# Recognition of every concrete Stage-3 local obstruction

The four constructors of `Stage3LocalObstruction` are discharged here:
two bad neighbours at a triangle and a donation-edge collision force the
failed-Fano configuration, while a donation-vertex collision and two bad
donor edges at the donation corner are impossible in the literal polar
cellulation.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace Erdos735.ConcreteStage3ObstructionRecognition

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector

abbrev Point := ProjectiveArrangement.Point
private abbrev B {P : Finset Point} := nonordinaryPoints P
private abbrev C {P : Finset Point} {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarCellulation.blueCellulation (B (P := P)) ha hb hd hncol
private abbrev D {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarABKPRData.concreteData hred ha hb hd hncol

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P))
variable (hd : d ∈ B (P := P))
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (B (P := P)))]

/-- Every one of the four explicit local Stage-3 obstructions for the
literal polar data forces the failed-Fano exception. -/
theorem isFailedFano_of_stage3LocalObstruction
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hobs : (D hred ha hb hd hncol).Stage3LocalObstruction) :
    IsFailedFano P := by
  rcases hobs with
    (_ | _ | _ | _)
  case triangleTwoBad t ht i j hij hi hj =>
    exact TriangleExceptionCardinality.isFailedFano_of_triangleTwoBad
      hred ha hb hd hncol hAcard t ht i j hij hi hj
  case donationEdgeCollision f x y hxy hedge =>
    exact OppositeTriangleRecognition.isFailedFano_of_donationEdgeCollision
      hred ha hb hd hncol hAcard f x y hxy hedge
  case donationVertexCollision f x y hxy hvertex =>
    exact False.elim (hxy
      (ConcreteDonationObstructionRecognition.donationVertexOfGeometry_injective
        hred ha hb hd hncol f hvertex))
  case twoBadAtDonationVertex f x i hvertex hi hsucc =>
    exact False.elim
      (ConcreteDonationObstructionRecognition.no_two_bad_at_donationVertex
        hred ha hb hd hncol f x i hvertex hi hsucc)

end Erdos735.ConcreteStage3ObstructionRecognition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4UniformVolumeDecay
import ErdosProblems.Erdos186.CFP.Bilu.Section92PresentationDescent

/-!
# A concrete body-presentation instance of the Section 4 package

This module fixes the abstract candidate class in
`UniformReducedOuterDecayPackage` to the common rank-indexed body
presentations used by Sections 9.1--9.2.  The formal-coordinate cube closes
the entire bounded-cardinality branch.  Consequently the constructor's
only substantive inputs are the corrected large-cardinality Proposition
7.5 decay step and the terminal body-to-container estimate.
-/

namespace Erdos186.CFP.Bilu.Section4BodyPresentationPackage

open MeasureTheory
open CFP.BiluFreiman
open Section4SmallCardinality
open Section4UniformVolumeDecay
open Section92PresentationDescent
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

/-- Exact real volume of the canonical common-interface cube. -/
theorem bodyVolume_rankedBodyPresentationOfSmallCard
    (A : Finset ℤ) (hA : A.Nonempty) :
    bodyVolume (rankedBodyPresentationOfSmallCard A hA) =
      ((2 : ℕ) ^ A.card : ℝ) := by
  change (volume
      {x : Fin A.card → ℝ | cubeSeminorm A x ≤ 1}).toReal = _
  rw [volume_cubeSeminorm_unitBall A hA]
  norm_num [Measure.real]

/-- Concrete instantiation of the uniform Section 4 package.  Every
structural and bounded-cardinality field is discharged here; `hdecay` is
exactly the corrected large-cardinality Proposition 7.5 conclusion, and
`hrealize` is the stopped-body volume-to-container conversion. -/
def uniformReducedOuterDecayPackageOfBodyPresentations
    (s d : ℕ) (delta : ℝ)
    (volumeConstant rankBound cardinalityThreshold exponent : ℕ)
    (hvolumeConstant : 0 < volumeConstant)
    (hexponent : 0 < exponent)
    (hcube : 2 ^ cardinalityThreshold ≤ volumeConstant)
    (hdecay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      ((twoA A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
      cardinalityThreshold < A.card →
      ∀ x : RankedBodyPresentation A,
        ((volumeConstant * A.card : ℕ) : ℝ) < bodyVolume x →
        ∃ y : RankedBodyPresentation A,
          (2 * bodyVolume y) ^ exponent ≤
            ((volumeConstant * A.card : ℕ) : ℝ) *
              bodyVolume x ^ (exponent - 1))
    (hrealize : ∀ {A : Finset ℤ} (x : RankedBodyPresentation A),
      bodyVolume x ≤ ((volumeConstant * A.card : ℕ) : ℝ) →
        Nonempty (ReducedOuterRealization
          s volumeConstant rankBound A)) :
    UniformReducedOuterDecayPackage s d delta where
  volumeConstant := volumeConstant
  rankBound := rankBound
  cardinalityThreshold := cardinalityThreshold
  exponent := exponent
  volumeConstant_pos := hvolumeConstant
  exponent_pos := hexponent
  Candidate := RankedBodyPresentation
  volume := bodyVolume
  volume_pos := bodyVolume_pos
  initial := rankedBodyPresentationOfSmallCard
  boundedCardinality := by
    intro A hA hcard
    rw [bodyVolume_rankedBodyPresentationOfSmallCard A hA]
    norm_cast
    exact (Nat.pow_le_pow_right (by norm_num) hcard).trans <|
      hcube.trans
      (Nat.le_mul_of_pos_right volumeConstant hA.card_pos)
  decay := hdecay
  realize := hrealize

end

end Erdos186.CFP.Bilu.Section4BodyPresentationPackage

#print axioms
  Erdos186.CFP.Bilu.Section4BodyPresentationPackage.uniformReducedOuterDecayPackageOfBodyPresentations

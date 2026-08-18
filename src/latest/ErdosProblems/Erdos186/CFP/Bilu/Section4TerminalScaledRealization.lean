/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4ScaledDecay
import ErdosProblems.Erdos186.CFP.Bilu.Section4TerminalConstants
import ErdosProblems.Erdos186.CFP.Bilu.Section4BodyPresentationPackage
import ErdosProblems.Erdos186.CFP.Bilu.Section92SingletonRealization

/-!
# Realizing a selected uniformly-scaled Section 4 body

This is the complete `realize` field for the final Section 4 package.  For
sets with at least two elements it runs the canonical primitive quotient
repair and the Mahler conversion.  The only remaining cardinality case is
the direct rank-one singleton realization.
-/

namespace Erdos186.CFP.Bilu.Section4TerminalScaledRealization

open Section4ScaledDecay
open Section4TerminalConstants Section4BodyPresentationPackage
open Section4UniformVolumeDecay
open Section92MahlerVolumeConversion
open Section92PresentationDescent
open Section92SingletonRealization
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

/-- Rank-bounded body presentations are the final concrete candidate class
used in Section 4. -/
abbrev RankBoundedBodyPresentation (A : Finset ℤ) (rankBound : ℕ) :=
  {X : RankedBodyPresentation A // X.1 ≤ rankBound}

/-- The fixed terminal scaling of the formal-coordinate cube is exactly
the terminal scale times `2^|A|`. -/
theorem uniformTerminalBodyVolume_rankedBodyPresentationOfSmallCard
    (s rankBound : ℕ) (A : Finset ℤ) (hA : A.Nonempty) :
    uniformTerminalBodyVolume s rankBound
        (rankedBodyPresentationOfSmallCard A hA) =
      uniformTerminalScale s rankBound * ((2 ^ A.card : ℕ) : ℝ) := by
  rw [uniformTerminalBodyVolume, uniformTerminalScale,
    bodyVolume_rankedBodyPresentationOfSmallCard A hA]
  norm_num [Nat.cast_pow]

/-- The formal-coordinate cube supplies the bounded-cardinality field for
the canonical terminal constant. -/
theorem uniformTerminalBodyVolume_smallCard_le_terminalVolumeConstant_mul
    (s rankBound cardinalityThreshold rawConstant : ℕ)
    (hthreshold : 1 ≤ cardinalityThreshold)
    (A : Finset ℤ) (hA : A.Nonempty)
    (hcard : A.card ≤ cardinalityThreshold) :
    uniformTerminalBodyVolume s rankBound
        (rankedBodyPresentationOfSmallCard A hA) ≤
      ((terminalVolumeConstant s rankBound cardinalityThreshold rawConstant *
        A.card : ℕ) : ℝ) := by
  rw [uniformTerminalBodyVolume_rankedBodyPresentationOfSmallCard]
  exact uniformTerminalScale_mul_two_pow_le_terminalVolumeConstant_mul
    s rankBound cardinalityThreshold rawConstant A.card hthreshold
      hA.card_pos hcard

/-- The exact adapter from a raw Proposition 7.5 body-volume decay to the
uniformly scaled decay field of the final package.  Rounding the fixed
coefficient is handled by `terminalVolumeConstant`. -/
theorem uniformTerminalBodyVolume_decay_of_bodyVolume_decay
    {A : Finset ℤ}
    (s rankBound cardinalityThreshold rawConstant exponent : ℕ)
    (hthreshold : 1 ≤ cardinalityThreshold) (hA : A.Nonempty)
    (hexponent : 0 < exponent)
    (x y : RankedBodyPresentation A)
    (hraw : (2 * bodyVolume y) ^ exponent ≤
      (((rawConstant * A.card : ℕ) : ℝ)) *
        bodyVolume x ^ (exponent - 1)) :
    (2 * uniformTerminalBodyVolume s rankBound y) ^ exponent ≤
      ((terminalVolumeConstant s rankBound cardinalityThreshold rawConstant *
        A.card : ℕ) : ℝ) *
        uniformTerminalBodyVolume s rankBound x ^ (exponent - 1) := by
  have hscaled := scaled_decay_of_decay x y
    (uniformTerminalScale_pos s rankBound) hexponent hraw
  have hcoefficient :=
    uniformTerminalScale_mul_rawConstant_mul_le_terminalVolumeConstant_mul
      s rankBound cardinalityThreshold rawConstant A.card hthreshold
        hA.card_pos
  have hpow : 0 ≤
      uniformTerminalBodyVolume s rankBound x ^ (exponent - 1) :=
    pow_nonneg (uniformTerminalBodyVolume_pos s rankBound x).le _
  have hright := mul_le_mul_of_nonneg_right hcoefficient hpow
  simpa only [uniformTerminalBodyVolume, uniformTerminalScale] using
    hscaled.trans hright

/-- A rank-bounded candidate selected at uniformly scaled volume at most
`volumeConstant * |A|` gives the complete reduced outer realization. -/
theorem exists_reducedOuterRealization_of_uniformTerminalBodyVolume
    {A : Finset ℤ} (s volumeConstant rankBound : ℕ)
    (hA : A.Nonempty) (hrankBound : 1 ≤ rankBound)
    (hsingleton :
      2 * uniformMahlerOuterVolumeConstant rankBound ≤ volumeConstant)
    (X : RankedBodyPresentation A) (hrank : X.1 ≤ rankBound)
    (hvolume : uniformTerminalBodyVolume s rankBound X ≤
      ((volumeConstant * A.card : ℕ) : ℝ)) :
    Nonempty (ReducedOuterRealization
      s volumeConstant rankBound A) := by
  by_cases hcard : 1 < A.card
  · apply exists_reducedOuterRealization_of_terminalScaledBodyVolume
      s volumeConstant rankBound hcard X hrank
    exact (terminalScaledBodyVolume_le_uniformTerminalBodyVolume
      s rankBound X hrank).trans hvolume
  · have hcardOne : A.card = 1 := by
      have hpos := hA.card_pos
      omega
    exact exists_reducedOuterRealization_of_card_eq_one
      s volumeConstant rankBound hcardOne hrankBound hsingleton

/-- Generic concrete Section 4 package after the source construction has
supplied its rank-bounded initial candidate and corrected Proposition 7.5
decay.  Every terminal geometric field, including the singleton branch, is
discharged internally. -/
def uniformReducedOuterDecayPackageOfRankBoundedBodies
    (s d : ℕ) (delta : ℝ)
    (volumeConstant rankBound cardinalityThreshold exponent : ℕ)
    (hvolumeConstant : 0 < volumeConstant)
    (hrankBound : 1 ≤ rankBound)
    (hexponent : 0 < exponent)
    (hsingleton :
      2 * uniformMahlerOuterVolumeConstant rankBound ≤ volumeConstant)
    (initial : ∀ (A : Finset ℤ), A.Nonempty →
      RankBoundedBodyPresentation A rankBound)
    (hbounded : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      A.card ≤ cardinalityThreshold →
        uniformTerminalBodyVolume s rankBound (initial A hA).1 ≤
          ((volumeConstant * A.card : ℕ) : ℝ))
    (hdecay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      ((CFP.BiluFreiman.twoA A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
      cardinalityThreshold < A.card →
      ∀ x : RankBoundedBodyPresentation A rankBound,
        ((volumeConstant * A.card : ℕ) : ℝ) <
            uniformTerminalBodyVolume s rankBound x.1 →
        ∃ y : RankBoundedBodyPresentation A rankBound,
          (2 * uniformTerminalBodyVolume s rankBound y.1) ^ exponent ≤
            ((volumeConstant * A.card : ℕ) : ℝ) *
              uniformTerminalBodyVolume s rankBound x.1 ^
                (exponent - 1)) :
    UniformReducedOuterDecayPackage s d delta where
  volumeConstant := volumeConstant
  rankBound := rankBound
  cardinalityThreshold := cardinalityThreshold
  exponent := exponent
  volumeConstant_pos := hvolumeConstant
  exponent_pos := hexponent
  Candidate := fun A ↦ RankBoundedBodyPresentation A rankBound
  volume := fun x ↦ uniformTerminalBodyVolume s rankBound x.1
  volume_pos := fun x ↦ uniformTerminalBodyVolume_pos s rankBound x.1
  initial := initial
  boundedCardinality := hbounded
  decay := hdecay
  realize := by
    intro A x hx
    exact exists_reducedOuterRealization_of_uniformTerminalBodyVolume
      s volumeConstant rankBound
      (by
        by_contra hA
        have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
        subst A
        have hx0 : uniformTerminalBodyVolume s rankBound x.1 ≤ 0 := by
          simpa using hx
        exact (not_lt_of_ge hx0)
          (uniformTerminalBodyVolume_pos s rankBound x.1))
      hrankBound hsingleton x.1 x.2 hx

/-- Final source-facing package constructor.  The terminal natural constant
is chosen internally.  The source side supplies only a total rank-bounded
initial choice which is the formal cube below the cutoff, and the raw
ordinary-body decay furnished by the corrected Proposition 7.5
construction. -/
def uniformReducedOuterDecayPackageOfRawBodyDecay
    (s d : ℕ) (delta : ℝ)
    (rankBound cardinalityThreshold rawConstant exponent : ℕ)
    (hrankBound : 1 ≤ rankBound)
    (hthreshold : 1 ≤ cardinalityThreshold)
    (hexponent : 0 < exponent)
    (initial : ∀ (A : Finset ℤ), A.Nonempty →
      RankBoundedBodyPresentation A rankBound)
    (hsmall : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      A.card ≤ cardinalityThreshold →
        (initial A hA).1 = rankedBodyPresentationOfSmallCard A hA)
    (hrawDecay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      ((CFP.BiluFreiman.twoA A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
      cardinalityThreshold < A.card →
      ∀ x : RankBoundedBodyPresentation A rankBound,
        ((terminalVolumeConstant s rankBound cardinalityThreshold
            rawConstant * A.card : ℕ) : ℝ) <
              uniformTerminalBodyVolume s rankBound x.1 →
        ∃ y : RankBoundedBodyPresentation A rankBound,
          (2 * bodyVolume y.1) ^ exponent ≤
            (((rawConstant * A.card : ℕ) : ℝ)) *
              bodyVolume x.1 ^ (exponent - 1)) :
    UniformReducedOuterDecayPackage s d delta := by
  let volumeConstant := terminalVolumeConstant s rankBound
    cardinalityThreshold rawConstant
  refine uniformReducedOuterDecayPackageOfRankBoundedBodies
    s d delta volumeConstant rankBound cardinalityThreshold exponent
      (terminalVolumeConstant_pos s rankBound cardinalityThreshold
        rawConstant hthreshold)
      hrankBound hexponent
      (two_mul_uniformMahlerOuterVolumeConstant_le_terminalVolumeConstant
        s rankBound cardinalityThreshold rawConstant hthreshold)
      initial ?_ ?_
  · intro A hA hcard
    rw [hsmall A hA hcard]
    exact uniformTerminalBodyVolume_smallCard_le_terminalVolumeConstant_mul
      s rankBound cardinalityThreshold rawConstant hthreshold A hA hcard
  · intro A hA hdouble hlarge x hx
    obtain ⟨y, hy⟩ := hrawDecay A hA hdouble hlarge x hx
    exact ⟨y,
      uniformTerminalBodyVolume_decay_of_bodyVolume_decay
        s rankBound cardinalityThreshold rawConstant exponent
          hthreshold hA hexponent x.1 y.1 hy⟩

end

end Erdos186.CFP.Bilu.Section4TerminalScaledRealization

#print axioms
  Erdos186.CFP.Bilu.Section4TerminalScaledRealization.exists_reducedOuterRealization_of_uniformTerminalBodyVolume
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalScaledRealization.uniformTerminalBodyVolume_decay_of_bodyVolume_decay
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalScaledRealization.uniformReducedOuterDecayPackageOfRankBoundedBodies
#print axioms
  Erdos186.CFP.Bilu.Section4TerminalScaledRealization.uniformReducedOuterDecayPackageOfRawBodyDecay

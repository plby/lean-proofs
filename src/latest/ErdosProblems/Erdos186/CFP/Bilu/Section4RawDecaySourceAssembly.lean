/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4TerminalScaledRealization
import ErdosProblems.Erdos186.CFP.Bilu.Section94TerminalAssembly

/-!
# Source-facing terminal assembly from raw body-volume decay

This file fixes the exact boundary for the remaining Section 7--9
geometric construction.  All Section 4 iteration, bounded-cardinality,
terminal scaling, primitive-quotient repair, and Mahler conversion are
downstream of this record.
-/

namespace Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly

open CFP.BiluFreiman
open Section4TerminalConstants
open Section4TerminalScaledRealization
open Section4UniformVolumeDecay
open Section92PresentationDescent
open Section94TerminalAssembly

noncomputable section

set_option autoImplicit false

/-- The precise output required from the source-correct large-cardinality
Sections 7--9 construction.  The small-cardinality initial presentation is
fixed to the formal coordinate cube; the sole analytic field is the raw
ordinary-body Proposition 7.5 decay. -/
structure RawBodyDecaySourcePackage (s d : ℕ) (delta : ℝ) where
  rankBound : ℕ
  cardinalityThreshold : ℕ
  rawConstant : ℕ
  exponent : ℕ
  rankBound_pos : 1 ≤ rankBound
  cardinalityThreshold_pos : 1 ≤ cardinalityThreshold
  exponent_pos : 0 < exponent
  initial : ∀ (A : Finset ℤ), A.Nonempty →
    RankBoundedBodyPresentation A rankBound
  initial_eq_small : ∀ (A : Finset ℤ) (hA : A.Nonempty),
    A.card ≤ cardinalityThreshold →
      (initial A hA).1 = rankedBodyPresentationOfSmallCard A hA
  rawDecay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
    ((twoA A).card : ℝ) ≤
        Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
    cardinalityThreshold < A.card →
    ∀ x : RankBoundedBodyPresentation A rankBound,
      ((terminalVolumeConstant s rankBound cardinalityThreshold
          rawConstant * A.card : ℕ) : ℝ) <
            Section4ScaledDecay.uniformTerminalBodyVolume
              s rankBound x.1 →
      ∃ y : RankBoundedBodyPresentation A rankBound,
        (2 * bodyVolume y.1) ^ exponent ≤
          (((rawConstant * A.card : ℕ) : ℝ)) *
            bodyVolume x.1 ^ (exponent - 1)

/-- Total initial choice obtained from the canonical small-cardinality cube
and an initializer needed only above the cutoff. -/
def initialOfSmallOrLarge
    (rankBound cardinalityThreshold : ℕ)
    (hthresholdRank : cardinalityThreshold ≤ rankBound)
    (largeInitial : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      cardinalityThreshold < A.card →
        RankBoundedBodyPresentation A rankBound)
    (A : Finset ℤ) (hA : A.Nonempty) :
    RankBoundedBodyPresentation A rankBound := by
  by_cases hcard : A.card ≤ cardinalityThreshold
  · exact ⟨rankedBodyPresentationOfSmallCard A hA,
      (rank_rankedBodyPresentationOfSmallCard A hA).le.trans
        (hcard.trans hthresholdRank)⟩
  · exact largeInitial A hA (Nat.lt_of_not_ge hcard)

@[simp] theorem initialOfSmallOrLarge_eq_small
    (rankBound cardinalityThreshold : ℕ)
    (hthresholdRank : cardinalityThreshold ≤ rankBound)
    (largeInitial : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      cardinalityThreshold < A.card →
        RankBoundedBodyPresentation A rankBound)
    (A : Finset ℤ) (hA : A.Nonempty)
    (hcard : A.card ≤ cardinalityThreshold) :
    (initialOfSmallOrLarge rankBound cardinalityThreshold hthresholdRank
      largeInitial A hA).1 = rankedBodyPresentationOfSmallCard A hA := by
  simp only [initialOfSmallOrLarge, dif_pos hcard]

/-- Build the exact terminal source package from data used only in the
large-cardinality branch. -/
def rawBodyDecaySourcePackageOfLarge
    (s d : ℕ) (delta : ℝ)
    (rankBound cardinalityThreshold rawConstant exponent : ℕ)
    (hrankBound : 1 ≤ rankBound)
    (hthreshold : 1 ≤ cardinalityThreshold)
    (hthresholdRank : cardinalityThreshold ≤ rankBound)
    (hexponent : 0 < exponent)
    (largeInitial : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      cardinalityThreshold < A.card →
        RankBoundedBodyPresentation A rankBound)
    (hrawDecay : ∀ (A : Finset ℤ) (hA : A.Nonempty),
      ((twoA A).card : ℝ) ≤
          Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card →
      cardinalityThreshold < A.card →
      ∀ x : RankBoundedBodyPresentation A rankBound,
        ((terminalVolumeConstant s rankBound cardinalityThreshold
            rawConstant * A.card : ℕ) : ℝ) <
              Section4ScaledDecay.uniformTerminalBodyVolume
                s rankBound x.1 →
        ∃ y : RankBoundedBodyPresentation A rankBound,
          (2 * bodyVolume y.1) ^ exponent ≤
            (((rawConstant * A.card : ℕ) : ℝ)) *
              bodyVolume x.1 ^ (exponent - 1)) :
    RawBodyDecaySourcePackage s d delta where
  rankBound := rankBound
  cardinalityThreshold := cardinalityThreshold
  rawConstant := rawConstant
  exponent := exponent
  rankBound_pos := hrankBound
  cardinalityThreshold_pos := hthreshold
  exponent_pos := hexponent
  initial := initialOfSmallOrLarge rankBound cardinalityThreshold
    hthresholdRank largeInitial
  initial_eq_small := initialOfSmallOrLarge_eq_small rankBound
    cardinalityThreshold hthresholdRank largeInitial
  rawDecay := hrawDecay

namespace RawBodyDecaySourcePackage

/-- Discharge every downstream field of the uniform Section 4 package. -/
def toUniformReducedOuterDecayPackage
    {s d : ℕ} {delta : ℝ}
    (P : RawBodyDecaySourcePackage s d delta) :
    UniformReducedOuterDecayPackage s d delta :=
  uniformReducedOuterDecayPackageOfRawBodyDecay
    s d delta P.rankBound P.cardinalityThreshold P.rawConstant P.exponent
      P.rankBound_pos P.cardinalityThreshold_pos P.exponent_pos
      P.initial P.initial_eq_small P.rawDecay

end RawBodyDecaySourcePackage

/-- A uniform family of the exact raw Section 7--9 packages proves the
public reduced-outer realization statement. -/
theorem reducedOuterRealizationStatement_of_rawBodyDecay
    (hsource : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (RawBodyDecaySourcePackage s d delta)) :
    Section94RpowContainerAssembly.ReducedOuterRealizationStatement := by
  apply reducedOuterRealizationStatement_of_uniformVolumeDecay
  intro s d hs hd delta hdelta
  obtain ⟨P⟩ := hsource s d hs hd delta hdelta
  exact ⟨P.toUniformReducedOuterDecayPackage⟩

/-- The exact end-to-end public Bilu--Freiman statement from the remaining
raw large-cardinality source construction. -/
theorem biluFreimanStatement_of_rawBodyDecay
    (hsource : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (RawBodyDecaySourcePackage s d delta)) :
    BiluFreimanStatement := by
  apply biluFreimanStatement_of_uniformVolumeDecay
  intro s d hs hd delta hdelta
  obtain ⟨P⟩ := hsource s d hs hd delta hdelta
  exact ⟨P.toUniformReducedOuterDecayPackage⟩

end

end Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly

#print axioms
  Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly.rawBodyDecaySourcePackageOfLarge
#print axioms
  Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly.RawBodyDecaySourcePackage.toUniformReducedOuterDecayPackage
#print axioms
  Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly.reducedOuterRealizationStatement_of_rawBodyDecay
#print axioms
  Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly.biluFreimanStatement_of_rawBodyDecay

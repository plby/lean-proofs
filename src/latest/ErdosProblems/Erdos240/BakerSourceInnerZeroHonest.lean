/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceInnerZeroIndependent
import ErdosProblems.Erdos240.BakerSourceInitialFixedOuterBudget

/-!
# Source Lemma-4 callback with the honest initial contour growth

The first inner stage has boundary growth

`exp ((2 h k + 24 h k^(1 - sigma + epsilon)) Omega log OmegaOld)`.

The generic positive-stage contour estimate has the same shape, but the
special `t = 0` nodal-product inequality is different.  This module packages
the source-faithful split: the exceptional stage uses
`initialStage_threeHalves_mul_outerFactor_lt_exp_neg_five_of_honestGrowth`,
while all positive stages use the ordinary positive-stage estimate.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceInnerZeroHonest

open Erdos240
open Erdos240.BakerInduction
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerLemma4InnerInduction
open Erdos240.BakerSourceAlgebraicMomentBounds
open Erdos240.BakerSourceInnerPointwiseIndependent
open Erdos240.BakerSourceInnerStepAssemblyIndependent
open Erdos240.BakerSourceLiouvilleLowerBounds
open Erdos240.BakerSourceLogFormNormalization
open Erdos240.BakerSourceOversizedConstantNumerics
open Erdos240.BakerSourceInnerZeroIndependent
open Erdos240.BakerSourceState

/-- Assemble the complete inner Lemma-4 callback using the honest boundary
growth at the exceptional first stage. -/
theorem innerStepCallback_of_honestAlgebraicGrowthBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hcontour : 4 * P.lemmaFourContourAbsorptionConstant ≤ C₀)
    (hreq : P.sourceTenThreshold ∈ P.kRequirements)
    (outer : ℕ → VDPLMultiIndex P.rank → ℝ)
    (houter : ∀ t m, 0 ≤ outer t m)
    (hrow : ∀ (t : ℕ), t < terminalStage P →
      ∀ (i : Fin (P.lemmaFourRadius N t))
        (m' : VDPLMultiIndex (oldRank + 1)),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        levelAlgebraicSourceRowError P state b bLast
            ((i.1 + 1 : ℕ) : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hboundary : ∀ (t : ℕ), t < terminalStage P →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
      ∀ z : ℂ, ‖z‖ = 3 * (P.lemmaFourRadius N (t + 1) : ℝ) →
        ‖f state b bLast z m‖ ≤ outer t m)
    (hzeroGrowth : ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N 1 →
        outer 0 m ≤ Real.exp
          ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
              P.k ^ (1 - P.sigma + P.epsilon)) *
            (P.Omega * Real.log P.OmegaOld)))
    (hpositiveGrowth : ∀ (t : ℕ), 1 ≤ t → t < terminalStage P →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
        outer t m ≤ Real.exp
          ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
            P.k ^ (1 - P.sigma +
              P.epsilon * ((t + 1 : ℕ) : ℝ))) *
            (P.Omega * Real.log P.OmegaOld)))
    (htargetError : ∀ (t : ℕ), t < terminalStage P →
      ∀ (l : ℕ), P.lemmaFourRadius N t < l →
        l ≤ P.lemmaFourRadius N (t + 1) →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
        levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
            (toSourceMultiIndex P m) ≤
          stateIntegralLiouvilleThreshold P N (toSourceMultiIndex P m)) :
    InnerStepCallback P (g state b bLast) N := by
  apply innerStepCallback_of_pointwise P (g state b bLast) N
  intro t ht hcurrent l hl1 hl m hm
  by_cases hnew : P.lemmaFourRadius N t < l
  · apply g_eq_zero_at_new_innerTarget_of_algebraicBounds
      state b hbLast hN ht hcurrent C₀ hsmall hjet (hrow t ht)
      hnew hl m hm (houter t m) (hboundary t ht m hm)
    · exact Real.exp_le_exp.mpr
        (by
          convert P.localError_add_contourExponent_le_neg_five_sourceHeight
            hcontour using 1 <;> ring)
    · by_cases ht0 : t = 0
      · subst t
        exact
          (P.initialStage_threeHalves_mul_outerFactor_lt_exp_neg_five_of_honestGrowth
            hN hreq (houter 0 m) (hzeroGrowth m hm)).le
      · have htpos : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
        exact (P.positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_five
          hN htpos ht hreq (houter t m)
            (hpositiveGrowth t htpos ht m hm)).le
    · exact htargetError t ht l hnew hl m hm
  · have hlold : l ≤ P.lemmaFourRadius N t := Nat.le_of_not_gt hnew
    have hmold : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N t :=
      hm.trans (lemmaFourBudget_succ_le P N t)
    simpa only [Nat.cast_one, div_one] using hcurrent l hl1 hlold m hmold

end Erdos240.BakerSourceInnerZeroHonest

#print axioms
  Erdos240.BakerSourceInnerZeroHonest.innerStepCallback_of_honestAlgebraicGrowthBounds

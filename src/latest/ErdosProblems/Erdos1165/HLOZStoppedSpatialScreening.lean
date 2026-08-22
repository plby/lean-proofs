/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.PreStoppingConditionalLaw
import ErdosProblems.Erdos1165.ScreeningInstantiation

/-!
# Stopped product-law adapters for the three HLOZ transitions

`PreStoppingConditionalLaw` identifies the stopped insertion fibre with an
explicit finite product of prefix-corrected truncated negative-binomial laws.
This file packages the data which vary from one stopped-past atom and one cap
to the next, and applies its cap-removal theorem to the three concrete
threshold-creation partitions from `HLOZSpatialAdapter`.

The remaining finite hypothesis is a bound on `upperProductScreenMass`, an
explicit finite sum of product point masses.  It is not a path-level measure
inequality.  The final section gives adapters which derive such bounds from
the checked adjacent-shell and small-window screening theorems.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.HLOZStoppedSpatialScreening

open HLOZPathEvents HLOZSpatialAdapter
open LazyDecomposition PathInsertion SpatialInsertionFiber
open PrefixConditionalLaw PreStoppingConditionalLaw

noncomputable section

/-! ## A varying stopped product fibre -/

/-- All non-analytic data identifying a cap-indexed finite stopped product
screen inside one family of stopped-past atoms.  The Boolean predicate is on
the literal vector of away-domino totals.  In particular, `disintegrate` is
an equality supplied by the stopped conditional law, not the transition
inequality which the upper argument needs. -/
structure UpperProductScreenData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) where
  orientation : index → ℕ → Orientation
  retainedCount : index → ℕ → ℕ
  start : index → ℕ → Point
  retained : ∀ z cap,
    Fin (retainedCount z cap) → RetainedBlock (orientation z cap)
  distinguished : index → ℕ → Finset Point
  upper : ∀ z cap,
    ExternalDomino (start z cap) (retained z cap) → ℕ
  accepts : ∀ z cap,
    UpperTruncatedDominoTotals (start z cap) (retained z cap)
      (distinguished z cap) (upper z cap) → Bool
  screened : index → ℕ → Set WalkPath
  fiber : index → ℕ → Set WalkPath
  measurable_screened : ∀ z cap, MeasurableSet (screened z cap)
  monotone_screened : ∀ z, Monotone (screened z)
  /-- The capped screens exhaust the transition locally on this stopped atom. -/
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap, screened z cap
  disintegrate : ∀ z cap,
    (simpleRandomWalk.restrict (piece z)).real (screened z cap) =
      upperProductScreenMass (start z cap) (retained z cap)
          (distinguished z cap) (upper z cap)
          (fun ell ↦ accepts z cap ell = true) *
        (simpleRandomWalk.restrict (piece z)).real (fiber z cap)

/-- The only quantitative datum in an `UpperProductScreenData`: a bound on
the explicit finite product probability, uniformly over atoms and caps. -/
def FiniteProductScreenBound {index : Type*}
    {piece : index → Set WalkPath} {next : Set WalkPath}
    (data : UpperProductScreenData piece next) (cost : ℝ≥0∞) : Prop :=
  ∀ z cap,
    upperProductScreenMass (data.start z cap) (data.retained z cap)
        (data.distinguished z cap) (data.upper z cap)
        (fun ell ↦ data.accepts z cap ell = true) ≤ cost.toReal

/-- Cap removal turns a uniform finite product bound into the path-space
restricted-real certificate. -/
theorem atomwiseRestrictedRealScreen_of_upperProductScreenData
    {index : Type*} (piece : index → Set WalkPath) (next : Set WalkPath)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (data : UpperProductScreenData piece next)
    (hbound : FiniteProductScreenBound data cost) :
    AtomwiseRestrictedRealScreen piece next cost := by
  exact atomwiseRestrictedRealScreen_of_upperProductDisintegration
    piece next cost hcost data.orientation data.retainedCount data.start
    data.retained data.distinguished data.upper
    (fun z cap ell ↦ data.accepts z cap ell = true)
    data.screened data.fiber data.measurable_screened data.monotone_screened
    data.transition_covered hbound data.disintegrate

/-! ## The three concrete stopped-creation partitions -/

abbrev FirstProductScreenData (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  UpperProductScreenData (firstCreationAtom m) (firstTransitionEvent t m a)

abbrev SecondProductScreenData (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  UpperProductScreenData (pairCreationAtom t m a) (secondTransitionEvent t m a)

abbrev ThirdProductScreenData (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :=
  UpperProductScreenData (tripleCreationAtom t m a)
    (screenedThirdTransitionEvent t m a)

/-- Finite stopped-product data and explicit product bounds for the first
transition, uniformly over all tilings, levels, and mesh branches. -/
structure FirstProductScreening (K : ℝ≥0) where
  data : ∀ t m a, FirstProductScreenData t m a
  product_bound : ∀ t m a,
    FiniteProductScreenBound (data t m a)
      (UpperCanonical.hlozTransitionCost K m)

/-- Finite stopped-product data for the second transition. -/
structure SecondProductScreening (K : ℝ≥0) where
  data : ∀ t m a, SecondProductScreenData t m a
  product_bound : ∀ t m a,
    FiniteProductScreenBound (data t m a)
      (UpperCanonical.hlozTransitionCost K m)

/-- Finite stopped-product data for the screened third transition. -/
structure ThirdProductScreening (K : ℝ≥0) where
  data : ∀ t m a, ThirdProductScreenData t m a
  product_bound : ∀ t m a,
    FiniteProductScreenBound (data t m a)
      (UpperCanonical.hlozTransitionCost K m)

lemma hlozTransitionCost_ne_top (K : ℝ≥0) (m : ℕ) :
    UpperCanonical.hlozTransitionCost K m ≠ ∞ := by
  rw [UpperCanonical.hlozTransitionCost, UpperAssembly.pSeriesWeight]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

/-- The literal stopped product law closes the first atomwise restricted-real
certificate once its explicit finite product screen has been bounded. -/
theorem firstStoppedPastSpatialDisintegration_of_productScreening
    (K : ℝ≥0) (h : FirstProductScreening K) :
    FirstStoppedPastSpatialDisintegration K := by
  intro t m a
  exact atomwiseRestrictedRealScreen_of_upperProductScreenData
    (firstCreationAtom m) (firstTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m) (hlozTransitionCost_ne_top K m)
    (h.data t m a) (h.product_bound t m a)

/-- Second-transition analogue. -/
theorem secondStoppedPastSpatialDisintegration_of_productScreening
    (K : ℝ≥0) (h : SecondProductScreening K) :
    SecondStoppedPastSpatialDisintegration K := by
  intro t m a
  exact atomwiseRestrictedRealScreen_of_upperProductScreenData
    (pairCreationAtom t m a) (secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m) (hlozTransitionCost_ne_top K m)
    (h.data t m a) (h.product_bound t m a)

/-- Screened-third-transition analogue. -/
theorem thirdStoppedPastSpatialDisintegration_of_productScreening
    (K : ℝ≥0) (h : ThirdProductScreening K) :
    ThirdStoppedPastSpatialDisintegration K := by
  intro t m a
  exact atomwiseRestrictedRealScreen_of_upperProductScreenData
    (tripleCreationAtom t m a) (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m) (hlozTransitionCost_ne_top K m)
    (h.data t m a) (h.product_bound t m a)

/-- Simultaneous form used by the upper endgame. -/
theorem stoppedPastSpatialDisintegrations_of_productScreening
    (K : ℝ≥0) (hfirst : FirstProductScreening K)
    (hsecond : SecondProductScreening K) (hthird : ThirdProductScreening K) :
    FirstStoppedPastSpatialDisintegration K ∧
      SecondStoppedPastSpatialDisintegration K ∧
      ThirdStoppedPastSpatialDisintegration K :=
  ⟨firstStoppedPastSpatialDisintegration_of_productScreening K hfirst,
    secondStoppedPastSpatialDisintegration_of_productScreening K hsecond,
    thirdStoppedPastSpatialDisintegration_of_productScreening K hthird⟩

/-! ## Producing the finite product bound from the checked screens -/

/-- Reinterpret an explicit product screen as a shell-overflow event and use
the uniform propagation theorem from `NearFavoriteShells`.  The equality
`hidentify` is purely a finite identification of the Boolean predicate on
domino totals with the abstract occupancy event. -/
theorem upperProductScreenMass_le_of_uniformShellPropagation
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (D : Finset Point) (upper : ExternalDomino x r → ℕ)
    (productEvent : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred productEvent]
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hidentify : upperProductScreenMass x r D upper productEvent =
      mu.real (NearFavoriteShells.totalOverflow occupancy threshold shellCount))
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    {baseCost interfaceCost : ℝ}
    (hbase : mu.real
      (NearFavoriteShells.shellOverflow occupancy threshold 0) ≤ baseCost)
    (hinterface : ∀ j < shellCount - 1,
      mu.real
        (NearFavoriteShells.interfaceBad balanced occupancy G j) ≤
          interfaceCost) :
    upperProductScreenMass x r D upper productEvent ≤
      baseCost + ((shellCount - 1 : ℕ) : ℝ) * interfaceCost := by
  rw [hidentify]
  exact NearFavoriteShells.measureReal_totalOverflow_le_uniform mu balanced
    occupancy threshold G shellCount hstep hbase hinterface

/-- Fully canonical shell-screen adapter.  This fixes the external candidate
set, deficit shells, geometric thresholds, adjacent integer windows, and all
local-CLT arithmetic by invoking `ScreeningInstantiation`'s concrete theorem.
The remaining quantitative assumptions are precisely the external one-point
estimate and the two stopped spatial balance/growth estimates. -/
theorem upperProductScreenMass_le_of_externalShellScreen
    {fiberOrientation : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock fiberOrientation) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (productEvent : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred productEvent]
    (shellOrientation : Orientation)
    (n externalThreshold J G shellCount : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m shellWidth : ℕ)
    (balanced : ℕ → Set WalkPath) (pairTotal successes : ℕ → ℕ)
    (q : ℝ≥0∞) (hJ : 0 < J) (hq : q ≠ ∞)
    (hsuccess : ∀ j < shellCount - 1, 120 ≤ successes j)
    (hidentify : upperProductScreenMass x r D upper productEvent =
      simpleRandomWalk.real
        (NearFavoriteShells.totalOverflow
          (ScreeningInstantiation.externalShellOccupancy shellOrientation n
            externalThreshold distinguished totalLocalTime m shellWidth)
          (ScreeningInstantiation.geometricShellThreshold J G) shellCount))
    (hweightedOneSite : ∀ y,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites
              shellOrientation s n)
            (ExternalThickCount.orientedLargeEvent shellOrientation n
              externalThreshold) y) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites
              shellOrientation s n) y))
    {balanceCost : ℕ → ℝ}
    (hspatialBalance : ∀ j < shellCount - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hspatialGrowth : ∀ (j : ℕ) (hj : j < shellCount - 1),
      simpleRandomWalk.real
          (NearFavoriteShells.balancedGrowthFailure balanced
            (ScreeningInstantiation.externalShellOccupancy shellOrientation n
              externalThreshold distinguished totalLocalTime m shellWidth)
            G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (SmallWindow.windowMass (successes j)
              (ScreeningInstantiation.upperFailureWindow (successes j)
                (ScreeningInstantiation.canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass (successes j)
              (ScreeningInstantiation.lowerFailureWindow (successes j)
                (ScreeningInstantiation.canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass_nonneg _ _)
            (SmallWindow.windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (SmallWindow.windowMass_nonneg _ _)
              (SmallWindow.windowMass_pos
                (ScreeningInstantiation.canonicalWindowWidth_numeric
                  (hsuccess j hj)).1
                (ScreeningInstantiation.lowerFailureWindow_nonempty
                  (ScreeningInstantiation.canonicalWindowWidth_numeric
                    (hsuccess j hj)).2.1)))).real
          {a | a ≤ pairTotal j ∧ G * (pairTotal j - a) < a}) :
    upperProductScreenMass x r D upper productEvent ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal +
        ∑ j ∈ Finset.range (shellCount - 1),
          (balanceCost j +
            (1 + ScreeningInstantiation.adjacentLocalRatio (successes j)
                  (ScreeningInstantiation.adjacentWindowRadius
                    (ScreeningInstantiation.canonicalWindowWidth (successes j)))
                  (ScreeningInstantiation.adjacentWindowSeparation
                    (ScreeningInstantiation.canonicalWindowWidth (successes j))) /
                (1 + ScreeningInstantiation.adjacentLocalRatio (successes j)
                  (ScreeningInstantiation.adjacentWindowRadius
                    (ScreeningInstantiation.canonicalWindowWidth (successes j)))
                  (ScreeningInstantiation.adjacentWindowSeparation
                    (ScreeningInstantiation.canonicalWindowWidth
                      (successes j))))) ^ pairTotal j /
              (2 : ℝ) ^ NearFavoriteShells.growthCut G (pairTotal j)) := by
  rw [hidentify]
  exact ScreeningInstantiation.simpleRandomWalk_externalShell_totalOverflow_le
    shellOrientation n externalThreshold J G shellCount distinguished
    totalLocalTime m shellWidth balanced pairTotal successes q hJ hq hsuccess
    hweightedOneSite hspatialBalance hspatialGrowth

/-- The more precise adjacent-window version.  All negative-binomial local
mass comparisons are discharged by `ScreeningInstantiation`; the remaining
inputs are the literal finite balance and urn-domination statements for the
product fibre. -/
theorem upperProductScreenMass_le_of_localCLTShellPropagation
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (distinguished : Finset Point) (upper : ExternalDomino x r → ℕ)
    (productEvent : UpperTruncatedDominoTotals x r distinguished upper → Prop)
    [DecidablePred productEvent]
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (pairTotal successes : ℕ → ℕ)
    (upperWindow lowerWindow : ℕ → Finset ℕ) (radius separation : ℕ → ℝ)
    (hidentify : upperProductScreenMass x r distinguished upper productEvent =
      mu.real (NearFavoriteShells.totalOverflow occupancy threshold shellCount))
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hsuccess : ∀ j < shellCount - 1, 0 < successes j)
    (hradius : ∀ j < shellCount - 1, 0 ≤ radius j)
    (hseparation : ∀ j < shellCount - 1, 0 ≤ separation j)
    (hmoderate : ∀ j < shellCount - 1,
      radius j ≤ (successes j : ℝ) / 30)
    (hlower : ∀ j < shellCount - 1, (lowerWindow j).Nonempty)
    (hcard : ∀ j < shellCount - 1,
      (upperWindow j).card ≤ (lowerWindow j).card)
    (hupperDev : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      |NegativeBinomialLocalCLT.deviation (successes j) a| ≤ radius j)
    (hlowerDev : ∀ j < shellCount - 1, ∀ a ∈ lowerWindow j,
      |NegativeBinomialLocalCLT.deviation (successes j) a| ≤ radius j)
    (hpair : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      ∀ b ∈ lowerWindow j,
        |NegativeBinomialLocalCLT.deviation (successes j) a -
          NegativeBinomialLocalCLT.deviation (successes j) b| ≤ separation j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    (hbase : mu.real
      (NearFavoriteShells.shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1,
      mu.real (balanced j)ᶜ ≤ balanceCost j)
    (hdom : ∀ (j : ℕ) (hj : j < shellCount - 1),
      mu.real
          (NearFavoriteShells.balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (SmallWindow.windowMass (successes j) (upperWindow j))
            (SmallWindow.windowMass (successes j) (lowerWindow j))
            (SmallWindow.windowMass_nonneg _ _)
            (SmallWindow.windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (SmallWindow.windowMass_nonneg _ _)
              (SmallWindow.windowMass_pos (hsuccess j hj)
                (hlower j hj)))).real
          {a | a ≤ pairTotal j ∧ G * (pairTotal j - a) < a}) :
    upperProductScreenMass x r distinguished upper productEvent ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          (1 + ScreeningInstantiation.adjacentLocalRatio
                (successes j) (radius j) (separation j) /
              (1 + ScreeningInstantiation.adjacentLocalRatio
                (successes j) (radius j) (separation j))) ^ pairTotal j /
            (2 : ℝ) ^ NearFavoriteShells.growthCut G (pairTotal j)) := by
  rw [hidentify]
  exact ScreeningInstantiation.measureReal_totalOverflow_le_of_localCLT mu
    balanced occupancy threshold G shellCount pairTotal successes
    upperWindow lowerWindow radius separation hstep hsuccess hradius hseparation
    hmoderate hlower hcard hupperDev hlowerDev hpair hbase hbalance hdom

/-- Reinterpret an explicit product predicate as the union of heterogeneous
small-window candidate events and apply `SmallWindow`'s checked local-CLT
union bound. -/
theorem upperProductScreenMass_le_of_heterogeneousSmallWindow
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (D : Finset Point) (upper : ExternalDomino x r → ℕ)
    (productEvent : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred productEvent]
    {Omega Candidate : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (candidates : Finset Candidate)
    (near : Candidate → Set Omega) (successes : Candidate → ℕ)
    (small large : Candidate → Finset ℕ) (reference : Candidate → ℝ)
    {J : ℕ} {C g f : ℝ}
    (hidentify : upperProductScreenMass x r D upper productEvent =
      mu.real {omega | ∃ candidate ∈ candidates, omega ∈ near candidate})
    (hcandidates : candidates.card ≤ J)
    (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsuccesses : ∀ candidate ∈ candidates, 0 < successes candidate)
    (href : ∀ candidate ∈ candidates, 0 < reference candidate)
    (hdisjoint : ∀ candidate ∈ candidates,
      Disjoint (small candidate) (large candidate))
    (hsmallCard : ∀ candidate ∈ candidates,
      ((small candidate).card : ℝ) ≤ g)
    (hlargeCard : ∀ candidate ∈ candidates,
      f ≤ ((large candidate).card : ℝ))
    (hsmall : ∀ candidate ∈ candidates, ∀ j ∈ small candidate,
      NegativeBinomial.hlozMass (successes candidate) j ≤
        C * reference candidate)
    (hlarge : ∀ candidate ∈ candidates, ∀ j ∈ large candidate,
      reference candidate ≤
        NegativeBinomial.hlozMass (successes candidate) j)
    (hnear : ∀ candidate ∈ candidates,
      mu.real (near candidate) ≤
        SmallWindow.windowMass (successes candidate) (small candidate) /
          SmallWindow.windowMass (successes candidate)
            (small candidate ∪ large candidate)) :
    upperProductScreenMass x r D upper productEvent ≤ C * g * J / f := by
  rw [hidentify]
  exact SmallWindow.heterogeneous_smallWindow_union_le mu candidates near
    successes small large reference hcandidates hC hg hf hsuccesses href
    hdisjoint hsmallCard hlargeCard hsmall hlarge hnear

end

end Erdos1165.HLOZStoppedSpatialScreening

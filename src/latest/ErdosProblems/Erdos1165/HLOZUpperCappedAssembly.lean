/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZGapRandomClockClosure
import ErdosProblems.Erdos1165.HLOZHighGapRouting
import ErdosProblems.Erdos1165.HLOZValidSupportCappedTraceScreening

/-!
# All-six capped-product upper assembly

This is the final upper-facing composition point for the sound variable
trace formalization.  The transition input is an eventual package of
valid-support literal capped-product certificates for every one of the six
domino tilings; the finite initial level segment is absorbed separately.
The low-scale exceptional input is the lazy/random-clock screen, restricted
to `alpha ≤ kappaTwo`.  Proper high-scale branches remain in the screened
terminal transition mesh, as recorded by `HLOZHighGapRouting`.

The premises below expose product disintegration, pathwise random-clock
extraction, and the two genuine overflow estimates.  None is a restatement
of the final favorite-count conclusion or of the three transition measure
inequalities.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.HLOZUpperCappedAssembly

open HLOZGapBetaArithmetic HLOZGapEstimate HLOZGapRandomClockScreen HLOZLazyOverflow
open HLOZPathEvents HLOZProposition48Candidates
open HLOZValidSupportCappedTraceScreening

noncomputable section

/-- Every proper high-scale terminal branch used below is still charged to
the full screened transition mesh.  This named specialization makes the
high-scale half of the low/high split visible at the final assembly point. -/
theorem highGap_terminalBranch_routed
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hproper₁ : a.1.1 ∈ properGapMesh)
    (hproper₂ : a.1.2 ∈ properGapMesh)
    (hproper₃ : a.2 ∈ properGapMesh)
    (hhigh : HasHighGapScale a) :
    thirdTransitionEvent t m a ⊆
      hlozExceptionalEvent t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (screenedThirdTransitionEvent t m) :=
  HLOZHighGapRouting.highGap_thirdTransitionEvent_subset_exceptional_union_screenedMesh
    t m a hproper₁ hproper₂ hproper₃ hhigh

/-- The all-six capped-product transition screens and the checked low-scale
lazy/random-clock estimate imply the canonical eventual upper bound.

The only upper-specific inputs left are the eventual valid-support literal
capped-product package, the pathwise low-gap band extraction, the lazy
stopped laws, and the two
overflow estimates.  Proposition 1.3 is kept as its established analytic
interface and is used only for late-clock and spatial-overflow summability. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_cappedPackage_lazyRandomClock
    (start : ℕ) (K : ℝ≥0)
    (package : PositiveLevelValidSupportCappedTraceScreenPackage start K)
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {c : ℝ} (hc : 0 < c)
    (cap : ℕ → ℕ) (laws : StoppedLazyLawFamily cap)
    (bands : DominoTiling → ℕ → Finset RandomClockBand)
    (index : ℕ → RandomClockBand → ℕ)
    (templates : DominoTiling → Finset (GapScale × ℕ))
    (B : DominoTiling → ℕ)
    (hextract : ∀ t m,
      LazyGoodRandomClockExtraction
        (onTimeLowGapDeficitExceptionalEvent t m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands t m))
    (overflowCost : DominoTiling → ℕ → ℝ≥0∞)
    (hoverflow : ∀ t, ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands t m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost t m)
    (hother : ∀ t, ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m + overflowCost t m ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)))
    (hscale : ∀ t p, p ∈ templates t → p.1 ∈ lowGapMesh)
    (hprojects : ∀ t m band, band ∈ bands t m →
      (band.scale, index m band) ∈ templates t)
    (hcard : ∀ t m, (bands t m).card ≤ B t)
    (hbeta : ∀ t m band, band ∈ bands t m →
      band.beta ≤ deficitExponent48 (meshExponent band.scale)
        (index m band + 1))
    (hreturns : ∀ t m band, band ∈ bands t m →
      requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) (index m band)) ≤
        band.returns) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hgap :=
    HLOZGapRandomClockClosure.hasGapDeficitReturnHarnack_of_lazy_randomClock_bounds
      hc cap laws bands index templates B hextract overflowCost hoverflow hother
      hscale hprojects hcard hbeta hreturns
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveValidSupportPackage
      start K package
  intro t
  exact HLOZUpperEstimates.simpleRandomWalk_hlozExceptional_series_ne_top
    hProp13 hc hgap t

end

end Erdos1165.HLOZUpperCappedAssembly

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCanonicalDominantCandidateWindows

/-!
# Favorite-supported canonical dominant windows

The pre-Theta all-creation fibre has an ambient coordinate upper bound.  Its
conditional denominator must therefore retain the literal strict
away-domino truncation which is automatic on an accepted creation atom but
is not implied by `D_eta` alone: the first `V₃` alternative only bounds the
canonical base endpoint.  This file adds that missing coordinatewise window
to the existing canonical dominant broad/narrow acceptors.

At the selected `I₁` coordinate the additional cutoff is redundant, since
the source window lies strictly below `m`.  Thus the checked one-coordinate
negative-binomial comparison is unchanged.  Everything below is an exact
finite-product statement; there is no path-probability or transition-bound
premise.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZCanonicalDominantCandidateWindows

open FiniteDominoProductLaw HLOZCanonicalDominantCandidateWindows
open HLOZShellZeroReplacementWindows HLOZTilingConditionalCoordinateReconstruction
open HLOZTilingConditionalCandidateWindows
open LazyDecomposition SmallWindow TilingCappedMarginalization
open TilingConditionalCappedMarginalization TilingInsertedLocalTime
open TilingLazyDecomposition TilingSpatialInsertionFiber

noncomputable section

namespace CanonicalDominantCandidateWindowSpec

/-- The strict away support which is part of a genuine level-`m` creation
atom, but not of the bare `D_eta` classification. -/
def strictAwaySupport (spec : CanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  ∀ b : spec.Away,
    tilingFixedBoundaryDominoMax spec.x spec.r spec.terminal b.1 +
        (ell b : ℕ) < spec.m

/-- Honest all-creation denominator: the broad source classification and
the strict favorite-support cutoff. -/
def acceptedBaseProp (spec : CanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  reconstructedCanonicalCandidateBaseAccepts spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S ell ∧
    spec.strictAwaySupport ell

/-- Honest numerator, adding the selected narrow endpoint window to the same
all-creation denominator. -/
def acceptedScreenedProp (spec : CanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper) : Prop :=
  reconstructedCanonicalCandidateScreenedAccepts spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S spec.chosen
          spec.narrowWindow ell ∧
    spec.strictAwaySupport ell

noncomputable def acceptedBaseAccepts
    (spec : CanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedBaseProp ell)

noncomputable def acceptedScreenedAccepts
    (spec : CanonicalDominantCandidateWindowSpec) :
    TruncatedTotals spec.upper → Bool := by
  classical
  exact fun ell ↦ decide (spec.acceptedScreenedProp ell)

/-- Coordinatewise form of the honest denominator. -/
noncomputable def acceptedBaseWindow
    (spec : CanonicalDominantCandidateWindowSpec) (b : spec.Away) :
    Finset ℕ := by
  classical
  exact (spec.baseWindow b).filter fun v ↦
    tilingFixedBoundaryDominoMax spec.x spec.r spec.terminal b.1 + v < spec.m

/-- Coordinatewise form of the honest numerator. -/
noncomputable def acceptedScreenedWindow
    (spec : CanonicalDominantCandidateWindowSpec) (b : spec.Away) :
    Finset ℕ := by
  classical
  exact (spec.screenedWindow b).filter fun v ↦
    tilingFixedBoundaryDominoMax spec.x spec.r spec.terminal b.1 + v < spec.m

theorem acceptedBaseProp_iff_windows
    (spec : CanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆
      (Finset.univ.image fun b : spec.Away ↦
        tilingFixedDominantEndpoint spec.x spec.r spec.terminal b.1)) :
    spec.acceptedBaseProp ell ↔
      ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b := by
  rw [acceptedBaseProp,
    reconstructedCanonicalCandidateBaseAccepts_iff_windows spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S ell hcoverage]
  simp only [strictAwaySupport, acceptedBaseWindow, Finset.mem_filter]
  constructor
  · rintro ⟨hbase, hstrict⟩ b
    exact ⟨hbase b, hstrict b⟩
  · intro hall
    exact ⟨fun b ↦ (hall b).1, fun b ↦ (hall b).2⟩

theorem acceptedScreenedProp_iff_windows
    (spec : CanonicalDominantCandidateWindowSpec)
    (ell : TruncatedTotals spec.upper)
    (hcoverage : spec.S ⊆
      (Finset.univ.image fun b : spec.Away ↦
        tilingFixedDominantEndpoint spec.x spec.r spec.terminal b.1)) :
    spec.acceptedScreenedProp ell ↔
      ∀ b, (ell b : ℕ) ∈ spec.acceptedScreenedWindow b := by
  rw [acceptedScreenedProp,
    reconstructedCanonicalCandidateScreenedAccepts_iff_windows spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S spec.chosen
        spec.narrowWindow ell hcoverage]
  simp only [strictAwaySupport, acceptedScreenedWindow, Finset.mem_filter]
  constructor
  · rintro ⟨hscreened, hstrict⟩ b
    exact ⟨hscreened b, hstrict b⟩
  · intro hall
    exact ⟨fun b ↦ (hall b).1, fun b ↦ (hall b).2⟩

theorem acceptedScreenedProp_subset_base
    (spec : CanonicalDominantCandidateWindowSpec)
    {ell : TruncatedTotals spec.upper}
    (h : spec.acceptedScreenedProp ell) : spec.acceptedBaseProp ell :=
  ⟨h.1.1, h.2⟩

theorem acceptedScreenedWindow_eq_base
    (spec : CanonicalDominantCandidateWindowSpec)
    (b : spec.Away) (hne : b ≠ spec.chosen) :
    spec.acceptedScreenedWindow b = spec.acceptedBaseWindow b := by
  unfold acceptedScreenedWindow acceptedBaseWindow
  unfold screenedWindow baseWindow
  rw [reconstructedCanonicalCandidateScreenedWindow_eq_base spec.t spec.x
    spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S spec.chosen b
        spec.narrowWindow hne]

theorem acceptedBaseWindow_chosen
    (spec : CanonicalDominantCandidateWindowSpec)
    (hbDominant : tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
        (tilingPartner spec.t spec.chosen.1.1) ≤
      tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
        spec.chosen.1.1)
    (hS : spec.chosen.1.1 ∈ spec.S)
    (hexternal : spec.externalLow ≤
        tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1 ∧
      tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1 < spec.externalHigh)
    (hbroad : spec.broadWindow = shellZeroSourceTotalWindow spec.m spec.w) :
    spec.acceptedBaseWindow spec.chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1)
        (spec.upper spec.chosen)
        (shellZeroSourceTotalWindow spec.m spec.w) := by
  rw [acceptedBaseWindow,
    baseWindow,
    reconstructedCanonicalCandidateBaseWindow_chosen spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S spec.chosen hbDominant hS
          hexternal hbroad]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [tilingFixedBoundaryDominoMax, max_eq_left hbDominant]
    exact (mem_shellZeroSourceTotalWindow.mp
      (Finset.mem_filter.mp hv).2).2

theorem acceptedScreenedWindow_chosen
    (spec : CanonicalDominantCandidateWindowSpec)
    (hbDominant : tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
        (tilingPartner spec.t spec.chosen.1.1) ≤
      tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
        spec.chosen.1.1)
    (hS : spec.chosen.1.1 ∈ spec.S)
    (hexternal : spec.externalLow ≤
        tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1 ∧
      tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1 < spec.externalHigh)
    (hbroad : spec.broadWindow = shellZeroSourceTotalWindow spec.m spec.w)
    (hnarrow : spec.narrowWindow ⊆
      shellZeroSourceTotalWindow spec.m spec.w) :
    spec.acceptedScreenedWindow spec.chosen =
      shiftedEndpointWindow
        (tilingFixedBoundaryLocalTime spec.x spec.r spec.terminal
          spec.chosen.1.1)
        (spec.upper spec.chosen) spec.narrowWindow := by
  rw [acceptedScreenedWindow,
    screenedWindow,
    reconstructedCanonicalCandidateScreenedWindow_chosen spec.t spec.x spec.r
      spec.terminal spec.D spec.upper spec.m spec.w spec.low spec.externalLow
        spec.externalHigh spec.broadWindow spec.S spec.chosen spec.narrowWindow
          hbDominant hS hexternal hbroad hnarrow]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [tilingFixedBoundaryDominoMax, max_eq_left hbDominant]
    exact (mem_shellZeroSourceTotalWindow.mp
      (hnarrow (Finset.mem_filter.mp hv).2)).2

/-- The checked data for the strengthened broad denominator. -/
structure AcceptedRatioData (cap : ℕ) (C : ℝ)
    (spec : CanonicalDominantCandidateWindowSpec) : Prop where
  coverage : spec.S ⊆ (Finset.univ.image fun b : spec.Away ↦
    tilingFixedDominantEndpoint spec.x spec.r spec.terminal b.1)
  basePos : 0 < screenMass (spec.pointMass cap) spec.upper
    (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b)
  screenedUpper : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen,
    v < spec.upper spec.chosen
  baseUpper : ∀ v ∈ spec.acceptedBaseWindow spec.chosen,
    v < spec.upper spec.chosen
  screenedCap : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen, v ≤ cap
  baseCap : ∀ v ∈ spec.acceptedBaseWindow spec.chosen, v ≤ cap
  coordinates : 0 < Fintype.card
    (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1)
  ratio : windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.acceptedScreenedWindow spec.chosen) ≤
    C * windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.acceptedBaseWindow spec.chosen)

theorem acceptedConditionalScreenMass_le {cap : ℕ} {C : ℝ}
    (spec : CanonicalDominantCandidateWindowSpec)
    (data : AcceptedRatioData cap C spec) :
    conditionalScreenMass (spec.pointMass cap) spec.upper
      (fun ell ↦ spec.acceptedBaseAccepts ell = true)
      (fun ell ↦ spec.acceptedScreenedAccepts ell = true) ≤ C := by
  classical
  have hbasePred : (fun ell ↦ spec.acceptedBaseAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b) := by
    funext ell
    apply propext
    simpa only [acceptedBaseAccepts, decide_eq_true_eq] using
      spec.acceptedBaseProp_iff_windows ell data.coverage
  have hscreenedPred :
      (fun ell ↦ spec.acceptedScreenedAccepts ell = true) =
        (fun ell ↦ ∀ b,
          (ell b : ℕ) ∈ spec.acceptedScreenedWindow b) := by
    funext ell
    apply propext
    simpa only [acceptedScreenedAccepts, decide_eq_true_eq] using
      spec.acceptedScreenedProp_iff_windows ell data.coverage
  simp only [hbasePred, hscreenedPred]
  simpa only [pointMass, Away] using
    tilingConditionalScreenMass_le_of_one_coordinate_window_ratio
      (cap := cap) (C := C) spec.t spec.x spec.r spec.D spec.upper
        spec.chosen spec.acceptedBaseWindow spec.acceptedScreenedWindow
          data.basePos
          (fun b hb ↦ spec.acceptedScreenedWindow_eq_base b hb)
          data.screenedUpper data.baseUpper data.screenedCap data.baseCap
          data.coordinates data.ratio

end CanonicalDominantCandidateWindowSpec

end

end Erdos1165.HLOZCanonicalDominantCandidateWindows

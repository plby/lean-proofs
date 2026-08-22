/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingConditionalCappedMarginalization
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance

/-!
# Reconstructing source classifications from stopped insertion totals

After a retained all-six tiling word is fixed, both endpoints of one
represented domino receive the same insertion total.  Consequently:

* each endpoint local time is its fixed retained-prefix value plus that
  total;
* the endpoint attaining `xi⁺` is fixed by the retained prefix and does not
  change when the total is varied;
* the corrected single-site `V₂`, `V₃`, and `Theta` predicates are literal
  predicates on the reconstructed total vector.

This is the deterministic bridge needed to define a nontrivial
`baseAccepts` for the conditional stopped-coordinate law.  It uses the
source-correct `M_e / M_o` dominant-endpoint normalization from
`HLOZThetaSourceBalance` and makes no probability assertion.
-/

open Set

namespace Erdos1165.HLOZTilingConditionalCoordinateReconstruction

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows
open HLOZThetaSourceBalance
open LazyDecomposition PreStoppingSpatialLaw SpatialInsertionFiber
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingShellZeroSourcePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The dominant endpoint determined solely by the retained-prefix local
times.  Adding a common insertion total to both endpoints cannot change this
choice. -/
def tilingFixedDominantEndpoint {i : ℕ} {t : DominoTiling} (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (b : TilingExternalDomino t x r) : Point :=
  if tilingFixedBoundaryLocalTime x r terminal (tilingPartner t b.1) ≤
      tilingFixedBoundaryLocalTime x r terminal b.1 then b.1
  else tilingPartner t b.1

/-- Reconstructed endpoint local time from an away-total vector. -/
def reconstructedTilingEndpointLocalTime {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (ell : TruncatedTotals upper)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (y : Point) : ℕ :=
  tilingFixedBoundaryLocalTime x r terminal y + (ell b : ℕ)

/-- Reconstructed `xi⁺`: the maximum fixed endpoint local time plus the
common insertion total. -/
def reconstructedTilingXiPlus {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (ell : TruncatedTotals upper)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : ℕ :=
  tilingFixedBoundaryDominoMax x r terminal b.1 + (ell b : ℕ)

/-- Corrected single-site `V₂(I)` reconstructed on one away domino. -/
def reconstructedTilingVTwoAt {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (window : Finset ℕ) (ell : TruncatedTotals upper)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Prop :=
  tilingFixedBoundaryLocalTime x r terminal (tilingPartner t b.1.1) ≤
      tilingFixedBoundaryLocalTime x r terminal b.1.1 ∧
    reconstructedTilingEndpointLocalTime
      t x r terminal D upper ell b b.1.1 ∈ window

/-- Corrected `V₃` classification reconstructed on one away domino. -/
def reconstructedTilingVThreeAt {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m low : ℕ) (ell : TruncatedTotals upper)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Prop :=
  reconstructedTilingEndpointLocalTime
      t x r terminal D upper ell b b.1.1 ≤ low ∨
    (reconstructedTilingEndpointLocalTime
        t x r terminal D upper ell b b.1.1 <
      reconstructedTilingEndpointLocalTime t x r terminal D upper ell b
        (tilingPartner t b.1.1) ∧
      reconstructedTilingEndpointLocalTime t x r terminal D upper ell b
        (tilingPartner t b.1.1) < m)

/-- The local `Theta` failure predicate reconstructed on one away domino.
The external local time is fixed by the retained word; only the corrected
single-site base local time varies with the total. -/
def reconstructedTilingThetaBadAt {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w externalLow externalHigh : ℕ) (ell : TruncatedTotals upper)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Prop :=
  reconstructedTilingEndpointLocalTime
      t x r terminal D upper ell b b.1.1 ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
    ¬(externalLow ≤ tilingFixedBoundaryLocalTime x r terminal b.1.1 ∧
      tilingFixedBoundaryLocalTime x r terminal b.1.1 < externalHigh)

/-- The away-domino part of the source `D_eta` classification.  Favorite
domino cardinality and terminal data live in the distinguished selection;
every away base must be in the corrected source `V₂(I₁)` or `V₃` class. -/
def reconstructedAwayDEtaClassifies {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low : ℕ) (ell : TruncatedTotals upper) : Prop :=
  ∀ b,
    reconstructedTilingVTwoAt t x r terminal D upper
        (shellZeroSourceTotalWindow m w) ell b ∨
      reconstructedTilingVThreeAt
        t x r terminal D upper m low ell b

/-- The away-domino part of `Theta_eta = ∅`. -/
def reconstructedAwayThetaGood {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w externalLow externalHigh : ℕ) (ell : TruncatedTotals upper) : Prop :=
  ∀ b, ¬reconstructedTilingThetaBadAt t x r terminal D upper
    m w externalLow externalHigh ell b

/-- Dominant broad-window sites in one parity class, reconstructed solely
from the retained word and total vector.  This is the finite-coordinate
counterpart of `tilingOrientedDominantNearBasesAtCreation` (`M_e` or `M_o`). -/
noncomputable def reconstructedOrientedDominantBroadAwaySites {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (broadWindow : Finset ℕ) (ell : TruncatedTotals upper) : Finset Point := by
  classical
  exact ((Finset.univ.filter fun b :
        TilingCappedMarginalization.TilingAwayDomino t x r D ↦
          reconstructedTilingXiPlus t x r terminal D upper ell b ∈ broadWindow).image
      (fun b ↦ tilingFixedDominantEndpoint x r terminal b.1)).filter
        (OrientationCompatible o)

/-- The same finite represented-away family, evaluated on an actual stopped
path.  This deliberately ranges over the represented away dominoes rather
than claiming that an arbitrary global visited-site family is unchanged by
coordinate replacement. -/
noncomputable def actualOrientedDominantBroadAwaySites {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (broadWindow : Finset ℕ) : Finset Point := by
  classical
  exact ((Finset.univ.filter fun b :
        TilingCappedMarginalization.TilingAwayDomino t x r D ↦
          tilingXiPlusAt t s n b.1.1 ∈ broadWindow).image
      (fun b ↦ tilingDominantEndpointAt t s n b.1.1)).filter
        (OrientationCompatible o)

/-- Literal broad-history acceptor: the away `D_eta` and `Theta_eta` parts
hold and the corrected parity-specific candidate Finset is exactly `S`. -/
def reconstructedSourceCandidateBaseAccepts {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper) : Prop :=
  reconstructedAwayDEtaClassifies t x r terminal D upper m w low ell ∧
    reconstructedAwayThetaGood t x r terminal D upper
      m w externalLow externalHigh ell ∧
    reconstructedOrientedDominantBroadAwaySites
      o t x r terminal D upper broadWindow ell = S

/-- The numerator acceptor adds one narrow single-site window to the exact
broad-history acceptor. -/
def reconstructedSourceCandidateScreenedAccepts {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper) : Prop :=
  reconstructedSourceCandidateBaseAccepts o t x r terminal D upper
      m w low externalLow externalHigh broadWindow S ell ∧
    reconstructedTilingEndpointLocalTime
      t x r terminal D upper ell chosen
        (tilingFixedDominantEndpoint x r terminal chosen.1) ∈ narrowWindow

theorem reconstructedSourceCandidateScreenedAccepts_subset_base
    {i : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper) :
    reconstructedSourceCandidateScreenedAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S chosen narrowWindow ell →
      reconstructedSourceCandidateBaseAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S ell :=
  fun h ↦ h.1

/-! The corresponding predicates on an actual stopped path.  They are
introduced only to state the reconstruction equivalences below; they make
no measurability or invariance claim. -/

def actualTilingThetaBadAt {i : ℕ}
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (m w externalLow externalHigh : ℕ)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) : Prop :=
  localTime s n b.1.1 ∈
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) ∧
    ¬(externalLow ≤ tilingExternalBaseLocalTime t s n b.1.1 ∧
      tilingExternalBaseLocalTime t s n b.1.1 < externalHigh)

/-- Actual represented-away broad history whose conditional denominator is
encoded by `reconstructedSourceCandidateBaseAccepts`. -/
def actualSourceCandidateBaseAccepts {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) : Prop :=
  (∀ b : TilingCappedMarginalization.TilingAwayDomino t x r D,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b.1.1 ∨
        tilingVThreeAt t m low s n b.1.1) ∧
    (∀ b : TilingCappedMarginalization.TilingAwayDomino t x r D,
      ¬actualTilingThetaBadAt t s n x r D
        m w externalLow externalHigh b) ∧
    actualOrientedDominantBroadAwaySites
      o t s n x r D broadWindow = S

/-- The actual numerator adds the narrow window at one chosen dominant
endpoint to the exact broad history. -/
def actualSourceCandidateScreenedAccepts {i : ℕ}
    (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) : Prop :=
  actualSourceCandidateBaseAccepts o t s n x r D
      m w low externalLow externalHigh broadWindow S ∧
    localTime s n (tilingDominantEndpointAt t s n chosen.1.1) ∈
      narrowWindow

/-! ## Exact comparison with a reconstructed stopped prefix -/

theorem localTime_eq_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (y : Point) (hy : tilingBase t y = b.1.1) :
    localTime s n y =
      reconstructedTilingEndpointLocalTime t x r terminal D upper
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b y := by
  rw [localTime_eq_listLocalTime, hpath,
    tilingInsertedPrefix_localTime_at_dominoPoint
      t x r (fun k ↦ (q k : ℕ)) terminal b.1 y hy]
  rfl

theorem tilingXiPlusAt_eq_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    tilingXiPlusAt t s n b.1.1 =
      reconstructedTilingXiPlus t x r terminal D upper
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b := by
  unfold tilingXiPlusAt reconstructedTilingXiPlus
    tilingFixedBoundaryDominoMax
  rw [localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
      (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]
  simp only [reconstructedTilingEndpointLocalTime,
    reconstructedTilingAwayTotalsOfCoordinates]
  rw [← max_add]

theorem tilingDominantEndpointAt_eq_fixed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    tilingDominantEndpointAt t s n b.1.1 =
      tilingFixedDominantEndpoint x r terminal b.1 := by
  unfold tilingDominantEndpointAt tilingFixedDominantEndpoint
  rw [localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
      (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]
  simp only [reconstructedTilingEndpointLocalTime,
    reconstructedTilingAwayTotalsOfCoordinates, add_le_add_iff_right]

theorem tilingBase_fixedDominantEndpoint {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r) :
    tilingBase t (tilingFixedDominantEndpoint x r terminal b) = b.1 := by
  unfold tilingFixedDominantEndpoint
  split
  · exact tilingExternalDomino_isBase t x r b
  · exact (tilingBase_partner t b.1).trans
      (tilingExternalDomino_isBase t x r b)

/-- The stopped local time at the dominant endpoint is recovered exactly
from the chosen away total. -/
theorem localTime_dominantEndpoint_eq_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    localTime s n (tilingDominantEndpointAt t s n b.1.1) =
      reconstructedTilingEndpointLocalTime t x r terminal D upper
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b
        (tilingFixedDominantEndpoint x r terminal b.1) := by
  rw [tilingDominantEndpointAt_eq_fixed_of_exact_prefix
    t s x r q terminal D upper hupper hpath b]
  exact localTime_eq_reconstructed_of_exact_prefix
    t s x r q terminal D upper hupper hpath b
      (tilingFixedDominantEndpoint x r terminal b.1)
      (tilingBase_fixedDominantEndpoint t x r terminal b.1)

/-- Exact recovery of the parity-specific broad candidate set on all
represented away dominoes.  No prefix-observability shortcut is used: the
proof rewrites both the broad membership and the dominant endpoint from the
fully reconstructed total vector. -/
theorem actualOrientedDominantBroadAwaySites_eq_reconstructed_of_exact_prefix
    {i cap n : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (broadWindow : Finset ℕ) :
    actualOrientedDominantBroadAwaySites
        o t s n x r D broadWindow =
      reconstructedOrientedDominantBroadAwaySites
        o t x r terminal D upper broadWindow
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  classical
  let actualFiltered := Finset.univ.filter fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        tilingXiPlusAt t s n b.1.1 ∈ broadWindow
  let reconstructedFiltered := Finset.univ.filter fun b :
      TilingCappedMarginalization.TilingAwayDomino t x r D ↦
        reconstructedTilingXiPlus t x r terminal D upper
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) b ∈ broadWindow
  have hfiltered : actualFiltered = reconstructedFiltered := by
    ext b
    simp only [actualFiltered, reconstructedFiltered, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [tilingXiPlusAt_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b]
  have himage :
      actualFiltered.image (fun b ↦
          tilingDominantEndpointAt t s n b.1.1) =
        reconstructedFiltered.image (fun b ↦
          tilingFixedDominantEndpoint x r terminal b.1) := by
    rw [hfiltered]
    apply Finset.image_congr
    intro b _
    exact tilingDominantEndpointAt_eq_fixed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
  unfold actualOrientedDominantBroadAwaySites
    reconstructedOrientedDominantBroadAwaySites
  exact congrArg (fun S : Finset Point ↦
    S.filter (OrientationCompatible o)) himage

theorem tilingExternalBaseLocalTime_eq_fixed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (y : Point) :
    tilingExternalBaseLocalTime t s n y =
      tilingFixedBoundaryLocalTime x r terminal y := by
  unfold tilingExternalBaseLocalTime tilingFixedBoundaryLocalTime
  rw [hpath, tilingExternalPath_insertedPrefix]

theorem tilingVTwoAt_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (window : Finset ℕ)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    tilingVTwoAt t window s n b.1.1 ↔
      reconstructedTilingVTwoAt t x r terminal D upper window
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b := by
  unfold tilingVTwoAt reconstructedTilingVTwoAt
  rw [localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
      (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]
  simp only [reconstructedTilingEndpointLocalTime,
    reconstructedTilingAwayTotalsOfCoordinates, add_le_add_iff_right]

theorem tilingVThreeAt_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m low : ℕ)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    tilingVThreeAt t m low s n b.1.1 ↔
      reconstructedTilingVThreeAt t x r terminal D upper m low
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b := by
  unfold tilingVThreeAt reconstructedTilingVThreeAt
  rw [localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b
      (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]

theorem tilingThetaBadAt_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m w externalLow externalHigh : ℕ)
    (b : TilingCappedMarginalization.TilingAwayDomino t x r D) :
    (localTime s n b.1.1 ∈
          (shellZeroSourceTotalWindow m w ∪
            shellZeroReplacementTotalWindow m w) ∧
        ¬(externalLow ≤ tilingExternalBaseLocalTime t s n b.1.1 ∧
          tilingExternalBaseLocalTime t s n b.1.1 < externalHigh)) ↔
      reconstructedTilingThetaBadAt t x r terminal D upper
        m w externalLow externalHigh
        (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) b := by
  unfold reconstructedTilingThetaBadAt
  rw [localTime_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    tilingExternalBaseLocalTime_eq_fixed_of_exact_prefix
      t s x r q terminal hpath b.1.1]

/-- The broad `I₁`/away-`D_eta`/away-`Theta`/exact-`S` denominator is
recovered exactly from the insertion-total vector. -/
theorem actualSourceCandidateBaseAccepts_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) :
    actualSourceCandidateBaseAccepts o t s n x r D
        m w low externalLow externalHigh broadWindow S ↔
      reconstructedSourceCandidateBaseAccepts o t x r terminal D upper
        m w low externalLow externalHigh broadWindow S
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  unfold actualSourceCandidateBaseAccepts
    reconstructedSourceCandidateBaseAccepts
    reconstructedAwayDEtaClassifies reconstructedAwayThetaGood
    actualTilingThetaBadAt
  constructor
  · rintro ⟨hclassifies, htheta, hsites⟩
    refine ⟨?_, ?_, ?_⟩
    · intro b
      rw [← tilingVTwoAt_iff_reconstructed_of_exact_prefix
          t s x r q terminal D upper hupper hpath
            (shellZeroSourceTotalWindow m w) b,
        ← tilingVThreeAt_iff_reconstructed_of_exact_prefix
          t s x r q terminal D upper hupper hpath m low b]
      exact hclassifies b
    · intro b
      rw [← tilingThetaBadAt_iff_reconstructed_of_exact_prefix
        t s x r q terminal D upper hupper hpath
          m w externalLow externalHigh b]
      exact htheta b
    · rw [← actualOrientedDominantBroadAwaySites_eq_reconstructed_of_exact_prefix
        o t s x r q terminal D upper hupper hpath broadWindow]
      exact hsites
  · rintro ⟨hclassifies, htheta, hsites⟩
    refine ⟨?_, ?_, ?_⟩
    · intro b
      rw [tilingVTwoAt_iff_reconstructed_of_exact_prefix
          t s x r q terminal D upper hupper hpath
            (shellZeroSourceTotalWindow m w) b,
        tilingVThreeAt_iff_reconstructed_of_exact_prefix
          t s x r q terminal D upper hupper hpath m low b]
      exact hclassifies b
    · intro b
      rw [tilingThetaBadAt_iff_reconstructed_of_exact_prefix
        t s x r q terminal D upper hupper hpath
          m w externalLow externalHigh b]
      exact htheta b
    · rw [actualOrientedDominantBroadAwaySites_eq_reconstructed_of_exact_prefix
        o t s x r q terminal D upper hupper hpath broadWindow]
      exact hsites

/-- Adding the chosen dominant endpoint's narrow window is likewise an
exact reconstructed predicate. -/
theorem actualSourceCandidateScreenedAccepts_iff_reconstructed_of_exact_prefix
    {i cap n : ℕ} (o : LazyDecomposition.Orientation)
    (t : DominoTiling) (s : WalkPath) (x : Point)
    (r : TilingRetainedWord t x i) (q : TilingCappedCoordinates i cap)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b,
      tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r
        (fun k ↦ (q k : ℕ))) terminal)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point)
    (chosen : TilingCappedMarginalization.TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) :
    actualSourceCandidateScreenedAccepts o t s n x r D
        m w low externalLow externalHigh broadWindow S chosen narrowWindow ↔
      reconstructedSourceCandidateScreenedAccepts
        o t x r terminal D upper m w low externalLow externalHigh
          broadWindow S chosen narrowWindow
          (reconstructedTilingAwayTotalsOfCoordinates
            t x r D upper q hupper) := by
  unfold actualSourceCandidateScreenedAccepts
    reconstructedSourceCandidateScreenedAccepts
  rw [actualSourceCandidateBaseAccepts_iff_reconstructed_of_exact_prefix
      o t s x r q terminal D upper hupper hpath
        m w low externalLow externalHigh broadWindow S,
    localTime_dominantEndpoint_eq_reconstructed_of_exact_prefix
      t s x r q terminal D upper hupper hpath chosen]

end

end Erdos1165.HLOZTilingConditionalCoordinateReconstruction

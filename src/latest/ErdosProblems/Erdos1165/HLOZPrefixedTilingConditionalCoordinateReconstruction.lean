/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCanonicalDominantCandidateWindows
import ErdosProblems.Erdos1165.TilingPrefixedInsertedLocalTime

/-!
# Source classifications reconstructed on physical prefixed fibres

This is the prefix-correct counterpart of the insertion-only reconstruction.
Every fixed endpoint local time includes the physical initial word.  The
joining endpoint is counted once, so shifted checker/column fibres retain the
time-zero visit at the origin without duplicating their suffix start.
-/

open Set

namespace Erdos1165.HLOZPrefixedTilingConditionalCoordinateReconstruction

open FiniteDominoProductLaw HLOZCanonicalDominantCandidateWindows
open HLOZShellZeroReplacementWindows HLOZThetaSourceBalance
open LazyDecomposition PreStoppingSpatialLaw SpatialInsertionFiber
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingPrefixedInsertedLocalTime TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def prefixedTilingFixedDominantEndpoint (initial : List Direction) {i : ℕ}
    {t : DominoTiling} (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r) : Point :=
  if prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t b.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1 then b.1
  else tilingPartner t b.1

def reconstructedPrefixedTilingEndpointLocalTime (initial : List Direction)
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (ell : TruncatedTotals upper)
    (b : TilingAwayDomino t x r D) (y : Point) : ℕ :=
  prefixedTilingFixedBoundaryLocalTime initial x r terminal y + (ell b : ℕ)

def reconstructedPrefixedTilingXiPlus (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (ell : TruncatedTotals upper)
    (b : TilingAwayDomino t x r D) : ℕ :=
  prefixedTilingFixedBoundaryDominoMax initial x r terminal b.1 + (ell b : ℕ)

def reconstructedPrefixedTilingVTwoAt (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (window : Finset ℕ)
    (ell : TruncatedTotals upper) (b : TilingAwayDomino t x r D) : Prop :=
  prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t b.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 ∧
    reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D
      upper ell b b.1.1 ∈ window

def reconstructedPrefixedTilingVThreeAt (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (m low : ℕ)
    (ell : TruncatedTotals upper) (b : TilingAwayDomino t x r D) : Prop :=
  reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D upper
      ell b b.1.1 ≤ low ∨
    (reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D
        upper ell b b.1.1 <
      reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D
        upper ell b (tilingPartner t b.1.1) ∧
      reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D
        upper ell b (tilingPartner t b.1.1) < m)

def reconstructedPrefixedTilingThetaBadAt (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w externalLow externalHigh : ℕ) (ell : TruncatedTotals upper)
    (b : TilingAwayDomino t x r D) : Prop :=
  reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D upper
      ell b b.1.1 ∈
        (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w) ∧
    ¬(externalLow ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 <
        externalHigh)

def reconstructedPrefixedAwayDEtaClassifies (initial : List Direction)
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (m w low : ℕ)
    (ell : TruncatedTotals upper) : Prop :=
  ∀ b, reconstructedPrefixedTilingVTwoAt initial t x r terminal D upper
      (shellZeroSourceTotalWindow m w) ell b ∨
    reconstructedPrefixedTilingVThreeAt initial t x r terminal D upper
      m low ell b

def reconstructedPrefixedAwayThetaGood (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (m w externalLow externalHigh : ℕ) (ell : TruncatedTotals upper) : Prop :=
  ∀ b, ¬reconstructedPrefixedTilingThetaBadAt initial t x r terminal D
    upper m w externalLow externalHigh ell b

noncomputable def reconstructedPrefixedCanonicalDominantBroadAwaySites
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (broadWindow : Finset ℕ) (ell : TruncatedTotals upper) : Finset Point := by
  classical
  exact ((Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
      reconstructedPrefixedTilingXiPlus initial t x r terminal D upper ell b ∈
        broadWindow).image (fun b ↦
          prefixedTilingFixedDominantEndpoint initial x r terminal b.1)).filter
            (IsTilingBase t)

def reconstructedPrefixedCanonicalCandidateBaseAccepts
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (ell : TruncatedTotals upper) : Prop :=
  reconstructedPrefixedAwayDEtaClassifies initial t x r terminal D upper
      m w low ell ∧
    reconstructedPrefixedAwayThetaGood initial t x r terminal D upper
      m w externalLow externalHigh ell ∧
    reconstructedPrefixedCanonicalDominantBroadAwaySites initial t x r terminal
      D upper broadWindow ell = S

def reconstructedPrefixedCanonicalCandidateScreenedAccepts
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w low externalLow externalHigh : ℕ) (broadWindow : Finset ℕ)
    (S : Finset Point) (chosen : TilingAwayDomino t x r D)
    (narrowWindow : Finset ℕ) (ell : TruncatedTotals upper) : Prop :=
  reconstructedPrefixedCanonicalCandidateBaseAccepts initial t x r terminal D
      upper m w low externalLow externalHigh broadWindow S ell ∧
    reconstructedPrefixedTilingEndpointLocalTime initial t x r terminal D upper
      ell chosen (prefixedTilingFixedDominantEndpoint initial x r terminal
        chosen.1) ∈ narrowWindow

theorem tilingBase_prefixedTilingFixedDominantEndpoint (initial : List Direction)
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r) :
    tilingBase t (prefixedTilingFixedDominantEndpoint initial x r terminal b) =
      b.1 := by
  unfold prefixedTilingFixedDominantEndpoint
  split
  · exact tilingExternalDomino_isBase t x r b
  · exact (tilingBase_partner t b.1).trans
      (tilingExternalDomino_isBase t x r b)

theorem prefixedTilingFixedDominantEndpoint_injective (initial : List Direction)
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point) :
    Function.Injective (fun b : TilingAwayDomino t x r D ↦
      prefixedTilingFixedDominantEndpoint initial x r terminal b.1) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  have hb := tilingBase_prefixedTilingFixedDominantEndpoint
    initial t x r terminal b.1
  have hc := tilingBase_prefixedTilingFixedDominantEndpoint
    initial t x r terminal c.1
  exact hb.symm.trans ((congrArg (tilingBase t) h).trans hc)

theorem prefixedTilingFixedBoundaryLocalTime_fixedDominant
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (b : TilingExternalDomino t x r) :
    prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (prefixedTilingFixedDominantEndpoint initial x r terminal b) =
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b := by
  unfold prefixedTilingFixedDominantEndpoint
    prefixedTilingFixedBoundaryDominoMax
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (Nat.le_of_not_ge h)).symm

theorem localTime_eq_reconstructedPrefixed_of_exact_prefix
    (initial : List Direction) {i cap n : ℕ} (t : DominoTiling)
    (s : WalkPath) (x : Point) (r : TilingRetainedWord t x i)
    (q : TilingCappedCoordinates i cap) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 <
      upper b)
    (hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingAwayDomino t x r D) (y : Point)
    (hy : tilingBase t y = b.1.1) :
    localTime s n y = reconstructedPrefixedTilingEndpointLocalTime initial
      t x r terminal D upper (reconstructedTilingAwayTotalsOfCoordinates
        t x r D upper q hupper) b y := by
  rw [localTime_eq_listLocalTime, hpath,
    prefixedTilingInsertedPrefix_localTime_at_dominoPoint
      initial t x r (fun k ↦ (q k : ℕ)) terminal b.1 y hy]
  rfl

theorem tilingXiPlusAt_eq_reconstructedPrefixed_of_exact_prefix
    (initial : List Direction) {i cap n : ℕ} (t : DominoTiling)
    (s : WalkPath) (x : Point) (r : TilingRetainedWord t x i)
    (q : TilingCappedCoordinates i cap) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 <
      upper b)
    (hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingAwayDomino t x r D) :
    tilingXiPlusAt t s n b.1.1 = reconstructedPrefixedTilingXiPlus initial
      t x r terminal D upper (reconstructedTilingAwayTotalsOfCoordinates
        t x r D upper q hupper) b := by
  unfold tilingXiPlusAt reconstructedPrefixedTilingXiPlus
    prefixedTilingFixedBoundaryDominoMax
  rw [localTime_eq_reconstructedPrefixed_of_exact_prefix initial t s x r q
      terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructedPrefixed_of_exact_prefix initial t s x r q
      terminal D upper hupper hpath b (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]
  simp only [reconstructedPrefixedTilingEndpointLocalTime,
    reconstructedTilingAwayTotalsOfCoordinates]
  rw [← max_add]

theorem tilingDominantEndpointAt_eq_prefixedFixed_of_exact_prefix
    (initial : List Direction) {i cap n : ℕ} (t : DominoTiling)
    (s : WalkPath) (x : Point) (r : TilingRetainedWord t x i)
    (q : TilingCappedCoordinates i cap) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 <
      upper b)
    (hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal)
    (b : TilingAwayDomino t x r D) :
    tilingDominantEndpointAt t s n b.1.1 =
      prefixedTilingFixedDominantEndpoint initial x r terminal b.1 := by
  unfold tilingDominantEndpointAt prefixedTilingFixedDominantEndpoint
  rw [localTime_eq_reconstructedPrefixed_of_exact_prefix initial t s x r q
      terminal D upper hupper hpath b b.1.1
      (tilingExternalDomino_isBase t x r b.1),
    localTime_eq_reconstructedPrefixed_of_exact_prefix initial t s x r q
      terminal D upper hupper hpath b (tilingPartner t b.1.1)
      ((tilingBase_partner t b.1.1).trans
        (tilingExternalDomino_isBase t x r b.1))]
  simp only [reconstructedPrefixedTilingEndpointLocalTime,
    reconstructedTilingAwayTotalsOfCoordinates, add_le_add_iff_right]

theorem actualCanonicalDominantBroadAwaySites_eq_reconstructedPrefixed
    (initial : List Direction) {i cap n : ℕ} (t : DominoTiling)
    (s : WalkPath) (x : Point) (r : TilingRetainedWord t x i)
    (q : TilingCappedCoordinates i cap) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 <
      upper b)
    (hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal)
    (broadWindow : Finset ℕ) :
    actualCanonicalDominantBroadAwaySites t s n x r D broadWindow =
      reconstructedPrefixedCanonicalDominantBroadAwaySites initial t x r
        terminal D upper broadWindow (reconstructedTilingAwayTotalsOfCoordinates
          t x r D upper q hupper) := by
  classical
  unfold actualCanonicalDominantBroadAwaySites
    reconstructedPrefixedCanonicalDominantBroadAwaySites
  congr 2
  · funext b
    exact tilingDominantEndpointAt_eq_prefixedFixed_of_exact_prefix initial t s
      x r q terminal D upper hupper hpath b
  · apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [tilingXiPlusAt_eq_reconstructedPrefixed_of_exact_prefix initial t s x
      r q terminal D upper hupper hpath b]

end

end Erdos1165.HLOZPrefixedTilingConditionalCoordinateReconstruction

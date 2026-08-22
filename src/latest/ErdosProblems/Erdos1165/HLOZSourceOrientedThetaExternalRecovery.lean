/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalProduct
import ErdosProblems.Erdos1165.HLOZPrefixedTilingConditionalCoordinateReconstruction

/-!
# Physical-prefix recovery for the absolute external Theta product

This module is deliberately separate from the frozen quantitative product.
It identifies the pathwise prefixed Theta screen with the unconditional
negative-binomial coordinate window.  The remaining oriented geometric
input is the equality between the compatible endpoint's fixed boundary
count and its retained-coordinate multiplicity.
-/

namespace Erdos1165.HLOZSourceOrientedThetaExternalRecovery

open FiniteDominoProductLaw
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaProduct
open TilingCappedMarginalization TilingSpatialInsertionFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Once the fixed prefixed boundary count is identified with the retained
coordinate multiplicity, the physical Theta predicate is literally the
negative-binomial coordinate window. -/
theorem reconstructedPrefixedTilingThetaBadAt_iff_thetaCoordinateBad
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m w externalLow externalHigh : ℕ)
    (ell : TruncatedTotals upper) (b : TilingAwayDomino t x r D)
    (hboundary : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        b.1.1 = Fintype.card (TilingCoordinatesAt t x r b.1)) :
    reconstructedPrefixedTilingThetaBadAt initial t x r terminal D upper
        m w externalLow externalHigh ell b ↔
      thetaCoordinateBad m w externalLow externalHigh
        (Fintype.card (TilingCoordinatesAt t x r b.1)) (ell b) := by
  simp only [reconstructedPrefixedTilingThetaBadAt,
    reconstructedPrefixedTilingEndpointLocalTime, thetaCoordinateBad,
    thetaFailureWindow, Finset.mem_union,
    HLOZShellZeroReplacementWindows.mem_shellZeroSourceFailureWindow,
    HLOZShellZeroReplacementWindows.mem_shellZeroReplacementFailureWindow,
    HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow,
    HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow,
    hboundary]
  omega

/-- Boolean form of the same identification on an external fibre. -/
theorem externalThetaAccepts_eq_true_iff_reconstructed
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (terminal : Option Point)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap))
    (hboundary : ∀ b : TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S),
      prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
          terminal b.1.1 =
        Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) :
    externalThetaAccepts data w externalLow externalHigh cap ell = true ↔
      ∃ b, reconstructedPrefixedTilingThetaBadAt z.initial.1 t z.start
        z.retained terminal
        (supportComplementDistinguished t z.start z.retained S)
        (data.upper cap) m w externalLow externalHigh ell b := by
  simp only [externalThetaAccepts, decide_eq_true_eq]
  apply exists_congr
  intro b
  exact (reconstructedPrefixedTilingThetaBadAt_iff_thetaCoordinateBad
    z.initial.1 t z.start z.retained terminal
    (supportComplementDistinguished t z.start z.retained S)
    (data.upper cap) m w externalLow externalHigh ell b
    (hboundary b)).symm

end

end Erdos1165.HLOZSourceOrientedThetaExternalRecovery

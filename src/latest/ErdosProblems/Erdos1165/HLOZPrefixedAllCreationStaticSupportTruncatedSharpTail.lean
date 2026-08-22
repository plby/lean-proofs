/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCofinalTruncatedSharpWindow
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement

/-!
# Static-support recovery for truncated cofinal sharp windows

This file connects the prefix-correct recovery certificate on an exact
`(external word, static support)` atom to the corrected cofinal sharp-window
interface.  In particular, it does not require either canonical failure
window to lie wholly inside the same-rank accepted window.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationStaticSupportTruncatedSharpTail

open FiniteDominoProductLaw
open HLOZAllCreationCofinalTruncatedSharpWindow
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

namespace StaticSupportRecoveryCertificate

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}

/-- Public spelling of the screened capped-coordinate predicate used by the
static-support refinement.  The original constructor intentionally keeps
its implementation private; this definition exposes the proposition needed
to state concrete monotonicity and cofinal-cover hypotheses. -/
private noncomputable def truncatedScreenedPredicate
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (threshold : ℕ → ℕ) (shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((ConcreteFiber supportData eta).coordinateCap cap)) : Prop :=
  (ConcreteFiber supportData eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t
      ((ConcreteFiber supportData eta).start cap)
      ((ConcreteFiber supportData eta).retained cap)
      ((ConcreteFiber supportData eta).distinguished cap)
      ((ConcreteFiber supportData eta).upper cap)
      (fun ell ↦ cert.screenedAccepts threshold shell bound cap ell = true)
      ((splitTilingCoordinatesEquiv t
        ((ConcreteFiber supportData eta).start cap)
        ((ConcreteFiber supportData eta).retained cap)
        ((ConcreteFiber supportData eta).distinguished cap) q).2)

/-- Package exact static-support recovery as the corrected conditional
sharp-tail data.  The only analytic input is the local ratio after both
windows have been intersected with the honest accepted base window. -/
noncomputable def truncatedSharpTailData
    (cert : StaticSupportRecoveryCertificate supportData eta)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (baseLocalPos : ∀ cap
      (b : TilingAwayDomino t
        ((ConcreteFiber supportData eta).start cap)
        ((ConcreteFiber supportData eta).retained cap)
        ((ConcreteFiber supportData eta).distinguished cap)),
      0 < ∑ v : Fin ((ConcreteFiber supportData eta).upper cap b),
        if (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass
              (cap := (ConcreteFiber supportData eta).coordinateCap cap) t
              ((ConcreteFiber supportData eta).start cap)
              ((ConcreteFiber supportData eta).retained cap)
              ((ConcreteFiber supportData eta).distinguished cap))
            ((ConcreteFiber supportData eta).upper cap) b v else 0)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        ((ConcreteFiber supportData eta).stoppingTime cap)
        ((ConcreteFiber supportData eta).initial cap) t
        ((ConcreteFiber supportData eta).start cap)
        ((ConcreteFiber supportData eta).retained cap)
        ((ConcreteFiber supportData eta).coordinateCap cap)
        ((ConcreteFiber supportData eta).tail cap)
        (truncatedScreenedPredicate cert threshold shell bound cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        ((ConcreteFiber supportData eta).stoppingTime cap)
        ((ConcreteFiber supportData eta).initial cap) t
        ((ConcreteFiber supportData eta).start cap)
        ((ConcreteFiber supportData eta).retained cap)
        ((ConcreteFiber supportData eta).coordinateCap cap)
        ((ConcreteFiber supportData eta).tail cap)
        (truncatedScreenedPredicate cert threshold shell bound cap)))
    (capStart : ℕ)
    (window_ratio_inter_base : ∀ cap, capStart ≤ cap →
      ∀ (b : TilingAwayDomino t
        ((ConcreteFiber supportData eta).start cap)
        ((ConcreteFiber supportData eta).retained cap)
        ((ConcreteFiber supportData eta).distinguished cap)),
      (∑ v : Fin ((ConcreteFiber supportData eta).upper cap b),
        if (v : ℕ) ∈
              HLOZSharpWindowProductClosure.activeUpperFailureWindow m
                (Fintype.card (TilingCoordinatesAt t
                  ((ConcreteFiber supportData eta).start cap)
                  ((ConcreteFiber supportData eta).retained cap) b.1)) ∧
            (v : ℕ) ∈ cert.baseWindow cap b then
          coordinateMass
            (tilingAwayPointMass
              (cap := (ConcreteFiber supportData eta).coordinateCap cap) t
              ((ConcreteFiber supportData eta).start cap)
              ((ConcreteFiber supportData eta).retained cap)
              ((ConcreteFiber supportData eta).distinguished cap))
            ((ConcreteFiber supportData eta).upper cap) b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin ((ConcreteFiber supportData eta).upper cap b),
            if (v : ℕ) ∈
                  HLOZSharpWindowProductClosure.activeLowerFailureWindow m
                    (Fintype.card (TilingCoordinatesAt t
                      ((ConcreteFiber supportData eta).start cap)
                      ((ConcreteFiber supportData eta).retained cap) b.1)) ∧
                (v : ℕ) ∈ cert.baseWindow cap b then
              coordinateMass
                (tilingAwayPointMass
                  (cap := (ConcreteFiber supportData eta).coordinateCap cap) t
                  ((ConcreteFiber supportData eta).start cap)
                  ((ConcreteFiber supportData eta).retained cap)
                  ((ConcreteFiber supportData eta).distinguished cap))
                ((ConcreteFiber supportData eta).upper cap) b v else 0) :
    OrientedAllCreationConditionalTruncatedSharpTailData
      (ConcreteFiber supportData eta) piece next threshold shell bound where
  refinement := cert.refinement piece next threshold shell bound
    atom_subset_piece baseLocalPos monotone_screened transition_covered
  capStart := capStart
  baseWindow := cert.baseWindow
  baseAccepts_iff := by
    intro cap ell
    change cert.baseAccepts cap ell = true ↔ cert.baseProp cap ell
    simp only [baseAccepts, decide_eq_true_eq]
  screenedAccepts_iff := by
    intro cap ell
    change cert.screenedAccepts threshold shell bound cap ell = true ↔
      cert.screenedProp threshold shell bound cap ell
    simp only [screenedAccepts, decide_eq_true_eq]
  baseLocalPos := fun cap _hcap b ↦ baseLocalPos cap b
  window_ratio_inter_base := window_ratio_inter_base

end StaticSupportRecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationStaticSupportTruncatedSharpTail

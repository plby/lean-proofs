/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllCreationCanonicalRefinement
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationCanonicalDominantWindows

/-!
# Prefix-correct canonical broad/narrow refinement

This is the physical-prefix version of the all-creation canonical
refinement.  In particular, the denominator fixes the complete broad
`D_eta`/Theta/exact-candidate classification reconstructed with the initial
prefix included.  The reverse implication receives that complete screen;
strict truncation alone is deliberately insufficient.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedAllCreationCanonicalRefinement

open FiniteDominoProductLaw HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open LazyDecomposition TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The prefix-correct window parameters on one concrete all-creation
fibre. -/
structure Parameters
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {S : Finset Point} {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) (candidate : Point) where
  terminal : Option Point
  low : ℕ
  externalLow : ℕ
  externalHigh : ℕ
  broadWindow : Finset ℕ
  chosen : TilingAwayDomino t (fiber.start cap) (fiber.retained cap)
    (fiber.distinguished cap)
  candidate_eq :
    prefixedTilingFixedDominantEndpoint (fiber.initial cap) (fiber.start cap)
      (fiber.retained cap) terminal chosen.1 = candidate
  narrowWindow : Finset ℕ

namespace Parameters

noncomputable def toSpec
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {S : Finset Point} {z : OrientedAllCreationTraceCode t}
    {fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z} {cap : ℕ} {candidate : Point}
    (p : Parameters fiber cap candidate) :
    PrefixedCanonicalDominantCandidateWindowSpec where
  initial := fiber.initial cap
  i := fiber.retainedCount cap
  t := t
  x := fiber.start cap
  r := fiber.retained cap
  terminal := p.terminal
  D := fiber.distinguished cap
  upper := fiber.upper cap
  m := m
  w := HLOZProposition48Candidates.shellWidth48 m
  low := p.low
  externalLow := p.externalLow
  externalHigh := p.externalHigh
  broadWindow := p.broadWindow
  S := S
  chosen := p.chosen
  narrowWindow := p.narrowWindow

end Parameters

abbrev ConcreteFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt) :=
  (orientedAllCreationConcreteFamily
    t o m k supportAt supportData).fiber eta

/-- The only atom-specific deterministic obligation.  A realizable
distinguished assignment together with the complete prefix-correct broad
screen must recover the exact accepted stopped atom. -/
structure RecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt)
    (candidate : Point) where
  parameters : ∀ cap, Parameters
    ((orientedAllCreationConcreteFamily
      t o m k supportAt supportData).fiber eta) cap candidate
  recover : ∀ cap
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (((orientedAllCreationConcreteFamily
        t o m k supportAt supportData).fiber eta).coordinateCap cap)),
    let fiber := (orientedAllCreationConcreteFamily
      t o m k supportAt supportData).fiber eta
    let spec := (parameters cap).toSpec
    fiber.selected cap
        ((splitTilingCoordinatesEquiv t (fiber.start cap)
          (fiber.retained cap) (fiber.distinguished cap) q).1) →
      TilingAwayTotalsScreen t (fiber.start cap) (fiber.retained cap)
          (fiber.distinguished cap) (fiber.upper cap)
          (fun ell ↦ spec.acceptedBaseAccepts ell = true)
          ((splitTilingCoordinatesEquiv t (fiber.start cap)
            (fiber.retained cap) (fiber.distinguished cap) q).2) →
        fiber.atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted (fiber.stoppingTime cap)
            (fiber.initial cap) t (fiber.start cap) (fiber.retained cap)
            (fun j ↦ (q j : ℕ)) (fiber.tail cap)

namespace RecoveryCertificate

variable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    {supportData : OrientedAllCreationSupportSelectorData t o m k supportAt}
    {eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt}
    {candidate : Point}

private abbrev fiber (_cert : RecoveryCertificate supportData eta candidate) :=
  ConcreteFiber supportData eta

private noncomputable def basePredicate
    (cert : RecoveryCertificate supportData eta candidate) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private noncomputable def screenedPredicate
    (cert : RecoveryCertificate supportData eta candidate) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) : Prop :=
  cert.fiber.atomPredicate cap q ∧
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦
        (cert.parameters cap).toSpec.acceptedScreenedAccepts ell = true)
      ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
        (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2)

private theorem screenedScreen_base
    (cert : RecoveryCertificate supportData eta candidate) (cap : ℕ)
    (a : TilingAwayCoordinates (cap := cert.fiber.coordinateCap cap)
      t (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.distinguished cap))
    (h : TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦
        (cert.parameters cap).toSpec.acceptedScreenedAccepts ell = true) a) :
    TilingAwayTotalsScreen t (cert.fiber.start cap)
      (cert.fiber.retained cap) (cert.fiber.distinguished cap)
      (cert.fiber.upper cap)
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      a := by
  rcases h with ⟨ell, hell, htotal⟩
  refine ⟨ell, ?_, htotal⟩
  have hprop : (cert.parameters cap).toSpec.acceptedScreenedProp ell := by
    simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedScreenedAccepts,
      decide_eq_true_eq] using hell
  simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
    decide_eq_true_eq] using
      (cert.parameters cap).toSpec.acceptedScreenedProp_subset_base hprop

private theorem base_factorization
    (cert : RecoveryCertificate supportData eta candidate) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) :
    cert.basePredicate cap q ∧
        PrefixedTilingStoppingAccepted (cert.fiber.stoppingTime cap)
          (cert.fiber.initial cap) t (cert.fiber.start cap)
          (cert.fiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.fiber.tail cap) ↔
      cert.fiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.fiber.start cap)
          (cert.fiber.retained cap) (cert.fiber.distinguished cap)
          (cert.fiber.upper cap)
          (fun ell ↦
            (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  exact allCreationScreenedPredicate_factorization_of_reconstructed
      supportData eta cap
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      (cert.recover cap) q

private theorem screened_factorization
    (cert : RecoveryCertificate supportData eta candidate) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      (cert.fiber.coordinateCap cap)) :
    cert.screenedPredicate cap q ∧
        PrefixedTilingStoppingAccepted (cert.fiber.stoppingTime cap)
          (cert.fiber.initial cap) t (cert.fiber.start cap)
          (cert.fiber.retained cap) (fun j ↦ (q j : ℕ))
          (cert.fiber.tail cap) ↔
      cert.fiber.selected cap
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (cert.fiber.start cap)
          (cert.fiber.retained cap) (cert.fiber.distinguished cap)
          (cert.fiber.upper cap)
          (fun ell ↦
            (cert.parameters cap).toSpec.acceptedScreenedAccepts ell = true)
          ((splitTilingCoordinatesEquiv t (cert.fiber.start cap)
            (cert.fiber.retained cap) (cert.fiber.distinguished cap) q).2) := by
  apply allCreationScreenedPredicate_factorization_of_reconstructed
      supportData eta cap
      (fun ell ↦
        (cert.parameters cap).toSpec.acceptedScreenedAccepts ell = true)
      (q := q)
  intro q'
  dsimp only
  intro hselected hscreened
  exact cert.recover cap q' hselected
    (cert.screenedScreen_base cap _ hscreened)

/-- Assemble the existing low-coordinate interface using the physical-prefix
broad/narrow windows.  Only exact-atom recovery, event coverage, and the
literal one-coordinate window ratio remain consumer data. -/
noncomputable def refinement
    (cert : RecoveryCertificate supportData eta candidate)
    (piece next : Set WalkPath) (ratio : ℝ≥0∞)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2 ⊆ piece)
    (ratioData : ∀ cap,
      PrefixedCanonicalDominantCandidateWindowSpec.AcceptedRatioData
        (cert.fiber.coordinateCap cap) ratio.toReal
        (cert.parameters cap).toSpec)
    (monotone_screened : Monotone fun cap ↦
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate cap)))
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      walkLift (prefixedTilingPreStoppingFiberEvent
        (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
        (cert.fiber.start cap) (cert.fiber.retained cap)
        (cert.fiber.coordinateCap cap) (cert.fiber.tail cap)
        (cert.screenedPredicate cap))) :
    OrientedAllCreationConditionalRefinementData
      cert.fiber piece next ratio where
  basePredicate := cert.basePredicate
  screenedPredicate := cert.screenedPredicate
  base_subset_atom := fun _cap _q hq ↦ hq.1
  screened_subset_basePredicate := by
    intro cap q hq
    exact ⟨hq.1, cert.screenedScreen_base cap _ hq.2⟩
  baseAccepts := fun cap ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts
  screenedAccepts := fun cap ↦
    (cert.parameters cap).toSpec.acceptedScreenedAccepts
  screened_subset_base := by
    intro cap ell hell
    have hprop : (cert.parameters cap).toSpec.acceptedScreenedProp ell := by
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedScreenedAccepts,
        decide_eq_true_eq] using hell
    simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
      decide_eq_true_eq] using
      (cert.parameters cap).toSpec.acceptedScreenedProp_subset_base hprop
  base_factorization := cert.base_factorization
  screened_factorization := cert.screened_factorization
  base_mass_pos := fun cap ↦ by
    change 0 < screenMass ((cert.parameters cap).toSpec.pointMass
      (cert.fiber.coordinateCap cap)) (cert.parameters cap).toSpec.upper
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
    have hbase := (ratioData cap).basePos
    have heq : (fun ell ↦
        (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true) =
      (fun ell ↦ ∀ b, (ell b : ℕ) ∈
        (cert.parameters cap).toSpec.acceptedBaseWindow b) := by
      funext ell
      apply propext
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
        decide_eq_true_eq] using
        (cert.parameters cap).toSpec.acceptedBaseProp_iff_windows ell
          (ratioData cap).coverage
    simpa only [heq] using hbase
  base_subset_piece := by
    intro cap s hs
    apply atom_subset_piece
    apply cert.fiber.atom_sound cap
    exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
      (cert.fiber.stoppingTime cap) (cert.fiber.initial cap) t
      (cert.fiber.start cap) (cert.fiber.retained cap)
      (cert.fiber.tail cap) (fun _q hq ↦ hq.1) hs.2⟩
  monotone_screened := monotone_screened
  transition_covered := transition_covered
  product_bound := fun cap ↦ by
    change conditionalScreenMass ((cert.parameters cap).toSpec.pointMass
      (cert.fiber.coordinateCap cap)) (cert.parameters cap).toSpec.upper
      (fun ell ↦ (cert.parameters cap).toSpec.acceptedBaseAccepts ell = true)
      (fun ell ↦
        (cert.parameters cap).toSpec.acceptedScreenedAccepts ell = true) ≤
      ratio.toReal
    exact (cert.parameters cap).toSpec.acceptedConditionalScreenMass_le
      (ratioData cap)

end RecoveryCertificate

end

end Erdos1165.HLOZPrefixedAllCreationCanonicalRefinement

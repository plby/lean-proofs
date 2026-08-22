/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationStaticSupportAggregateRefinement
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Data

/-!
# Static-support recovery for the canonical source screen

The positive-interface aggregate product cannot choose a candidate: its
exact source support may be empty.  This file removes that artificial
choice from the prefix-correct canonical recovery certificate.

On a nonempty support we reuse the already proved candidate recovery; its
accepted base window is independent of the chosen candidate.  On an empty
support there are no away dominoes, so the distinguished projection fixes
the entire insertion vector and recovery follows directly from `selected`.
-/

open Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceAggregateRecovery

open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Data.SourceThetaGoodRepresentative
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The candidate-independent broad source window on an exact `(z,S)` atom.
When `S` is nonempty this is definitionally the accepted base window of the
canonical candidate certificate.  When `S` is empty its domain is empty, so
the displayed value is immaterial. -/
noncomputable def sourceAggregateBaseWindow
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (low externalLow externalHigh cap : ℕ) :
    TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap) →
        Finset ℕ := by
  classical
  by_cases hS : eta.1.2.Nonempty
  · exact ((sourceParameters (cap := cap) eta hS.choose hS.choose_spec low
      externalLow externalHigh
      (shellZeroSourceTotalWindow m (shellWidth48 m))).toSpec).acceptedBaseWindow
  · exact fun _ ↦ ∅

theorem sourceAggregateBaseWindow_eq_of_nonempty
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (low externalLow externalHigh cap : ℕ) (hS : eta.1.2.Nonempty)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    sourceAggregateBaseWindow eta low externalLow externalHigh cap b =
      ((sourceParameters (cap := cap) eta hS.choose hS.choose_spec low
        externalLow externalHigh
        (shellZeroSourceTotalWindow m (shellWidth48 m))).toSpec).acceptedBaseWindow
          b := by
  simp [sourceAggregateBaseWindow, hS]

/-- Exact prefix-correct recovery for the aggregate source screen, with no
chosen coordinate and no nonempty-support hypothesis. -/
noncomputable def sourceStaticSupportRecoveryCertificate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (low externalLow externalHigh : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hzero : 0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m)) :
    StaticSupportRecoveryCertificate (SourceSupportData t o m k) eta where
  baseWindow cap := sourceAggregateBaseWindow eta low externalLow externalHigh cap
  recover cap q hselected hscreen := by
    classical
    by_cases hS : eta.1.2.Nonempty
    · apply (sourceRecoveryCertificate eta hS.choose hS.choose_spec low
        externalLow externalHigh
          (shellZeroSourceTotalWindow m (shellWidth48 m)) hm hk hzero).recover
            cap q hselected
      rcases hscreen with ⟨ell, hell, htotal⟩
      refine ⟨ell, ?_, htotal⟩
      have hbase : ((sourceParameters (cap := cap) eta hS.choose
          hS.choose_spec low externalLow externalHigh
          (shellZeroSourceTotalWindow m (shellWidth48 m))).toSpec).acceptedBaseProp
            ell := by
        have hcoverage :
            ((sourceParameters (cap := cap) eta hS.choose hS.choose_spec low
              externalLow externalHigh
              (shellZeroSourceTotalWindow m
                (shellWidth48 m))).toSpec).S ⊆
              Finset.univ.image fun b :
                ((sourceParameters (cap := cap) eta hS.choose hS.choose_spec low
                  externalLow externalHigh
                  (shellZeroSourceTotalWindow m
                    (shellWidth48 m))).toSpec).Away ↦
                prefixedTilingFixedDominantEndpoint
                  ((sourceParameters (cap := cap) eta hS.choose
                    hS.choose_spec low externalLow externalHigh
                    (shellZeroSourceTotalWindow m
                      (shellWidth48 m))).toSpec).initial
                  ((sourceParameters (cap := cap) eta hS.choose
                    hS.choose_spec low externalLow externalHigh
                    (shellZeroSourceTotalWindow m
                      (shellWidth48 m))).toSpec).x
                  ((sourceParameters (cap := cap) eta hS.choose
                    hS.choose_spec low externalLow externalHigh
                    (shellZeroSourceTotalWindow m
                      (shellWidth48 m))).toSpec).r
                  ((sourceParameters (cap := cap) eta hS.choose
                    hS.choose_spec low externalLow externalHigh
                    (shellZeroSourceTotalWindow m
                      (shellWidth48 m))).toSpec).terminal b.1 := by
          intro y hy
          let b := sourceChosen cap eta y hy
          refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
          exact sourceChosen_fixedDominant cap eta y hy
        apply (((sourceParameters (cap := cap) eta hS.choose hS.choose_spec low
          externalLow externalHigh
          (shellZeroSourceTotalWindow m (shellWidth48 m))).toSpec
            |>.acceptedBaseProp_iff_windows ell
              hcoverage).2)
        intro b
        rw [← sourceAggregateBaseWindow_eq_of_nonempty eta low externalLow
          externalHigh cap hS b]
        exact hell b
      dsimp only [sourceRecoveryCertificate]
      simpa only [PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseAccepts,
        decide_eq_true_eq] using hbase
    · let D := supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2
      let e := splitTilingCoordinatesEquiv
        (cap := (SourceFiber eta).coordinateCap cap) t
        eta.1.1.external.start eta.1.1.external.retained D
      change orientedAllCreationSelected o m k (SourceSupportAt t o m)
        eta.1.2 eta.1.1 ((SourceFiber eta).coordinateCap cap) (e q).1 at hselected
      rcases hselected with ⟨a, haSelected⟩
      have ha : a = (e q).2 := by
        funext b
        exfalso
        apply hS
        exact ⟨b.1.1,
          (away_mem_support_iff t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2 b.1).1 b.2⟩
      have hq : e.symm ((e q).1, a) = q := by
        rw [ha, Prod.eta, Equiv.symm_apply_apply]
      change orientedAllCreationStoppedAtomPredicate o m k
          (SourceSupportAt t o m) eta.1.2 eta.1.1
          ((SourceFiber eta).coordinateCap cap) q ∧
        PrefixedTilingStoppingAccepted
          (StoppedInsertion.truncatedLevelTime m k
            (orientedAllCreationCoordinateCutoff eta.1.1
              ((SourceFiber eta).coordinateCap cap)))
          eta.1.1.external.initial.1 t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ))
          eta.1.1.external.tail.1
      simpa only [e, D, hq] using haSelected

end

end Erdos1165.HLOZPrefixedCanonicalSourceAggregateRecovery

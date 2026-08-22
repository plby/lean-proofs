/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery
import ErdosProblems.Erdos1165.HLOZPrefixedProp49CandidateWindowRatio
import ErdosProblems.Erdos1165.HLOZShellZeroExternalWindow
import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

/-!
# Concrete Proposition 4.9 ratio data on one canonical source atom

This file turns the prefix-correct source recovery certificate into the
literal one-coordinate negative-binomial ratio.  The only history hypothesis
is the source-correct restricted-Theta screen on one representative of the
fixed stopped atom.  There is no transition probability or target
probability premise.
-/

open Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceProp49Data

open FiniteDominoProductLaw HLOZPathEvents
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZMeshCandidatePolynomialNumerics
open HLOZProposition48Candidates HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows HLOZThetaSourceBalance
open HLOZSourceOrientedExternalLocalTime
open HLOZTilingConditionalCandidateWindows
open LazyDecomposition
open SmallWindow SpatialInsertionFiber TilingAwayNegativeBinomial
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A source-correct representative of a fixed exact atom.  The full atom
already fixes the source support; this record adds precisely the good-history
restricted-Theta condition needed to identify the retained-count window. -/
structure SourceThetaGoodRepresentative
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (externalLow externalHigh : ℕ) where
  path : WalkPath
  mem_atom : path ∈ orientedAllCreationSupportTraceAtom
    t o m k (SourceSupportAt t o m) eta.1.1 eta.1.2
  theta_good : orientedTilingThetaBases t o m (shellWidth48 m)
    externalLow externalHigh path (creationTimeNat m k path) = ∅

namespace SourceThetaGoodRepresentative

private def transportExternalDomino
    {t : DominoTiling} {z z' : OrientedTilingTypedExternalWordCode t}
    (h : z = z')
    (b : TilingExternalDomino t z'.start z'.retained) :
    TilingExternalDomino t z.start z.retained :=
  cast (congrArg (fun w : OrientedTilingTypedExternalWordCode t ↦
    TilingExternalDomino t w.start w.retained) h.symm) b

@[simp] private theorem transportExternalDomino_base
    {t : DominoTiling} {z z' : OrientedTilingTypedExternalWordCode t}
    (h : z = z')
    (b : TilingExternalDomino t z'.start z'.retained) :
    (transportExternalDomino h b).1 = b.1 := by
  subst z'
  rfl

@[simp] private theorem card_coordinates_transportExternalDomino
    {t : DominoTiling} {z z' : OrientedTilingTypedExternalWordCode t}
    (h : z = z')
    (b : TilingExternalDomino t z'.start z'.retained) :
    Fintype.card (TilingCoordinatesAt t z.start z.retained
      (transportExternalDomino h b)) =
      Fintype.card (TilingCoordinatesAt t z'.start z'.retained b) := by
  subst z'
  rfl

theorem support_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh) :
    SourceSupportAt t o m good.path (creationTimeNat m k good.path) =
      eta.1.2 := good.mem_atom.2

theorem candidate_external_window
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    {candidate : Point} (hcandidate : candidate ∈ eta.1.2) :
    externalLow ≤ tilingSourceExternalBaseLocalTime t o good.path
        (creationTimeNat m k good.path) candidate ∧
      tilingSourceExternalBaseLocalTime t o good.path
        (creationTimeNat m k good.path) candidate < externalHigh := by
  classical
  have hsource : candidate ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) := by
    change candidate ∈ SourceSupportAt t o m good.path
      (creationTimeNat m k good.path)
    rw [good.support_eq]
    exact hcandidate
  have hsourceUnion : candidate ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
        shellZeroReplacementTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) := by
    rw [mem_orientedTilingVTwoBases_iff] at hsource ⊢
    refine ⟨?_, hsource.2⟩
    rw [tilingVTwoBases, Finset.mem_filter] at hsource ⊢
    exact ⟨hsource.1.1, hsource.1.2.1,
      Finset.mem_union_left _ hsource.1.2.2⟩
  have hnot : candidate ∉ orientedTilingThetaBases t o m (shellWidth48 m)
      externalLow externalHigh good.path
      (creationTimeNat m k good.path) := by
    rw [good.theta_good]
    simp
  rw [orientedTilingThetaBases, Finset.mem_filter, not_and_or] at hnot
  rcases hnot with hnot | hwindow
  · exact (hnot hsourceUnion).elim
  · exact not_not.mp hwindow

private noncomputable def externalIndex
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh) :
    TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k := by
  refine ⟨eta.1.1.external, good.path, ?_⟩
  exact ⟨good.mem_atom.1.1, good.mem_atom.1.2.1,
    congrArg OrientedAllCreationTraceCode.external good.mem_atom.1.2.2⟩

theorem fixedBoundary_eq_sourceExternal
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained)
    (hb : OrientationCompatible o b.1) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) b.1 =
      tilingSourceExternalBaseLocalTime t o good.path
        (creationTimeNat m k good.path) b.1 := by
  rcases eta with ⟨⟨⟨zext, zfavorite⟩, S⟩, heta⟩
  let indexed := good.externalIndex
  have hboundary := prefixedBoundaryLocalTime_eq_coordinateCard
    indexed hm hk (fun _ ↦ 0) b hb
  have hn : 0 < creationTimeNat m k good.path := by
    have hcreation : ThresholdCreation good.path m k
        (creationTimeNat m k good.path) := by
      simpa [creationTimeNat, good.mem_atom.1.2.1] using
        thresholdCreation_natFind good.mem_atom.1.2.1
    by_contra h
    have hnzero : creationTimeNat m k good.path = 0 := by omega
    rw [hnzero] at hcreation
    have hlocal := position_mem_thresholdSites_of_creation hk hcreation
    have hle := (mem_thresholdSites good.path 0 m (good.path 0)).mp hlocal |>.2
    have hzero : localTime good.path 0 (good.path 0) = 1 := by
      have hvalidZero : good.path 0 = (0, 0) := by
        rw [← good.mem_atom.1.1]
        rfl
      unfold localTime localTimePrefix pathPrefix
      simp [hvalidZero]
    rw [hzero] at hle
    omega
  have hvalid := good.mem_atom.1.1
  have hcode : fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k good.path) good.path = zext :=
    congrArg OrientedAllCreationTraceCode.external good.mem_atom.1.2.2
  let b0 := transportExternalDomino hcode b
  have hb0 : OrientationCompatible o b0.1 := by
    simpa only [b0, transportExternalDomino_base] using hb
  have hcard0 := card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
    t o good.path (creationTimeNat m k good.path) hvalid hn b0 hb0
  have hcard : Fintype.card (TilingCoordinatesAt t zext.start
      zext.retained b) =
      tilingSourceExternalBaseLocalTime t o good.path
        (creationTimeNat m k good.path) b.1 := by
    rw [← card_coordinates_transportExternalDomino hcode b]
    simpa only [b0, transportExternalDomino_base] using hcard0
  have hboundary' :
      prefixedTilingFixedBoundaryLocalTime zext.initial.1 zext.start
          zext.retained
          (prefixedTilingInsertionTerminal zext.initial t zext.start
            zext.retained (fun _ ↦ 0) zext.tail) b.1 =
        Fintype.card (TilingCoordinatesAt t zext.start zext.retained b) := by
    change prefixedTilingFixedBoundaryLocalTime zext.initial.1 zext.start
          zext.retained
          (prefixedTilingInsertionTerminal zext.initial t zext.start
            zext.retained (fun _ ↦ 0) zext.tail) b.1 =
        Fintype.card (TilingCoordinatesAt t zext.start zext.retained b)
      at hboundary
    exact hboundary
  change prefixedTilingFixedBoundaryLocalTime zext.initial.1 zext.start
      zext.retained
      (prefixedTilingInsertionTerminal zext.initial t zext.start
        zext.retained (fun _ ↦ 0) zext.tail) b.1 = _
  exact hboundary'.trans hcard

theorem coordinateCard_eq_sourceExternal
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained)
    (hb : OrientationCompatible o b.1) :
    Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b) =
      tilingSourceExternalBaseLocalTime t o good.path
        (creationTimeNat m k good.path) b.1 := by
  rcases eta with ⟨⟨⟨zext, zfavorite⟩, S⟩, heta⟩
  have hn : 0 < creationTimeNat m k good.path := by
    have hcreation : ThresholdCreation good.path m k
        (creationTimeNat m k good.path) := by
      simpa [creationTimeNat, good.mem_atom.1.2.1] using
        thresholdCreation_natFind good.mem_atom.1.2.1
    by_contra h
    have hnzero : creationTimeNat m k good.path = 0 := by omega
    rw [hnzero] at hcreation
    have hlocal := position_mem_thresholdSites_of_creation hk hcreation
    have hle := (mem_thresholdSites good.path 0 m (good.path 0)).mp hlocal |>.2
    have hzero : localTime good.path 0 (good.path 0) = 1 := by
      have hvalidZero : good.path 0 = (0, 0) := by
        rw [← good.mem_atom.1.1]
        rfl
      unfold localTime localTimePrefix pathPrefix
      simp [hvalidZero]
    rw [hzero] at hle
    omega
  have hcode : fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k good.path) good.path = zext :=
    congrArg OrientedAllCreationTraceCode.external good.mem_atom.1.2.2
  let b0 := transportExternalDomino hcode b
  have hb0 : OrientationCompatible o b0.1 := by
    simpa only [b0, transportExternalDomino_base] using hb
  have hcard0 := card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
    t o good.path (creationTimeNat m k good.path) good.mem_atom.1.1 hn b0 hb0
  rw [← card_coordinates_transportExternalDomino hcode b]
  simpa only [b0, transportExternalDomino_base] using hcard0

theorem fixedBoundary_eq_coordinateCard
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained)
    (hb : OrientationCompatible o b.1) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) b.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b) :=
  (good.fixedBoundary_eq_sourceExternal hm hk b hb).trans
    (good.coordinateCard_eq_sourceExternal hm hk b hb).symm

theorem away_mem_sourceSupport
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    b.1.1 ∈ eta.1.2 := by
  exact (away_mem_support_iff t eta.1.1.external.start
    eta.1.1.external.retained eta.1.2 b.1).mp b.2

theorem away_fixedBoundary_partner_le_base
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (sourceTerminal eta) (tilingPartner t b.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (sourceTerminal eta) b.1.1 := by
  have h := sourceChosen_fixedBoundary_partner_le_base (cap := cap) eta b.1.1
    (away_mem_sourceSupport eta b)
  have hbase := sourceChosen_base cap eta b.1.1
    (away_mem_sourceSupport eta b)
  rw [hbase] at h
  exact h

theorem away_fixedBoundary_external_window
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    externalLow ≤ prefixedTilingFixedBoundaryLocalTime
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (sourceTerminal eta) b.1.1 ∧
      prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        (sourceTerminal eta) b.1.1 < externalHigh := by
  have hS := away_mem_sourceSupport eta b
  have hext := good.candidate_external_window hS
  have hsource : b.1.1 ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) := by
    change b.1.1 ∈ SourceSupportAt t o m good.path
      (creationTimeNat m k good.path)
    rw [good.support_eq]
    exact hS
  have hcompatible := (mem_orientedTilingVTwoBases_iff t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) b.1.1).mp hsource |>.2
  have heq := good.fixedBoundary_eq_sourceExternal hm hk b.1 hcompatible
  change externalLow ≤ prefixedTilingFixedBoundaryLocalTime
      eta.1.1.external.initial.1 eta.1.1.external.start
      eta.1.1.external.retained (sourceTerminal eta) b.1.1 ∧
    prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
      eta.1.1.external.start eta.1.1.external.retained
      (sourceTerminal eta) b.1.1 < externalHigh
  rw [heq]
  exact hext

theorem source_coverage
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) :
    eta.1.2 ⊆ Finset.univ.image fun b :
      TilingAwayDomino t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap) ↦
      prefixedTilingFixedDominantEndpoint ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        (sourceTerminal eta) b.1 := by
  intro candidate hcandidate
  let b := sourceChosen cap eta candidate hcandidate
  refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
  exact sourceChosen_fixedDominant cap eta candidate hcandidate

theorem acceptedBaseWindow_eq_shifted
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low externalLow externalHigh : ℕ)
    {externalLow' externalHigh' : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow' externalHigh')
    (hexternalLow : externalLow = externalLow')
    (hexternalHigh : externalHigh = externalHigh')
    (hm : 1 < m) (hk : 0 < k)
    (narrowWindow : Finset ℕ)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    ((sourceParameters (cap := cap) eta candidate hcandidate low externalLow
      externalHigh narrowWindow).toSpec).acceptedBaseWindow b =
      shiftedEndpointWindow
        (prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (sourceTerminal eta) b.1.1)
        ((SourceFiber eta).upper cap b)
        (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
  classical
  let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
    externalLow externalHigh narrowWindow).toSpec
  have hdominant := away_fixedBoundary_partner_le_base eta b
  have hS := away_mem_sourceSupport eta b
  have hext := good.away_fixedBoundary_external_window hm hk b
  rw [← hexternalLow, ← hexternalHigh] at hext
  change spec.acceptedBaseWindow b = _
  unfold PrefixedCanonicalDominantCandidateWindowSpec.acceptedBaseWindow
    PrefixedCanonicalDominantCandidateWindowSpec.baseWindow
  rw [prefixedCanonicalCandidateBaseWindow_chosen spec.initial spec.t spec.x
      spec.r spec.terminal spec.D spec.upper spec.m spec.w spec.low
      spec.externalLow spec.externalHigh spec.broadWindow spec.S b
      hdominant hS hext rfl]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    change prefixedTilingFixedBoundaryDominoMax
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (sourceTerminal eta) b.1 + v < m
    unfold prefixedTilingFixedBoundaryDominoMax
    rw [max_eq_left hdominant]
    exact (mem_shellZeroSourceTotalWindow.mp
      (Finset.mem_filter.mp hv).2).2

theorem away_orientationCompatible
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    {externalLow externalHigh : ℕ}
    (good : SourceThetaGoodRepresentative eta externalLow externalHigh)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    OrientationCompatible o b.1.1 := by
  have hsource : b.1.1 ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) := by
    change b.1.1 ∈ SourceSupportAt t o m good.path
      (creationTimeNat m k good.path)
    rw [good.support_eq]
    exact away_mem_sourceSupport eta b
  exact (mem_orientedTilingVTwoBases_iff t o
    (shellZeroSourceTotalWindow m (shellWidth48 m)) good.path
      (creationTimeNat m k good.path) b.1.1).mp hsource |>.2

theorem m_le_sourceFiber_totalCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) :
    m ≤ (SourceFiber eta).totalCap := by
  change m ≤ max eta.1.1.external.retainedCount (m + shellWidth48 m)
  omega

theorem acceptedBaseCoordinateMass_pos
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (narrowWindow : Finset ℕ)
    (b : TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)) :
    0 < ∑ v : Fin (((sourceParameters (cap := cap) eta candidate hcandidate
        low (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
        narrowWindow).toSpec).upper b),
      if (v : ℕ) ∈ ((sourceParameters (cap := cap) eta candidate hcandidate
          low (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
          narrowWindow).toSpec).acceptedBaseWindow b then
        coordinateMass
          (((sourceParameters (cap := cap) eta candidate hcandidate low
            (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
            narrowWindow).toSpec).pointMass
              ((SourceFiber eta).coordinateCap cap))
          ((sourceParameters (cap := cap) eta candidate hcandidate low
            (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
            narrowWindow).toSpec).upper b v else 0 := by
  classical
  let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    narrowWindow).toSpec
  let i := Fintype.card (TilingCoordinatesAt t ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) b.1)
  have hcompatible := good.away_orientationCompatible b
  have hboundaryCard := good.fixedBoundary_eq_coordinateCard hm hk b.1
    hcompatible
  have hboundaryCard' : prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta) b.1.1 = i := by
    change prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) b.1.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b.1)
    exact hboundaryCard
  have hext := good.away_fixedBoundary_external_window hm hk b
  have hiWindow := hexternalArithmetic _ hext.1 hext.2
  rw [hboundaryCard'] at hiWindow
  have hi : 0 < i := by
    exact HLOZSourceOrientedThetaProduct.card_tilingCoordinatesAt_pos
      t ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap) b.1
  have hmTotal : m ≤ (SourceFiber eta).totalCap :=
    m_le_sourceFiber_totalCap eta
  have hupperM : m ≤ spec.upper b := by
    exact hmTotal.trans ((SourceFiber eta).totalCap_lt_upper cap b).le
  have hcoordinateM : m ≤ (SourceFiber eta).coordinateCap cap :=
    hmTotal.trans ((SourceFiber eta).totalCap_le_coordinateCap cap)
  have hshiftUpper : m - i ≤ spec.upper b := by omega
  have hwindowEq : spec.acceptedBaseWindow b =
      shellZeroSourceFailureWindow m (shellWidth48 m) i := by
    calc
      spec.acceptedBaseWindow b = shiftedEndpointWindow
          (prefixedTilingFixedBoundaryLocalTime ((SourceFiber eta).initial cap)
            ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
            (sourceTerminal eta) b.1.1)
          (spec.upper b)
          (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
            exact good.acceptedBaseWindow_eq_shifted candidate hcandidate low
              (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) rfl rfl
              hm hk narrowWindow b
      _ = shiftedEndpointWindow i (spec.upper b)
          (shellZeroSourceTotalWindow m (shellWidth48 m)) := by
            rw [hboundaryCard']
      _ = shellZeroSourceFailureWindow m (shellWidth48 m) i := by
            exact shiftedEndpointWindow_shellZeroSourceTotalWindow
              hiWindow.2.1 harithmetic.2.1 hshiftUpper
  have hwindowUpper : ∀ v ∈ spec.acceptedBaseWindow b, v < spec.upper b := by
    intro v hv
    rw [hwindowEq] at hv
    have hv' := (mem_shellZeroSourceFailureWindow.mp hv).2
    omega
  have hwindowCap : ∀ v ∈ spec.acceptedBaseWindow b,
      v ≤ (SourceFiber eta).coordinateCap cap := by
    intro v hv
    rw [hwindowEq] at hv
    have hv' := (mem_shellZeroSourceFailureWindow.mp hv).2
    omega
  have hwindowPos : 0 < windowMass i (spec.acceptedBaseWindow b) := by
    rw [hwindowEq]
    exact windowMass_pos hi (shellZeroSourceFailureWindow_nonempty
      hiWindow.2.1 harithmetic.1 harithmetic.2.1)
  have hdenPos : 0 < ∑ j : Fin (spec.upper b),
      spec.pointMass ((SourceFiber eta).coordinateCap cap) b j := by
    let v0 : Fin (spec.upper b) := ⟨0, by
      exact (SourceFiber eta).upper_pos cap b⟩
    have hv0 : 0 < spec.pointMass ((SourceFiber eta).coordinateCap cap) b v0 := by
      change 0 < tilingAwayPointMass
        (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) b 0
      exact tilingAwayExactTotalMass_zero_pos
        (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) b
    exact hv0.trans_le (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (spec.upper b) ↦
        spec.pointMass ((SourceFiber eta).coordinateCap cap) b j)
      (fun j _ ↦ tilingAwayExactTotalMass_nonneg t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) b j)
      (Finset.mem_univ v0))
  have heq := sum_tilingAway_coordinateMass_window t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).distinguished cap) spec.upper b
    (spec.acceptedBaseWindow b) hwindowUpper hwindowCap hi
  have hdenPos' : 0 < ∑ j : Fin (spec.upper b),
      tilingAwayPointMass (cap := (SourceFiber eta).coordinateCap cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) b j := by
    change 0 < ∑ j : Fin (spec.upper b),
      spec.pointMass ((SourceFiber eta).coordinateCap cap) b j at hdenPos
    exact hdenPos
  have hpos := div_pos hwindowPos hdenPos'
  rw [← heq] at hpos
  change 0 < ∑ v : Fin (spec.upper b),
      if (v : ℕ) ∈ spec.acceptedBaseWindow b then
        coordinateMass (tilingAwayPointMass
          (cap := (SourceFiber eta).coordinateCap cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          ((SourceFiber eta).distinguished cap)) spec.upper b v else 0
  exact hpos

theorem acceptedBaseScreenMass_pos
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (narrowWindow : Finset ℕ) :
    let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      narrowWindow).toSpec
    0 < screenMass (spec.pointMass ((SourceFiber eta).coordinateCap cap))
      spec.upper (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b) := by
  classical
  dsimp only
  rw [screenMass_all_coordinate_windows_eq_prod]
  exact Finset.prod_pos fun b _ ↦ good.acceptedBaseCoordinateMass_pos
    candidate hcandidate low hm hk harithmetic hexternalArithmetic
      narrowWindow b

/-- The prefix-correct canonical source specification with the literal
Proposition 4.9 narrow window.  Keeping this specialization opaque avoids
re-elaborating the large dependent coordinate record in every public ratio
theorem. -/
noncomputable def sourceProp49Spec
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) : PrefixedCanonicalDominantCandidateWindowSpec :=
  (sourceParameters (cap := cap) eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a)).toSpec

private theorem sourceProp49_chosen_ratio
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (prop49NarrowTotalWindow m a)).toSpec
    windowMass
        (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
        (spec.acceptedScreenedWindow spec.chosen) ≤
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal *
        windowMass
          (Fintype.card
            (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
          (spec.acceptedBaseWindow spec.chosen) := by
  classical
  dsimp only
  let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a)).toSpec
  change windowMass
      (Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
      (spec.acceptedScreenedWindow spec.chosen) ≤
    (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal *
      windowMass
        (Fintype.card
          (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1))
        (spec.acceptedBaseWindow spec.chosen)
  have hnarrow : prop49NarrowTotalWindow m a ⊆
      shellZeroSourceTotalWindow m (shellWidth48 m) :=
    prop49NarrowTotalWindow_subset_source
      ((show 1 ≤ 2 by norm_num).trans harithmetic.1) harithmetic.2.1
      hwindow.cut_le_width_pred
  have hdominant := sourceChosen_fixedBoundary_partner_le_base (cap := cap)
    eta candidate hcandidate
  have hS : spec.chosen.1.1 ∈ spec.S := by
    change (sourceChosen cap eta candidate hcandidate).1.1 ∈ eta.1.2
    simpa only [sourceChosen_base] using hcandidate
  have hext := good.away_fixedBoundary_external_window (cap := cap) hm hk
    spec.chosen
  have hbaseEq := spec.acceptedBaseWindow_chosen hdominant hS hext rfl
  have hscreenedEq := spec.acceptedScreenedWindow_chosen hdominant hS hext
    rfl hnarrow
  have hcompatible := good.away_orientationCompatible (cap := cap) spec.chosen
  have hboundaryCard := good.fixedBoundary_eq_coordinateCard hm hk
    spec.chosen.1 hcompatible
  have hboundaryCard' : prefixedTilingFixedBoundaryLocalTime spec.initial
      spec.x spec.r spec.terminal spec.chosen.1.1 =
      Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) := by
    change prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) (sourceChosen cap eta candidate hcandidate).1.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained
        (sourceChosen cap eta candidate hcandidate).1)
    exact hboundaryCard
  have hboundaryCardFiber : prefixedTilingFixedBoundaryLocalTime
      ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta)
      spec.chosen.1.1 =
      Fintype.card (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) := by
    change prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (sourceTerminal eta) (sourceChosen cap eta candidate hcandidate).1.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained
        (sourceChosen cap eta candidate hcandidate).1)
    exact hboundaryCard
  have hiWindow := hexternalArithmetic _ hext.1 hext.2
  rw [hboundaryCardFiber] at hiWindow
  have hmTotal : m ≤ (SourceFiber eta).totalCap :=
    m_le_sourceFiber_totalCap eta
  have hupperM : m ≤ spec.upper spec.chosen :=
    hmTotal.trans ((SourceFiber eta).totalCap_lt_upper cap spec.chosen).le
  have hshiftUpper : m - Fintype.card
      (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1) ≤
      spec.upper spec.chosen := by omega
  rw [hscreenedEq, hbaseEq, hboundaryCard']
  rw [prop49CandidateRatioEnvelope_toReal
    prop49WindowRatioConstant_pos.le]
  exact shiftedEndpointWindow_prop49_mass_le a hwindow harithmetic
    hiWindow.1 hiWindow.2.1 hiWindow.2.2 hshiftUpper

private structure SourceProp49SupportData (cap : ℕ)
    (spec : PrefixedCanonicalDominantCandidateWindowSpec) : Prop where
  screenedUpper : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen,
    v < spec.upper spec.chosen
  baseUpper : ∀ v ∈ spec.acceptedBaseWindow spec.chosen,
    v < spec.upper spec.chosen
  screenedCap : ∀ v ∈ spec.acceptedScreenedWindow spec.chosen, v ≤ cap
  baseCap : ∀ v ∈ spec.acceptedBaseWindow spec.chosen, v ≤ cap
  coordinates : 0 < Fintype.card
    (TilingCoordinatesAt spec.t spec.x spec.r spec.chosen.1)

private theorem sourceProp49_supportData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (cap : ℕ) :
    SourceProp49SupportData ((SourceFiber eta).coordinateCap cap)
      ((sourceParameters (cap := cap) eta candidate hcandidate low
        (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
        (prop49NarrowTotalWindow m a)).toSpec) := by
  classical
  let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a)).toSpec
  change SourceProp49SupportData ((SourceFiber eta).coordinateCap cap) spec
  have hnarrow : prop49NarrowTotalWindow m a ⊆
      shellZeroSourceTotalWindow m (shellWidth48 m) :=
    prop49NarrowTotalWindow_subset_source
      ((show 1 ≤ 2 by norm_num).trans harithmetic.1) harithmetic.2.1
      hwindow.cut_le_width_pred
  have hdominant := sourceChosen_fixedBoundary_partner_le_base (cap := cap)
    eta candidate hcandidate
  have hS : spec.chosen.1.1 ∈ spec.S := by
    change (sourceChosen cap eta candidate hcandidate).1.1 ∈ eta.1.2
    simpa only [sourceChosen_base] using hcandidate
  have hext := good.away_fixedBoundary_external_window (cap := cap) hm hk
    spec.chosen
  have hbaseEq := spec.acceptedBaseWindow_chosen hdominant hS hext rfl
  have hscreenedEq := spec.acceptedScreenedWindow_chosen hdominant hS hext
    rfl hnarrow
  refine {
    screenedUpper := ?_
    baseUpper := ?_
    screenedCap := ?_
    baseCap := ?_
    coordinates := HLOZSourceOrientedThetaProduct.card_tilingCoordinatesAt_pos
      spec.t spec.x spec.r spec.chosen.1 }
  · intro v hv
    rw [hscreenedEq] at hv
    exact Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  · intro v hv
    rw [hbaseEq] at hv
    exact Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  · intro v hv
    have hv' := hv
    rw [hscreenedEq] at hv'
    have hvupper := Finset.mem_range.mp (Finset.mem_filter.mp hv').1
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1 at hvupper
    omega
  · intro v hv
    have hv' := hv
    rw [hbaseEq] at hv'
    have hvupper := Finset.mem_range.mp (Finset.mem_filter.mp hv').1
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1 at hvupper
    omega

private theorem sourceProp49_coverage
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) :
    let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (prop49NarrowTotalWindow m a)).toSpec
    spec.S ⊆ Finset.univ.image fun b : spec.Away ↦
      prefixedTilingFixedDominantEndpoint spec.initial spec.x spec.r
        spec.terminal b.1 := by
  classical
  dsimp only
  intro point hpoint
  let b := sourceChosen cap eta point hpoint
  refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
  exact sourceChosen_fixedDominant cap eta point hpoint

private theorem sourceProp49_basePos
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    let spec := (sourceParameters (cap := cap) eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (prop49NarrowTotalWindow m a)).toSpec
    0 < screenMass (spec.pointMass ((SourceFiber eta).coordinateCap cap))
      spec.upper (fun ell ↦ ∀ b, (ell b : ℕ) ∈ spec.acceptedBaseWindow b) := by
  classical
  dsimp only
  exact good.acceptedBaseScreenMass_pos candidate hcandidate low hm hk
    harithmetic hexternalArithmetic (prop49NarrowTotalWindow m a)

set_option linter.unusedVariables false in
set_option linter.constructorNameAsVariable false in
/-- Fully checked one-coordinate Proposition 4.9 ratio data on every logical
cap of a canonical source atom. -/
theorem acceptedRatioData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ)
    (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    PrefixedCanonicalDominantCandidateWindowSpec.AcceptedRatioData
      ((SourceFiber eta).coordinateCap cap)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a).toReal
      ((sourceParameters (cap := cap) eta candidate hcandidate low
        (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
        (prop49NarrowTotalWindow m a)).toSpec) := by
  classical
  have support := sourceProp49_supportData a candidate hcandidate low good hm hk
    hwindow harithmetic cap
  refine {
    coverage := sourceProp49_coverage a candidate hcandidate low
    basePos := sourceProp49_basePos a candidate hcandidate low good hm hk
      harithmetic hexternalArithmetic
    screenedUpper := support.screenedUpper
    baseUpper := support.baseUpper
    screenedCap := support.screenedCap
    baseCap := support.baseCap
    coordinates := support.coordinates
    ratio := sourceProp49_chosen_ratio a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic cap }

end SourceThetaGoodRepresentative

end

end Erdos1165.HLOZPrefixedCanonicalSourceProp49Data

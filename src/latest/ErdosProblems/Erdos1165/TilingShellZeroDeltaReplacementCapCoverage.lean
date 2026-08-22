/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaReplacementPrefixInvariant
import ErdosProblems.Erdos1165.TilingShellZeroDeltaGeometricBound

/-!
# Sound stopped cylinders for one honest actual-increment replacement clock

The coordinate predicate reconstructs the canonical actual-increment atom.
Prefix invariance then promotes that result to every physical walk in the
same stopped cylinder.
-/

open Set

namespace Erdos1165.TilingShellZeroDeltaReplacementCapCoverage

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroActualDeltaReplacementPrefixInvariant
open TilingShellZeroDeltaGeometricBound
open TilingShellZeroDeltaReplacementFactorization
open TilingShellZeroDeltaReplacementSound
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourcePartition TilingShellZeroSourceScreenForward
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Every literal fixed-delta stopped cylinder is contained in the honest
actual-increment replacement atom. -/
theorem replacement_cap_sound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m) (htotal : 0 < total)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total))
    (cap : ℕ) :
    walkLift (prefixedTilingPreStoppingFiberEvent
      (replacementStoppingTime eta.1.1 m k cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (coordinateCap eta.1.1 m cap) eta.1.1.tail.1
      (replacementPredicate eta cap
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
          delta)) ⊆
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
          delta eta.1.1 eta.1.2 := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let qNat : Fin (eta.1.1.retainedCount + 1) → ℕ := fun j ↦ (q.1 j : ℕ)
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained qNat eta.1.1.tail.1
  let canonical := canonicalPath eta.1.1 qNat
  have hcanonical := replacement_sound eta hm hk hlow harithmetic hexternal
    (centralReplacementUpperCount_lt htotal) delta q.1 q.2.1
  have hpRaw := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    eta.1.1.initial.1 eta.1.1.start eta.1.1.retained qNat
      eta.1.1.tail.1 (stepsOfWalk s) hq
  have hp : pathPrefix canonical v.length = pathPrefix s v.length := by
    have hp' : pathPrefix (trajectory (stepsOfWalk s)) v.length =
        pathPrefix canonical v.length := by
      simpa only [v, canonical, canonicalPath] using hpRaw
    rw [hvalid] at hp'
    exact hp'.symm
  have hcreation : ThresholdCreation canonical m (k + (delta : ℕ))
      v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap))
      v.length (extendPrefix (directionVectorOfList v))
      (insertion_lt_cutoff eta.1.1 m cap q.1)).mp
    simpa only [PrefixedTilingStoppingAccepted, replacementStoppingTime,
      canonical, v, qNat] using q.2.2
  have htime : creationTimeNat m (k + (delta : ℕ)) canonical = v.length :=
    creationTimeNat_eq_of_creation hcreation
  apply actualDeltaReplacementStaticSupportAtom_of_pathPrefix_eq delta
    hcanonical hvalid
  rw [htime]
  exact hp

end

end Erdos1165.TilingShellZeroDeltaReplacementCapCoverage

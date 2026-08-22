/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticSupportPartition

/-!
# Shell-zero replacement partitioned by its actual endpoint increment

Changing one domino insertion total can change the threshold status of both
endpoints.  The replacement clock must therefore be indexed by the actual
endpoint-count increment, rather than by the number of moved dominoes.

For `moved = total - central`, at most `2 * moved` endpoint indicators can
change.  `ReplacementEndpointIncrement total central` is the finite safe
range `0, ..., 2 * moved`.  At each fixed increment the creation rank is
again common, so the oriented external word and static support give the
same variable-clock disjoint partition as before.
-/

open Set

namespace Erdos1165.TilingShellZeroActualDeltaPartition

open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourcePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Number of coordinates moved from `I₁` to `I₀`. -/
def replacementMovedCount (total central : ℕ) : ℕ := total - central

/-- Safe finite range for the actual number of newly favorite endpoints.
The upper bound has a factor two because a domino has two endpoints. -/
abbrev ReplacementEndpointIncrement (total central : ℕ) :=
  Fin (2 * replacementMovedCount total central + 1)

/-- The honest replacement creation rank at an actual endpoint increment. -/
def actualReplacementCreationRank (k : ℕ)
    {total central : ℕ}
    (delta : ReplacementEndpointIncrement total central) : ℕ :=
  k + delta

theorem replacementEndpointIncrement_le_twiceMoved
    {total central : ℕ}
    (delta : ReplacementEndpointIncrement total central) :
    (delta : ℕ) ≤ 2 * replacementMovedCount total central := by
  omega

theorem replacementEndpointIncrement_complete
    {total central delta : ℕ}
    (hdelta : delta ≤ 2 * replacementMovedCount total central) :
    ∃ d : ReplacementEndpointIncrement total central, (d : ℕ) = delta := by
  exact ⟨⟨delta, by omega⟩, rfl⟩

/-- Static moved support read at the actual replacement clock. -/
def actualDeltaReplacementStaticSupport
    (t : DominoTiling) (o : Orientation)
    (m k w total central : ℕ)
    (delta : ReplacementEndpointIncrement total central)
    (s : WalkPath) : Finset Point :=
  let n := creationTimeNat m (actualReplacementCreationRank k delta) s
  orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w) s n ∪
    orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w) s n

/-- Fixed-count replacement event at its honest endpoint-count increment. -/
def orientedShellZeroActualDeltaReplacementEvent
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (delta : ReplacementEndpointIncrement total central) : Set WalkPath :=
  let rank := actualReplacementCreationRank k delta
  {s | ReachesThreshold s m rank ∧
    let n := creationTimeNat m rank s
    tilingDtildeEtaAt t m k w low s n ∧
      orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ ∧
      (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n).card = central ∧
      (orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s n).card = total - central}

/-- Valid external/static-support atom at one actual increment. -/
def orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (delta : ReplacementEndpointIncrement total central)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  orientedShellZeroActualDeltaReplacementEvent t o m k w low externalLow
      externalHigh total central delta ∩
    {s | fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m (actualReplacementCreationRank k delta) s) s = z} ∩
    validStepWalk ∩
    {s | actualDeltaReplacementStaticSupport t o m k w total central delta s = S}

/-- The fixed-increment event is covered by its physical external word and
static moved support. -/
theorem iUnion_all_actualDeltaReplacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (delta : ReplacementEndpointIncrement total central) :
    (⋃ p : OrientedTilingTypedExternalWordCode t × Finset Point,
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k w low externalLow externalHigh total central delta p.1 p.2) =
      orientedShellZeroActualDeltaReplacementEvent t o m k w low externalLow
        externalHigh total central delta ∩ validStepWalk := by
  ext s
  simp only [Set.mem_iUnion,
    orientedValidShellZeroActualDeltaReplacementStaticSupportAtom,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨⟨⟨hevent, _⟩, hvalid⟩, _⟩⟩
    exact ⟨hevent, hvalid⟩
  · rintro ⟨hevent, hvalid⟩
    let z := fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (actualReplacementCreationRank k delta) s) s
    let S := actualDeltaReplacementStaticSupport
      t o m k w total central delta s
    exact ⟨(z, S), ⟨⟨⟨hevent, rfl⟩, hvalid⟩, rfl⟩⟩

/-- At a fixed actual increment, the external word and support are
functional at one common creation rank. -/
theorem pairwise_disjoint_actualDeltaReplacementStaticSupportAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (delta : ReplacementEndpointIncrement total central) :
    Pairwise fun p q : OrientedTilingTypedExternalWordCode t × Finset Point ↦
      Disjoint
        (orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
          t o m k w low externalLow externalHigh total central delta p.1 p.2)
        (orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
          t o m k w low externalLow externalHigh total central delta q.1 q.2) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro s hs ht
  apply hpq
  apply Prod.ext
  · exact hs.1.1.2.symm.trans ht.1.1.2
  · exact hs.2.symm.trans ht.2

end

end Erdos1165.TilingShellZeroActualDeltaPartition

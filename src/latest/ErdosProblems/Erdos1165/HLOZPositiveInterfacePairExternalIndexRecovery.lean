/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportFiber

/-!
# Canonical external history for one physical positive-interface pair

The pair-support product must later be summed over complete stopped external
histories.  This file fixes the canonical history attached to a path at its
rank-`k` creation clock.  In particular, neither the current favorite data
nor a proof-dependent choice of a nonempty atom enters the index.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePairExternalIndexRecovery

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The complete external word and exact adjacent-row support seen at the
rank-`k` creation clock of `s`. -/
def positiveInterfaceExternalPairHistory
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) (s : WalkPath) :
    OrientedTilingTypedExternalWordCode t × Finset Point :=
  (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s,
    PositiveInterfacePairSupportAt t o m externalThreshold width shell s
      (creationTimeNat m k s))

/-- A valid path reaching its `k`-th level-`m` creation canonically inhabits
the external pair-history atom determined by its own stopped prefix. -/
noncomputable def positiveInterfaceExternalPairSupportedIndexOfPath
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) (s : WalkPath)
    (hvalid : s ∈ validStepWalk) (hreach : ReachesThreshold s m k) :
    PositiveInterfaceExternalPairSupportedIndex t o m k externalThreshold
      width shell := by
  let history := positiveInterfaceExternalPairHistory t o m k
    externalThreshold width shell s
  refine ⟨history, ⟨s, ?_⟩⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  exact ⟨hvalid, hreach, rfl, rfl⟩

@[simp] theorem positiveInterfaceExternalPairSupportedIndexOfPath_code
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) (s : WalkPath)
    (hvalid : s ∈ validStepWalk) (hreach : ReachesThreshold s m k) :
    (positiveInterfaceExternalPairSupportedIndexOfPath t o m k
      externalThreshold width shell s hvalid hreach).1.1 =
      fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s := by
  rfl

@[simp] theorem positiveInterfaceExternalPairSupportedIndexOfPath_support
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) (s : WalkPath)
    (hvalid : s ∈ validStepWalk) (hreach : ReachesThreshold s m k) :
    (positiveInterfaceExternalPairSupportedIndexOfPath t o m k
      externalThreshold width shell s hvalid hreach).1.2 =
      orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s (creationTimeNat m k s) := by
  rfl

/-- Membership in the canonical atom, exposed as a theorem so downstream
cap-recovery proofs do not unfold the subtype witness. -/
theorem mem_externalPairAtom_ofPath
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) (s : WalkPath)
    (hvalid : s ∈ validStepWalk) (hreach : ReachesThreshold s m k) :
    s ∈ orientedExternalAllCreationSupportTraceAtom t o m k
      (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
      (positiveInterfaceExternalPairSupportedIndexOfPath t o m k
        externalThreshold width shell s hvalid hreach).1.1
      (positiveInterfaceExternalPairSupportedIndexOfPath t o m k
        externalThreshold width shell s hvalid hreach).1.2 := by
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  exact ⟨hvalid, hreach, rfl, rfl⟩

end

end Erdos1165.HLOZPositiveInterfacePairExternalIndexRecovery

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseScanSignature
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice
import ErdosProblems.Erdos1165.AsymmetricTerminalPartitionAdapter

/-!
# Left-signature restriction for terminal right replacements

An arbitrary terminal bridge around `y` need not preserve the coarser
excursion clocks around `x`: before the first separation level the small
`y`-disc may meet an `x`-boundary.  The correct retained datum is therefore
the finite `x` scanner signature through separation.  Above separation the
terminal bridge is confined to the separated `y`-disc, so the remaining
signature coordinates are automatic.

This file packages that deterministic correction.  Restricting a bridge
family by its retained prefix signature only decreases its literal kernel;
no probability comparison is used here.
-/

open Set

namespace Erdos1165.AsymmetricTerminalLeftSignatureRestriction

open AnnularProfileClocks AppendixPair
open AsymmetricCoarseScanSignature AsymmetricPairSeparationGeometry
open AsymmetricPostSeparationReturnSignature
open AsymmetricSplitCompletionPreservation AsymmetricSplitLevelSplice
open AsymmetricTerminalPartitionAdapter MarkedBoundaryVisitKernel
open MarkedBridgeFactorization
open MarkedSkeletonPartition TerminalExcursionPathwise
open TerminalGlobalExitSplice TerminalSequentialVisitLaw
open TerminalSkeletonFactorization TerminalSkeletonWords
open TerminalProfileClockEquivalence TerminalSkeletonInvariance
open TerminalSpliceProfileGeometry ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A terminal first-hit word is confined to every earlier `y` profile
disc. -/
theorem terminalBridge_wordWalk_mem_separationDisc
    {n splitLevel : ℕ} {y start endpoint : Point}
    (hn : 1 ≤ n) (hsplit : splitLevel ≤ n)
    (hstart : start ∈ terminalInnerBoundary n y)
    (bridge : BoundaryExitWordCode
      (terminalOuterBoundary n y) start endpoint) :
    ∀ q ≤ (List.ofFn bridge.1.2).length,
      wordWalk start (List.ofFn bridge.1.2) q ∈
        disc y (scaleRadius n splitLevel) := by
  have hwithin : WordWithin (disc y (scaleRadius n n)) start
      (List.ofFn bridge.1.2) :=
    unmarkedTerminalBridge_wordWithin hn hstart bridge
  intro q hq
  exact (wordWalk_mem_of_wordWithin hwithin q hq).trans
    (scaleRadius_antitone_of_le hsplit le_rfl)

/-- Endpoint-matched words confined to the separated `y` disc have the same
effect also on the terminal `x` scanner.  The regular coordinates are the
existing post-separation cancellation theorem; only `k = n + 1` needs the
terminal-inner-boundary argument. -/
theorem scanWordFrom_eq_of_postSeparation_confined_words_terminal
    {n k : ℕ} {x y start : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y < k) (hkUpper : k ≤ n + 1)
    (state : BoundaryScanState) (leftWord rightWord : List Direction)
    (hleft : ∀ q ≤ leftWord.length,
      wordWalk start leftWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hright : ∀ q ≤ rightWord.length,
      wordWalk start rightWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state leftWord =
      scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state rightWord := by
  by_cases hkn : k ≤ n
  · exact scanWordFrom_eq_of_postSeparation_confined_words
      hlevel hkLower hkn state leftWord rightWord hleft hright hend
  · have hk : k = n + 1 := by omega
    subst k
    let D := disc y (scaleRadius n (separationLevel n x y))
    have hsep : Disjoint (disc x (scaleRadius n n)) D := by
      simpa only [D] using
        (regularDisc_disjoint_postSeparationDisc hlevel hlevel le_rfl)
    have avoid (word : List Direction)
        (hword : ∀ q ≤ word.length, wordWalk start word q ∈ D) :
        ∀ q, 0 < q → q ≤ word.length →
          wordWalk start word q ∉ profileOuterBoundary n (n + 1) x ∧
          wordWalk start word q ∉ profileInnerBoundary n (n + 1) x := by
      intro q _hqpos hq
      have hz : wordWalk start word q ∈ D := hword q hq
      constructor
      · simpa only [profileOuterBoundary, Nat.add_sub_cancel] using
          (postSeparationDisc_avoids_other_radialBoundary
            (k := n) hlevel hlevel le_rfl hz)
      · intro hinner
        have hn : 1 ≤ n := by
          have hne := separationLevel_ne_zero n x y
          omega
        have hregular : wordWalk start word q ∈
            disc x (scaleRadius n n) :=
          hinner.1.trans (terminalRadius_le_regularRadius_self n hn)
        exact Set.disjoint_left.mp hsep hregular hz
    rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord
        (avoid leftWord (by simpa only [D] using hleft)),
      scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord
        (avoid rightWord (by simpa only [D] using hright)), hend]

/-- Equality of the retained `x` signature through separation determines
the complete scanner transition of endpoint-matched terminal `y` bridges. -/
theorem xProfileScanCompatible_of_terminalPrefixSignature_eq
    {n splitLevel : ℕ} {x y start endpoint : Point}
    (hn : 1 ≤ n) (hseparation : splitLevel = separationLevel n x y)
    (hsplit : splitLevel ≤ n)
    (hstart : start ∈ terminalInnerBoundary n y)
    (left right : BoundaryExitWordCode
      (terminalOuterBoundary n y) start endpoint)
    (hprefix :
      PrefixXProfileScanSignature n splitLevel x start
          (List.ofFn left.1.2) =
        PrefixXProfileScanSignature n splitLevel x start
          (List.ofFn right.1.2)) :
    XProfileScanCompatible n x start
      (List.ofFn left.1.2) (List.ofFn right.1.2) := by
  rw [xProfileScanCompatible_iff_signature_eq]
  funext k seekingOuter
  by_cases hk : (k.1 : ℕ) ≤ splitLevel
  · exact congrFun (congrFun hprefix ⟨k, hk⟩) seekingOuter
  · have hlevel : separationLevel n x y ≤ n := by
      rw [← hseparation]
      exact hsplit
    have hkLower : separationLevel n x y < (k.1 : ℕ) := by
      rw [← hseparation]
      omega
    exact scanWordFrom_eq_of_postSeparation_confined_words_terminal
      hlevel hkLower (by omega) ⟨seekingOuter, 0⟩ _ _
      (by
        simpa only [hseparation] using
          terminalBridge_wordWalk_mem_separationDisc hn hsplit hstart left)
      (by
        simpa only [hseparation] using
          terminalBridge_wordWalk_mem_separationDisc hn hsplit hstart right)
      (by
        simpa only [wordWalk_length, wordEndpoint] using
          (boundaryExitWordCode_wordEndpoint left).trans
            (boundaryExitWordCode_wordEndpoint right).symm)

/-- The terminal right-only factor restricted to one retained prefix
signature at each erased bridge. -/
def leftSignatureRestrictedFactor
    {start n splitLevel : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 1 ≤ n)
    (data : Data n profileDelta)
    (entrance : Fin (coordinateCount n profileDelta) → TerminalEntrance n y)
    (exit : Fin (coordinateCount n profileDelta) → TerminalExit n y)
    (signature : Fin (coordinateCount n profileDelta) →
      PrefixXProfileScanSignatureData n splitLevel) :=
  restrictBridges (unmarkedFactor (start := start) hn data entrance exit)
    (fun j bridge ↦
      PrefixXProfileScanSignature n splitLevel x (entrance j).1
        (List.ofFn bridge.1.2) = signature j)

/-- Any two bridges in one retained signature fibre have the same complete
`x` scanner transition. -/
theorem leftSignatureRestrictedBridge_xProfileScanCompatible
    {n splitLevel : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 1 ≤ n) (hseparation : splitLevel = separationLevel n x y)
    (hsplit : splitLevel ≤ n)
    (entrance : Fin (coordinateCount n profileDelta) → TerminalEntrance n y)
    (exit : Fin (coordinateCount n profileDelta) → TerminalExit n y)
    (signature : Fin (coordinateCount n profileDelta) →
      PrefixXProfileScanSignatureData n splitLevel)
    (j : Fin (coordinateCount n profileDelta))
    (left right :
      {bridge : UnmarkedBridge profileDelta n y j (entrance j) (exit j) //
        PrefixXProfileScanSignature n splitLevel x (entrance j).1
          (List.ofFn bridge.1.2) = signature j}) :
    XProfileScanCompatible n x (entrance j).1
      (List.ofFn left.1.1.2) (List.ofFn right.1.1.2) := by
  apply xProfileScanCompatible_of_terminalPrefixSignature_eq
    hn hseparation hsplit (entrance j).2 left.1 right.1
  exact left.2.trans right.2.symm

/-- Signature restriction can only decrease each canonical terminal exit
kernel. -/
theorem leftSignatureRestrictedFactor_kernel_le
    {start n splitLevel : ℕ} {profileDelta : ℝ} {x y : Point}
    (hn : 1 ≤ n)
    (data : Data n profileDelta)
    (entrance : Fin (coordinateCount n profileDelta) → TerminalEntrance n y)
    (exit : Fin (coordinateCount n profileDelta) → TerminalExit n y)
    (signature : Fin (coordinateCount n profileDelta) →
      PrefixXProfileScanSignatureData n splitLevel)
    (j : Fin (coordinateCount n profileDelta)) :
    (leftSignatureRestrictedFactor (start := start) (x := x) hn data
        entrance exit signature).kernel j ≤
      terminalSkeletonKernel (terminalOuterBoundary n y)
        (entrance j).1 (exit j).1 := by
  exact (restrictBridges_kernel_le
    (unmarkedFactor (start := start) hn data entrance exit)
    (fun j bridge ↦
      PrefixXProfileScanSignature n splitLevel x (entrance j).1
        (List.ofFn bridge.1.2) = signature j) j).trans_eq
    (unmarkedFactor_kernel (start := start) hn data entrance exit j)

end

end Erdos1165.AsymmetricTerminalLeftSignatureRestriction

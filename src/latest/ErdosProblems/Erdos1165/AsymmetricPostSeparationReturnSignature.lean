/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPairSeparationGeometry
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionPreservation

/-!
# Automatic scanner transitions for post-separation return words

An endpoint-matched first return to the separated `y` boundary stays inside
the separated `y` disc.  Consequently its transition on every strictly
deeper `x` profile scanner is independent of the chosen return word.  This
is the pathwise cancellation used when a split-completion atom is refined by
the deeper `y` profile; no conditional-probability comparison is involved.
-/

open Set

namespace Erdos1165.AsymmetricPostSeparationReturnSignature

open AnnularProfileClocks AppendixPair
open AsymmetricPairSeparationGeometry
open AsymmetricSplitCompletionPreservation
open MarkedBridgeFactorization TerminalGlobalExitSplice
open TerminalProfileClockEquivalence ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Recursive word containment is equivalent to containment of every
finite-time vertex in the corresponding list walk.  The forward direction
is kept public because first-boundary codes naturally provide `WordWithin`,
whereas scanner geometry is stated using `wordWalk`. -/
theorem wordWalk_mem_of_wordWithin
    {D : Set Point} {start : Point} {word : List Direction}
    (hword : WordWithin D start word) :
    ∀ q ≤ word.length, wordWalk start word q ∈ D := by
  induction word generalizing start with
  | nil =>
      intro q hq
      have hq0 : q = 0 := by simpa using hq
      subst q
      simpa [wordWalk] using hword
  | cons d tail ih =>
      intro q hq
      cases q with
      | zero =>
          simpa [wordWalk] using hword.1
      | succ q =>
          have hqTail : q ≤ tail.length := by
            simpa using hq
          simpa [wordWalk] using ih hword.2 q hqTail

/-- Two canonical first returns to the separated `y` boundary have the same
transition on every strictly post-separation regular scanner about `x`.
The split scanner itself is deliberately excluded. -/
theorem scanWordFrom_eq_of_postSeparation_boundaryExitWordCodes
    {n k : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y < k) (hkUpper : k ≤ n)
    (hstart : start ∈
      disc y (scaleRadius n (separationLevel n x y)))
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n (separationLevel n x y) y) start endpoint)
    (state : BoundaryScanState) :
    scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state (List.ofFn left.1.2) =
      scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state
        (List.ofFn right.1.2) := by
  let D := disc y (scaleRadius n (separationLevel n x y))
  have hleftWithin : WordWithin D start (List.ofFn left.1.2) := by
    simpa only [D, profileInnerBoundary, discBoundary] using
      (boundaryExitWordCode_wordWithin_and_endpoint hstart left).1
  have hrightWithin : WordWithin D start (List.ofFn right.1.2) := by
    simpa only [D, profileInnerBoundary, discBoundary] using
      (boundaryExitWordCode_wordWithin_and_endpoint hstart right).1
  apply scanWordFrom_eq_of_postSeparation_confined_words
    hlevel hkLower hkUpper state
  · exact wordWalk_mem_of_wordWithin hleftWithin
  · exact wordWalk_mem_of_wordWithin hrightWithin
  · simpa only [wordWalk_length, wordEndpoint] using
      (boundaryExitWordCode_wordEndpoint left).trans
        (boundaryExitWordCode_wordEndpoint right).symm

/-- The same automatic transition statement including the terminal scanner
`k = n + 1`.  At that last coordinate the outer boundary is the regular
level-`n` boundary, while the terminal inner disc is contained in the
regular level-`n` disc. -/
theorem scanWordFrom_eq_of_postSeparation_boundaryExitWordCodes_terminal
    {n k : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y < k) (hkUpper : k ≤ n + 1)
    (hstart : start ∈
      disc y (scaleRadius n (separationLevel n x y)))
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n (separationLevel n x y) y) start endpoint)
    (state : BoundaryScanState) :
    scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state (List.ofFn left.1.2) =
      scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state
        (List.ofFn right.1.2) := by
  have hn : 1 ≤ n := by
    have hne := separationLevel_ne_zero n x y
    omega
  by_cases hkn : k ≤ n
  · exact scanWordFrom_eq_of_postSeparation_boundaryExitWordCodes
      hlevel hkLower hkn hstart left right state
  · have hk : k = n + 1 := by omega
    subst k
    let D := disc y (scaleRadius n (separationLevel n x y))
    have hleftWithin : WordWithin D start (List.ofFn left.1.2) := by
      simpa only [D, profileInnerBoundary, discBoundary] using
        (boundaryExitWordCode_wordWithin_and_endpoint hstart left).1
    have hrightWithin : WordWithin D start (List.ofFn right.1.2) := by
      simpa only [D, profileInnerBoundary, discBoundary] using
        (boundaryExitWordCode_wordWithin_and_endpoint hstart right).1
    have hsep : Disjoint (disc x (scaleRadius n n)) D := by
      simpa only [D] using
        (regularDisc_disjoint_postSeparationDisc hlevel hlevel le_rfl)
    have avoid (word : List Direction)
        (hword : WordWithin D start word) :
        ∀ q, 0 < q → q ≤ word.length →
          wordWalk start word q ∉ profileOuterBoundary n (n + 1) x ∧
          wordWalk start word q ∉ profileInnerBoundary n (n + 1) x := by
      intro q _hqpos hq
      have hz : wordWalk start word q ∈ D :=
        wordWalk_mem_of_wordWithin hword q hq
      constructor
      · simpa only [profileOuterBoundary, Nat.add_sub_cancel] using
          (postSeparationDisc_avoids_other_radialBoundary
            (k := n) hlevel hlevel le_rfl hz)
      · intro hinner
        have hregular : wordWalk start word q ∈ disc x (scaleRadius n n) :=
          hinner.1.trans
            (terminalRadius_le_regularRadius_self n hn)
        exact Set.disjoint_left.mp hsep hregular hz
    rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state
        (List.ofFn left.1.2) (avoid _ hleftWithin),
      scanWordFrom_eq_of_wordWalk_avoids _ _ start state
        (List.ofFn right.1.2) (avoid _ hrightWithin)]
    have hend := (boundaryExitWordCode_wordEndpoint left).trans
      (boundaryExitWordCode_wordEndpoint right).symm
    simpa only [wordWalk_length, wordEndpoint] using
      congrArg (fun z ↦ (z, state)) hend

/-- Word-level form of the post-separation cancellation, including the
terminal scanner.  Unlike the boundary-code wrapper above, the two words may
start and end on any deeper `y` boundary; confinement in the separation disc
is the only geometric input. -/
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
    have hn : 1 ≤ n := by
      have hne := separationLevel_ne_zero n x y
      omega
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
        have hregular : wordWalk start word q ∈ disc x (scaleRadius n n) :=
          hinner.1.trans
            (terminalRadius_le_regularRadius_self n hn)
        exact Set.disjoint_left.mp hsep hregular hz
    rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord
        (avoid leftWord (by simpa only [D] using hleft)),
      scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord
        (avoid rightWord (by simpa only [D] using hright))]
    simpa only [wordWalk_length] using congrArg (fun z ↦ (z, state)) hend

/-- Signature-coordinate form of the preceding cancellation. -/
theorem xProfileScanSignature_eq_at_strictPostSeparation
    {n : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n (separationLevel n x y) y) start endpoint)
    (hstart : start ∈
      disc y (scaleRadius n (separationLevel n x y)))
    (k : {k : Fin (n + 2) // (k : ℕ) ≠ 0})
    (hkLower : separationLevel n x y < (k.1 : ℕ))
    (hkUpper : (k.1 : ℕ) ≤ n) (seekingOuter : Bool) :
    XProfileScanSignature n x start (List.ofFn left.1.2) k seekingOuter =
      XProfileScanSignature n x start (List.ofFn right.1.2) k seekingOuter := by
  exact scanWordFrom_eq_of_postSeparation_boundaryExitWordCodes
    hlevel hkLower hkUpper hstart left right ⟨seekingOuter, 0⟩

/-- All signature coordinates strictly above separation, including the
terminal coordinate, are automatic for endpoint-matched first returns. -/
theorem xProfileScanSignature_eq_at_strictPostSeparation_terminal
    {n : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n (separationLevel n x y) y) start endpoint)
    (hstart : start ∈
      disc y (scaleRadius n (separationLevel n x y)))
    (k : {k : Fin (n + 2) // (k : ℕ) ≠ 0})
    (hkLower : separationLevel n x y < (k.1 : ℕ))
    (seekingOuter : Bool) :
    XProfileScanSignature n x start (List.ofFn left.1.2) k seekingOuter =
      XProfileScanSignature n x start (List.ofFn right.1.2) k seekingOuter := by
  apply scanWordFrom_eq_of_postSeparation_boundaryExitWordCodes_terminal
    hlevel hkLower (by omega) hstart left right ⟨seekingOuter, 0⟩

end

end Erdos1165.AsymmetricPostSeparationReturnSignature

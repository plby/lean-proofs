/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.BufferedSuccessfulProfile
import ErdosProblems.Erdos1165.AsymmetricPostSeparationReturnSignature

/-!
# Buffered left-profile preservation under an asymmetric splice

Words erased from the right-hand separated disc cannot affect left-profile
scanners at least three scales before separation or at/after the padded cut.
This file composes that coordinatewise fact through an arbitrary retained
alternating skeleton.
-/

open Set

namespace Erdos1165.AsymmetricBufferedProfileSplice

open AnnularProfileClocks AppendixPair
open AsymmetricPairSeparationGeometry
open AsymmetricPostSeparationReturnSignature
open BufferedSuccessfulProfile
open TerminalGlobalExitSplice TerminalProfileClockEquivalence
open TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The low buffered and high post-separation scanner identities, combined
for the retained-coordinate predicate used by the padded splice. -/
theorem scanWordFrom_eq_of_bufferedSeparation_confined_words_terminal
    {n l p k : ℕ} {x y start : Point}
    (hn : 1 ≤ n)
    (hseparation : l = separationLevel n x y)
    (hlevel : l ≤ n) (hlower : 3 ≤ l) (hlp : l < p)
    (hretained : RetainedCoordinate (l - 3) p k)
    (state : BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleft : ∀ q ≤ leftWord.length,
      wordWalk start leftWord q ∈ disc y (scaleRadius n l))
    (hright : ∀ q ≤ rightWord.length,
      wordWalk start rightWord q ∈ disc y (scaleRadius n l))
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length)
    (hkUpper : k ≤ n + 1) :
    scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state leftWord =
      scanWordFrom (profileOuterBoundary n k x)
        (profileInnerBoundary n k x) start state rightWord := by
  rcases hretained with hlow | hhigh
  · apply scanWordFrom_eq_of_preSeparation_buffered_confined_words
      hn (by simpa only [hseparation] using hlevel)
      (by simpa only [hseparation] using hlower)
      (by simpa only [← hseparation] using hlow) state
    · simpa only [hseparation] using hleft
    · simpa only [hseparation] using hright
    · exact hend
  · apply scanWordFrom_eq_of_postSeparation_confined_words_terminal
      (by simpa only [hseparation] using hlevel)
      (by omega) hkUpper state
    · simpa only [hseparation] using hleft
    · simpa only [hseparation] using hright
    · exact hend

/-- Coordinatewise scanner compatibility composes through the common
retained pieces and identifies every retained excursion-profile entry. -/
theorem excursionProfile_alternatingConcat_eq_on_retained
    {n m low high : ℕ} (hn : 2 ≤ n) {x start : Point}
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hcompatible : ∀ j (k : Fin (n + 2)), (k : ℕ) ≠ 0 →
      RetainedCoordinate low high k.1 → ∀ state : BoundaryScanState,
        scanWordFrom (profileOuterBoundary n (k : ℕ) x)
            (profileInnerBoundary n (k : ℕ) x) (geometry.wordStart j)
            state (sourceWords j) =
          scanWordFrom (profileOuterBoundary n (k : ℕ) x)
            (profileInnerBoundary n (k : ℕ) x) (geometry.wordStart j)
            state (candidateWords j)) :
    ∀ k : Fin (n + 2), RetainedCoordinate low high k.1 →
      excursionProfile
          (wordWalk start (alternatingConcat m pieces sourceWords)) n
          (alternatingConcat m pieces sourceWords).length x k =
        excursionProfile
          (wordWalk start (alternatingConcat m pieces candidateWords)) n
          (alternatingConcat m pieces candidateWords).length x k := by
  classical
  intro k hkRetained
  unfold excursionProfile
  split_ifs with hk
  · rfl
  · apply completedExcursionCount_wordWalk_eq_of_scanWordFrom_eq
      (profileBoundaries_disjoint hn x k hk)
    change scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start
        (visitBoundary
          (profileOuterBoundary n (k : ℕ) x)
          (profileInnerBoundary n (k : ℕ) x)
          TerminalBoundaryScan.initialState start)
        (alternatingConcat m pieces sourceWords) = _
    apply scanWordFrom_alternatingConcat_eq_of_endpointGeometry
      m _ _ pieces sourceWords candidateWords start _ geometry
    intro j state
    exact hcompatible j k hk hkRetained state

/-- Specialization to words confined to the separated right-hand disc.
Only the interval `l-2,...,p-1` of the left profile may change. -/
theorem excursionProfile_alternatingConcat_eq_outside_buffer
    {n m l p : ℕ} (hn : 2 ≤ n) {x y start : Point}
    (hseparation : l = separationLevel n x y)
    (hlevel : l ≤ n) (hlower : 3 ≤ l) (hlp : l < p)
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hsource : ∀ j q, q ≤ (sourceWords j).length →
      wordWalk (geometry.wordStart j) (sourceWords j) q ∈
        disc y (scaleRadius n l))
    (hcandidate : ∀ j q, q ≤ (candidateWords j).length →
      wordWalk (geometry.wordStart j) (candidateWords j) q ∈
        disc y (scaleRadius n l)) :
    ∀ k : Fin (n + 2), RetainedCoordinate (l - 3) p k.1 →
      excursionProfile
          (wordWalk start (alternatingConcat m pieces sourceWords)) n
          (alternatingConcat m pieces sourceWords).length x k =
        excursionProfile
          (wordWalk start (alternatingConcat m pieces candidateWords)) n
          (alternatingConcat m pieces candidateWords).length x k := by
  apply excursionProfile_alternatingConcat_eq_on_retained hn geometry
  intro j k hk hretained state
  apply scanWordFrom_eq_of_bufferedSeparation_confined_words_terminal
    (Nat.one_le_of_lt hn) hseparation hlevel hlower hlp hretained state
  · exact hsource j
  · exact hcandidate j
  · rw [wordWalk_length, wordWalk_length,
      geometry.leftWordEndpoint, geometry.rightWordEndpoint]
  · omega

/-- Sharp form used by the retained completion: although the words are cut
at a much deeper padded scale, confinement to the separation disc already
preserves every scanner strictly above `l`.  Thus precisely the three
coordinates `l-2,l-1,l` may change. -/
theorem excursionProfile_alternatingConcat_eq_outside_three_coordinate_buffer
    {n m l : ℕ} (hn : 2 ≤ n) {x y start : Point}
    (hseparation : l = separationLevel n x y)
    (hlevel : l ≤ n) (hlower : 3 ≤ l)
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hsource : ∀ j q, q ≤ (sourceWords j).length →
      wordWalk (geometry.wordStart j) (sourceWords j) q ∈
        disc y (scaleRadius n l))
    (hcandidate : ∀ j q, q ≤ (candidateWords j).length →
      wordWalk (geometry.wordStart j) (candidateWords j) q ∈
        disc y (scaleRadius n l)) :
    ∀ k : Fin (n + 2), RetainedCoordinate (l - 3) (l + 1) k.1 →
      excursionProfile
          (wordWalk start (alternatingConcat m pieces sourceWords)) n
          (alternatingConcat m pieces sourceWords).length x k =
        excursionProfile
          (wordWalk start (alternatingConcat m pieces candidateWords)) n
          (alternatingConcat m pieces candidateWords).length x k := by
  exact excursionProfile_alternatingConcat_eq_outside_buffer hn hseparation
    hlevel hlower (by omega) geometry hsource hcandidate

/-- With the sharper two-scale geometric margin, only the two coordinates
`l-1,l` can change.  This form is used at `l = 3` to retain coordinate one. -/
theorem excursionProfile_alternatingConcat_eq_outside_two_coordinate_buffer
    {n m l : ℕ} (hn : 2 ≤ n) {x y start : Point}
    (hseparation : l = separationLevel n x y)
    (hlevel : l ≤ n) (hlower : 3 ≤ l)
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hsource : ∀ j q, q ≤ (sourceWords j).length →
      wordWalk (geometry.wordStart j) (sourceWords j) q ∈
        disc y (scaleRadius n l))
    (hcandidate : ∀ j q, q ≤ (candidateWords j).length →
      wordWalk (geometry.wordStart j) (candidateWords j) q ∈
        disc y (scaleRadius n l)) :
    ∀ k : Fin (n + 2), RetainedCoordinate (l - 2) (l + 1) k.1 →
      excursionProfile
          (wordWalk start (alternatingConcat m pieces sourceWords)) n
          (alternatingConcat m pieces sourceWords).length x k =
        excursionProfile
          (wordWalk start (alternatingConcat m pieces candidateWords)) n
          (alternatingConcat m pieces candidateWords).length x k := by
  apply excursionProfile_alternatingConcat_eq_on_retained hn geometry
  intro j k hk hretained state
  rcases hretained with hlow | hhigh
  · apply scanWordFrom_eq_of_preSeparation_twoStep_confined_words
      (x := x) (y := y) hn (by simpa only [← hseparation] using hlevel)
      (by simpa only [← hseparation] using hlower)
      (by simpa only [← hseparation] using hlow) state
    · simpa only [hseparation] using hsource j
    · simpa only [hseparation] using hcandidate j
    · rw [wordWalk_length, wordWalk_length,
        geometry.leftWordEndpoint, geometry.rightWordEndpoint]
  · apply scanWordFrom_eq_of_postSeparation_confined_words_terminal
      (x := x) (y := y) (by simpa only [← hseparation] using hlevel)
      (by omega) (by omega) state
    · simpa only [hseparation] using hsource j
    · simpa only [hseparation] using hcandidate j
    · rw [wordWalk_length, wordWalk_length,
        geometry.leftWordEndpoint, geometry.rightWordEndpoint]

/-- Uniform form of the three-coordinate buffer.  At separation levels below
three the low retained block is empty (apart from coordinate zero, which is
not scanned), so the post-separation confinement theorem supplies the whole
claim. -/
theorem excursionProfile_alternatingConcat_eq_outside_three_coordinate_buffer_all
    {n m l : ℕ} (hn : 2 ≤ n) {x y start : Point}
    (hseparation : l = separationLevel n x y)
    (hlevel : l ≤ n)
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hsource : ∀ j q, q ≤ (sourceWords j).length →
      wordWalk (geometry.wordStart j) (sourceWords j) q ∈
        disc y (scaleRadius n l))
    (hcandidate : ∀ j q, q ≤ (candidateWords j).length →
      wordWalk (geometry.wordStart j) (candidateWords j) q ∈
        disc y (scaleRadius n l)) :
    ∀ k : Fin (n + 2), RetainedCoordinate (l - 3) (l + 1) k.1 →
      excursionProfile
          (wordWalk start (alternatingConcat m pieces sourceWords)) n
          (alternatingConcat m pieces sourceWords).length x k =
        excursionProfile
          (wordWalk start (alternatingConcat m pieces candidateWords)) n
          (alternatingConcat m pieces candidateWords).length x k := by
  by_cases hlower : 3 ≤ l
  · exact excursionProfile_alternatingConcat_eq_outside_three_coordinate_buffer
      hn hseparation hlevel hlower geometry hsource hcandidate
  · apply excursionProfile_alternatingConcat_eq_on_retained hn geometry
    intro j k hk hretained state
    rcases hretained with hlow | hhigh
    · have : k.1 = 0 := by omega
      exact (hk this).elim
    · apply scanWordFrom_eq_of_postSeparation_confined_words_terminal
        (by simpa only [hseparation] using hlevel)
        (by omega) (by omega) state
      · simpa only [hseparation] using hsource j
      · simpa only [hseparation] using hcandidate j
      · rw [wordWalk_length, wordWalk_length,
          geometry.leftWordEndpoint, geometry.rightWordEndpoint]

end

end Erdos1165.AsymmetricBufferedProfileSplice

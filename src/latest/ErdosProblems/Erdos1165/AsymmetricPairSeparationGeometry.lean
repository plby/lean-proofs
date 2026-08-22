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

import ErdosProblems.Erdos1165.SharedPrefixPairClockAlignment
import ErdosProblems.Erdos1165.TerminalProfileClockEquivalence
import ErdosProblems.Erdos1165.PoissonKernelGreenPole

/-!
# Geometry for the asymmetric post-separation pair splice

After the first separation level `l`, every regular disc of either centre at
a level `k ≥ l` is contained in its level-`l` disc.  Hence a path segment
confined to the `y` level-`l` disc cannot touch any post-separation radial
boundary about `x`.  This is the geometric half of the source-correct A.16
asymmetric splice; temporal extraction of the confined `y` radial tail is a
separate clock statement.
-/

open Set

namespace Erdos1165.AsymmetricPairSeparationGeometry

open AppendixPair
open AnnularProfileClocks TerminalGlobalExitSplice
open TerminalProfileClockEquivalence TerminalSpliceProfileGeometry ThickPoint
open PoissonKernelGreenPole

noncomputable section

attribute [local instance] Classical.propDecidable

/-- At every regular level after the first separation, the `x` disc is
disjoint from the level-`l` disc about `y`. -/
theorem regularDisc_disjoint_postSeparationDisc
    {n k : ℕ} {x y : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y ≤ k) (hkUpper : k ≤ n) :
    Disjoint (disc x (scaleRadius n k))
      (disc y (scaleRadius n (separationLevel n x y))) := by
  have hnonempty : (separatingIndices n x y).Nonempty := by
    by_contra hempty
    have hsentinel : separationLevel n x y = n + 2 :=
      separationLevel_eq_sentinel_iff.mpr hempty
    omega
  have hseparated := separationLevel_isSeparated hnonempty
  have hradius : scaleRadius n k ≤
      scaleRadius n (separationLevel n x y) :=
    scaleRadius_antitone_of_le hkLower hkUpper
  exact hseparated.mono (fun _ hz ↦ hz.trans hradius) (fun _ hz ↦ hz)

/-- Consequently the confined `y` tail avoids every `x` radial boundary at
a regular level at or after separation. -/
theorem postSeparationDisc_avoids_other_radialBoundary
    {n k : ℕ} {x y z : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y ≤ k) (hkUpper : k ≤ n)
    (hz : z ∈ disc y (scaleRadius n (separationLevel n x y))) :
    z ∉ discBoundary x (scaleRadius n k) := by
  intro hboundary
  exact Set.disjoint_left.mp
    (regularDisc_disjoint_postSeparationDisc hlevel hkLower hkUpper)
      hboundary.1 hz

/-- The same statement with the two centres interchanged. -/
theorem postSeparationDisc_avoids_other_radialBoundary_comm
    {n k : ℕ} {x y z : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y ≤ k) (hkUpper : k ≤ n)
    (hz : z ∈ disc x (scaleRadius n (separationLevel n x y))) :
    z ∉ discBoundary y (scaleRadius n k) := by
  have hcomm : separationLevel n y x = separationLevel n x y :=
    separationLevel_comm n y x
  apply postSeparationDisc_avoids_other_radialBoundary
    (x := y) (y := x) (z := z)
  · simpa [hcomm] using hlevel
  · simpa [hcomm] using hkLower
  · exact hkUpper
  · simpa [hcomm] using hz

/-! ## The buffered low side of the separation scale -/

lemma regularRadius_pred_eq_exp_mul
    {n l : ℕ} (hl : 1 ≤ l) :
    regularRadius n (l - 1) = Real.exp 1 * regularRadius n l := by
  unfold regularRadius
  have hexponent : (n : ℝ) - (l - 1 : ℕ) =
      1 + ((n : ℝ) - (l : ℝ)) := by
    push_cast [Nat.cast_sub hl]
    ring
  rw [hexponent, Real.exp_add]
  ring

lemma regularRadius_sub_three_eq_exp_mul
    {n l : ℕ} (hl : 3 ≤ l) :
    regularRadius n (l - 3) = Real.exp 3 * regularRadius n l := by
  unfold regularRadius
  have hexponent : (n : ℝ) - (l - 3 : ℕ) =
      3 + ((n : ℝ) - (l : ℝ)) := by
    push_cast [Nat.cast_sub hl]
    ring
  rw [hexponent, Real.exp_add]
  ring

lemma regularRadius_sub_two_eq_exp_sq_mul
    {n l : ℕ} (hl : 2 ≤ l) :
    regularRadius n (l - 2) = (Real.exp 1) ^ 2 * regularRadius n l := by
  unfold regularRadius
  have hexponent : (n : ℝ) - (l - 2 : ℕ) =
      1 + 1 + ((n : ℝ) - (l : ℝ)) := by
    push_cast [Nat.cast_sub hl]
    ring
  rw [hexponent, Real.exp_add, Real.exp_add]
  ring

lemma two_exp_one_add_two_le_exp_three :
    2 * Real.exp 1 + 2 ≤ Real.exp 3 := by
  rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
    Real.exp_add, Real.exp_add]
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have he0 : 0 ≤ Real.exp 1 := Real.exp_nonneg _
  nlinarith [mul_nonneg he0 (sq_nonneg (Real.exp 1 - 2))]

lemma one_le_regularRadius_of_le
    {n l : ℕ} (hn : 1 ≤ n) (hln : l ≤ n) :
    1 ≤ regularRadius n l := by
  unfold regularRadius
  have hdiff : (0 : ℝ) ≤ (n : ℝ) - (l : ℝ) := by
    have hcast : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
    linarith
  have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - (l : ℝ)) :=
    Real.one_le_exp hdiff
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 9 :=
    one_le_pow₀ (by exact_mod_cast hn)
  nlinarith [mul_le_mul_of_nonneg_left hexp
    (by positivity : 0 ≤ (n : ℝ) ^ 9)]

lemma two_le_regularRadius_of_le
    {n l : ℕ} (hn : 2 ≤ n) (hln : l ≤ n) :
    2 ≤ regularRadius n l := by
  unfold regularRadius
  have hdiff : (0 : ℝ) ≤ (n : ℝ) - (l : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hln)
  have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - (l : ℝ)) :=
    Real.one_le_exp hdiff
  have hpowNat : 2 ≤ n ^ 9 := by
    calc
      2 ≤ 2 ^ 9 := by norm_num
      _ ≤ n ^ 9 := Nat.pow_le_pow_left hn 9
  have hpow : (2 : ℝ) ≤ (n : ℝ) ^ 9 := by
    exact_mod_cast hpowNat
  nlinarith [mul_le_mul_of_nonneg_left hexp
    (by positivity : 0 ≤ (n : ℝ) ^ 9)]

lemma two_exp_one_add_three_halves_le_exp_one_sq :
    2 * Real.exp 1 + (3 / 2 : ℝ) ≤ (Real.exp 1) ^ 2 := by
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hfactor : 0 ≤
      (Real.exp 1 - 27 / 10) * (Real.exp 1 + 27 / 10 - 2) := by
    exact mul_nonneg (sub_nonneg.mpr he) (by linarith)
  nlinarith

/-- Two scales already suffice to place the separated disc strictly inside
the earlier disc.  This sharper estimate is only needed at separation level
three, where it preserves the forced first profile coordinate. -/
lemma scaleRadius_two_step_dominates_add_one
    {n l : ℕ} (hn : 2 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n) :
    2 * scaleRadius n (l - 1) + scaleRadius n l + 1 ≤
      scaleRadius n (l - 2) := by
  rw [scaleRadius_of_le hln,
    scaleRadius_of_le (by omega : l - 1 ≤ n),
    scaleRadius_of_le (by omega : l - 2 ≤ n),
    regularRadius_pred_eq_exp_mul (by omega : 1 ≤ l),
    regularRadius_sub_two_eq_exp_sq_mul hl]
  have hr : 0 ≤ regularRadius n l := by
    unfold regularRadius
    positivity
  have hr2 : 2 ≤ regularRadius n l :=
    two_le_regularRadius_of_le hn hln
  have hconstant := mul_le_mul_of_nonneg_right
    two_exp_one_add_three_halves_le_exp_one_sq hr
  nlinarith

/-- The three-scale buffer absorbs two previous-scale radii, the current
radius, and a full nearest-neighbor step. -/
lemma scaleRadius_three_step_dominates_add_one
    {n l : ℕ} (hn : 1 ≤ n) (hl : 3 ≤ l) (hln : l ≤ n) :
    2 * scaleRadius n (l - 1) + scaleRadius n l + 1 ≤
      scaleRadius n (l - 3) := by
  rw [scaleRadius_of_le hln,
    scaleRadius_of_le (by omega : l - 1 ≤ n),
    scaleRadius_of_le (by omega : l - 3 ≤ n),
    regularRadius_pred_eq_exp_mul (by omega : 1 ≤ l),
    regularRadius_sub_three_eq_exp_mul hl]
  have hr : 0 ≤ regularRadius n l := by
    unfold regularRadius
    positivity
  have hr1 : 1 ≤ regularRadius n l :=
    one_le_regularRadius_of_le hn hln
  nlinarith [mul_le_mul_of_nonneg_right
    two_exp_one_add_two_le_exp_three hr]

lemma latticeDistance_comm (x y : Point) :
    latticeDistance x y = latticeDistance y x := by
  unfold latticeDistance squaredDistance
  congr 1
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  norm_num
  ring

lemma latticeDistance_triangle (x y z : Point) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  have h := euclideanRadius_sub_le_add (z - y) (x - y)
  calc
    latticeDistance x z =
        PotentialEuclideanGeometry.euclideanRadius (z - x) :=
      latticeDistance_eq_euclideanRadius_sub x z
    _ ≤ PotentialEuclideanGeometry.euclideanRadius (z - y) +
        PotentialEuclideanGeometry.euclideanRadius (x - y) := by
      simpa [sub_sub] using h
    _ = latticeDistance y z + latticeDistance y x := by
      rw [latticeDistance_eq_euclideanRadius_sub,
        latticeDistance_eq_euclideanRadius_sub]
    _ = latticeDistance x y + latticeDistance y z := by
      rw [latticeDistance_comm y x]
      ring

/-- Failure of separation at the preceding scale bounds the distance between
the two centres by twice that preceding radius. -/
lemma separationCenters_distance_le_two_previous
    {n : ℕ} {x y : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 2 ≤ separationLevel n x y) :
    latticeDistance x y ≤
      2 * scaleRadius n (separationLevel n x y - 1) := by
  have hnonempty : (separatingIndices n x y).Nonempty := by
    by_contra hempty
    have hsentinel : separationLevel n x y = n + 2 :=
      separationLevel_eq_sentinel_iff.mpr hempty
    omega
  have hnot := separationLevel_not_separated_before hnonempty
    (k := separationLevel n x y - 1)
    (by
      unfold scaleIndices
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    (by omega)
  rw [SeparatedAt, Set.not_disjoint_iff] at hnot
  obtain ⟨z, hzx, hzy⟩ := hnot
  have htri := latticeDistance_triangle x z y
  change latticeDistance x z ≤
    scaleRadius n (separationLevel n x y - 1) at hzx
  change latticeDistance y z ≤
    scaleRadius n (separationLevel n x y - 1) at hzy
  rw [latticeDistance_comm z y] at htri
  linarith

/-- The separated `y` disc lies at least one lattice step inside the `x`
disc three scales earlier.  This is the exact buffered containment used in
the erased-gap asymmetric splice. -/
lemma lowSeparationDisc_distance_add_one_le
    {n : ℕ} {x y z : Point}
    (hn : 1 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hz : z ∈ disc y (scaleRadius n (separationLevel n x y))) :
    latticeDistance x z + 1 ≤
      scaleRadius n (separationLevel n x y - 3) := by
  have hcenters := separationCenters_distance_le_two_previous
    hlevel (by omega : 2 ≤ separationLevel n x y)
  have htri := latticeDistance_triangle x y z
  have hscale := scaleRadius_three_step_dominates_add_one hn hlower hlevel
  change latticeDistance y z ≤
    scaleRadius n (separationLevel n x y) at hz
  linarith

/-- The separated disc is already one lattice step inside the disc two
scales earlier.  The extra `n ≥ 2` supplies the tiny additive lattice
margin which is not available from the scale ratio alone. -/
lemma twoStepLowSeparationDisc_distance_add_one_le
    {n : ℕ} {x y z : Point}
    (hn : 2 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hz : z ∈ disc y (scaleRadius n (separationLevel n x y))) :
    latticeDistance x z + 1 ≤
      scaleRadius n (separationLevel n x y - 2) := by
  have hcenters := separationCenters_distance_le_two_previous
    hlevel (by omega : 2 ≤ separationLevel n x y)
  have htri := latticeDistance_triangle x y z
  have hscale := scaleRadius_two_step_dominates_add_one hn
    (by omega : 2 ≤ separationLevel n x y) hlevel
  change latticeDistance y z ≤
    scaleRadius n (separationLevel n x y) at hz
  linarith

/-- Consequently a confined replacement cannot touch any radial boundary
two or more scales before separation. -/
theorem twoStepLowSeparationDisc_avoids_other_radialBoundary
    {n k : ℕ} {x y z : Point}
    (hn : 2 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hk : k ≤ separationLevel n x y - 2)
    (hz : z ∈ disc y (scaleRadius n (separationLevel n x y))) :
    z ∉ discBoundary x (scaleRadius n k) := by
  apply not_mem_discBoundary_of_mem_disc_of_add_one_le
    (r := latticeDistance x z)
  · change latticeDistance x z ≤ latticeDistance x z
    exact le_rfl
  · exact (twoStepLowSeparationDisc_distance_add_one_le
      hn hlevel hlower hz).trans
        (scaleRadius_antitone_of_le hk (by omega))

/-- A word confined to the separated `y` disc avoids every `x` radial
boundary at least three scales before separation. -/
theorem lowSeparationDisc_avoids_other_radialBoundary
    {n k : ℕ} {x y z : Point}
    (hn : 1 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hk : k ≤ separationLevel n x y - 3)
    (hz : z ∈ disc y (scaleRadius n (separationLevel n x y))) :
    z ∉ discBoundary x (scaleRadius n k) := by
  apply not_mem_discBoundary_of_mem_disc_of_add_one_le
    (r := latticeDistance x z)
  · change latticeDistance x z ≤ latticeDistance x z
    exact le_rfl
  · exact (lowSeparationDisc_distance_add_one_le hn hlevel hlower hz).trans
      (scaleRadius_antitone_of_le hk (by omega))

/-- Two endpoint-matched words confined to the separated `y` disc have the
same effect on every `x` profile scanner at least three scales before
separation.  Together with the post-separation theorem below, this shows that
only the buffered gap can depend on the erased `y` continuation. -/
theorem scanWordFrom_eq_of_preSeparation_buffered_confined_words
    {n k : ℕ} {x y start : Point}
    (hn : 1 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hkUpper : k ≤ separationLevel n x y - 3)
    (state : TerminalProfileClockEquivalence.BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleft : ∀ q ≤ leftWord.length,
      wordWalk start leftWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hright : ∀ q ≤ rightWord.length,
      wordWalk start rightWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state leftWord =
      scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state rightWord := by
  have avoid (word : List Direction)
      (hword : ∀ q ≤ word.length,
        wordWalk start word q ∈
          disc y (scaleRadius n (separationLevel n x y))) :
      ∀ q, 0 < q → q ≤ word.length →
        wordWalk start word q ∉ profileOuterBoundary n k x ∧
        wordWalk start word q ∉ profileInnerBoundary n k x := by
    intro q _hqpos hq
    have hz := hword q hq
    constructor
    · simpa only [profileOuterBoundary] using
        (lowSeparationDisc_avoids_other_radialBoundary
          (k := k - 1) hn hlevel hlower (by omega) hz)
    · simpa only [profileInnerBoundary] using
        (lowSeparationDisc_avoids_other_radialBoundary
          (k := k) hn hlevel hlower hkUpper hz)
  rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord
      (avoid leftWord hleft),
    scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord
      (avoid rightWord hright), hend]

/-- Sharper two-scale version used to preserve coordinate one when the
separation level is three. -/
theorem scanWordFrom_eq_of_preSeparation_twoStep_confined_words
    {n k : ℕ} {x y start : Point}
    (hn : 2 ≤ n)
    (hlevel : separationLevel n x y ≤ n)
    (hlower : 3 ≤ separationLevel n x y)
    (hkUpper : k ≤ separationLevel n x y - 2)
    (state : TerminalProfileClockEquivalence.BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleft : ∀ q ≤ leftWord.length,
      wordWalk start leftWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hright : ∀ q ≤ rightWord.length,
      wordWalk start rightWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state leftWord =
      scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state rightWord := by
  have avoid (word : List Direction)
      (hword : ∀ q ≤ word.length,
        wordWalk start word q ∈
          disc y (scaleRadius n (separationLevel n x y))) :
      ∀ q, 0 < q → q ≤ word.length →
        wordWalk start word q ∉ profileOuterBoundary n k x ∧
        wordWalk start word q ∉ profileInnerBoundary n k x := by
    intro q _hqpos hq
    have hz := hword q hq
    constructor
    · simpa only [profileOuterBoundary] using
        (twoStepLowSeparationDisc_avoids_other_radialBoundary
          (k := k - 1) hn hlevel hlower (by omega) hz)
    · simpa only [profileInnerBoundary] using
        (twoStepLowSeparationDisc_avoids_other_radialBoundary
          (k := k) hn hlevel hlower hkUpper hz)
  rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord
      (avoid leftWord hleft),
    scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord
      (avoid rightWord hright), hend]

/-- A terminal replacement at `y` is in particular confined to the
post-separation disc, so it cannot create an `x` boundary hit at any regular
post-separation level. -/
theorem terminalDisc_avoids_other_postSeparation_radialBoundary
    {n k : ℕ} {x y z : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y ≤ k) (hkUpper : k ≤ n)
    (hz : z ∈ disc y (scaleRadius n n)) :
    z ∉ discBoundary x (scaleRadius n k) := by
  apply postSeparationDisc_avoids_other_radialBoundary
    hlevel hkLower hkUpper
  exact hz.trans (scaleRadius_antitone_of_le hlevel le_rfl)

/-- Two replacement words confined to the separated `y` disc have the same
effect on every strictly post-separation `x` profile scanner, provided they
have the same endpoint.  Strictness is essential: the outer boundary used by
the scanner at level `k` is the radial boundary `k-1`. -/
theorem scanWordFrom_eq_of_postSeparation_confined_words
    {n k : ℕ} {x y start : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hkLower : separationLevel n x y < k) (hkUpper : k ≤ n)
    (state : TerminalProfileClockEquivalence.BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleft : ∀ q ≤ leftWord.length,
      wordWalk start leftWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hright : ∀ q ≤ rightWord.length,
      wordWalk start rightWord q ∈
        disc y (scaleRadius n (separationLevel n x y)))
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state leftWord =
      scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state rightWord := by
  have avoid (word : List Direction)
      (hword : ∀ q ≤ word.length,
        wordWalk start word q ∈
          disc y (scaleRadius n (separationLevel n x y))) :
      ∀ q, 0 < q → q ≤ word.length →
        wordWalk start word q ∉ profileOuterBoundary n k x ∧
        wordWalk start word q ∉ profileInnerBoundary n k x := by
    intro q _hqpos hq
    have hz := hword q hq
    constructor
    · simpa only [profileOuterBoundary] using
        (postSeparationDisc_avoids_other_radialBoundary
          (k := k - 1) hlevel (by omega) (by omega) hz)
    · simpa only [profileInnerBoundary] using
        (postSeparationDisc_avoids_other_radialBoundary
          (k := k) hlevel hkLower.le hkUpper hz)
  rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord
      (avoid leftWord hleft),
    scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord
      (avoid rightWord hright), hend]

end

end Erdos1165.AsymmetricPairSeparationGeometry

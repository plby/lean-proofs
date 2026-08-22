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

import ErdosProblems.Erdos1165.AnnularProfileClocks
import ErdosProblems.Erdos1165.RadialHarnackSpecialization
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice

/-!
# Terminal splice words are invisible to coarser profile boundaries

A replacement terminal word starts on the radius `r_{n,n+1}` boundary and
first hits the radius `r_{n,n}` boundary at its endpoint.  Before that hit it
stays in the terminal disc.  This file records the elementary scale separation
showing that the whole terminal disc is disjoint from every profile boundary
with index strictly smaller than `n`.

The statements are purely geometric.  In particular, no independence or
distributional premise is used.
-/

open Set Real

namespace Erdos1165.TerminalSpliceProfileGeometry

open ThickPoint TerminalExcursionPathwise TerminalSequentialVisitLaw
open AnnularProfileClocks TerminalGlobalExitSplice
open RadialHarnackSpecialization PotentialEuclideanGeometry
open MarkedBridgeFactorization

noncomputable section

/-! ## Elementary Euclidean separation -/

lemma latticeDistance_eq_euclideanRadius_sub (center z : Point) :
    latticeDistance center z = euclideanRadius (z - center) := by
  unfold latticeDistance squaredDistance euclideanRadius euclideanRadiusSq
  congr 1
  rcases center with ⟨c₁, c₂⟩
  rcases z with ⟨z₁, z₂⟩
  norm_num
  ring

lemma adjacent_sub_center {center z w : Point} (hzw : Adjacent z w) :
    Adjacent (z - center) (w - center) := by
  rcases center with ⟨c₁, c₂⟩
  rcases z with ⟨z₁, z₂⟩
  rcases w with ⟨w₁, w₂⟩
  unfold Adjacent at hzw ⊢
  norm_num at hzw ⊢
  simpa [sub_sub] using hzw

/-- Moving by one nearest-neighbor step can increase distance from a fixed
center by at most one. -/
lemma latticeDistance_le_add_one_of_adjacent
    {center z w : Point} (hzw : Adjacent z w) :
    latticeDistance center w ≤ latticeDistance center z + 1 := by
  have hrad := abs_euclideanRadius_sub_le_of_adjacent
    (adjacent_sub_center (center := center) hzw)
  rw [latticeDistance_eq_euclideanRadius_sub,
    latticeDistance_eq_euclideanRadius_sub]
  linarith [(abs_le.mp hrad).1]

/-- A disc separated by one full nearest-neighbor step from a larger radius
does not meet the inner vertex boundary of the larger disc. -/
lemma not_mem_discBoundary_of_mem_disc_of_add_one_le
    {center z : Point} {r R : ℝ}
    (hz : z ∈ disc center r) (hsep : r + 1 ≤ R) :
    z ∉ discBoundary center R := by
  rintro ⟨_zIn, w, hwOut, hzw⟩
  apply hwOut
  change latticeDistance center w ≤ R
  have hzdist : latticeDistance center z ≤ r := hz
  exact (latticeDistance_le_add_one_of_adjacent hzw).trans (by linarith)

/-! ## Separation of the HLOZ scale array -/

/-- On its regular range the HLOZ radius array decreases with its index. -/
lemma scaleRadius_antitone_of_le
    {n k l : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    scaleRadius n l ≤ scaleRadius n k := by
  rw [scaleRadius_of_le hln, scaleRadius_of_le (hkl.trans hln)]
  unfold regularRadius
  apply mul_le_mul_of_nonneg_right
  · rw [Real.exp_le_exp]
    have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  · positivity

/-- Every pre-terminal regular scale is separated from the terminal outer
radius by at least one nearest-neighbor step. -/
lemma scaleRadius_self_add_one_le_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) :
    scaleRadius n n + 1 ≤ scaleRadius n k := by
  rw [scaleRadius_of_le le_rfl, regularRadius_self,
    scaleRadius_of_le hk.le]
  unfold regularRadius
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 9 :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hdiff : (1 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
    have hcast : (k : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hk)
    linarith
  have hexpTwo : (2 : ℝ) ≤ Real.exp ((n : ℝ) - (k : ℝ)) := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := Real.add_one_le_exp 1
      _ ≤ Real.exp ((n : ℝ) - (k : ℝ)) :=
        Real.exp_le_exp.mpr hdiff
  nlinarith [mul_le_mul_of_nonneg_right hexpTwo (by positivity :
    (0 : ℝ) ≤ (n : ℝ) ^ 9)]

/-- The entire terminal outer disc misses every strictly coarser profile
boundary. -/
lemma terminalDisc_avoids_scaleBoundary_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) {x z : Point}
    (hz : z ∈ disc x (scaleRadius n n)) :
    z ∉ discBoundary x (scaleRadius n k) := by
  exact not_mem_discBoundary_of_mem_disc_of_add_one_le hz
    (scaleRadius_self_add_one_le_of_lt hn hk)

/-- The corresponding statement in the profile-clock boundary notation. -/
lemma terminalDisc_avoids_profileInnerBoundary_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) {x z : Point}
    (hz : z ∈ disc x (scaleRadius n n)) :
    z ∉ profileInnerBoundary n k x := by
  simpa [profileInnerBoundary] using
    terminalDisc_avoids_scaleBoundary_of_lt hn hk hz

lemma terminalDisc_avoids_profileOuterBoundary_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) {x z : Point}
    (hz : z ∈ disc x (scaleRadius n n)) :
    z ∉ profileOuterBoundary n k x := by
  apply terminalDisc_avoids_scaleBoundary_of_lt hn (k := k - 1)
  · omega
  · exact hz

/-! ## First-hit terminal words -/

lemma terminalInnerBoundary_subset_terminalDisc
    {n : ℕ} (hn : 1 ≤ n) {x start : Point}
    (hstart : start ∈ terminalInnerBoundary n x) :
    start ∈ disc x (scaleRadius n n) := by
  exact hstart.1.trans (terminalRadius_le_regularRadius_self n hn)

/-- A terminal first-hit word stays inside the terminal outer disc through
its endpoint. -/
lemma trajectoryFrom_mem_terminalDisc_of_firstHit
    {n N : ℕ} (hn : 1 ≤ n) {x start : Point} {omega : StepPath}
    (hstart : start ∈ terminalInnerBoundary n x)
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start omega N) :
    ∀ q ≤ N, PlanarPotential.trajectoryFrom start omega q ∈
      disc x (scaleRadius n n) := by
  apply trajectoryFrom_mem_of_absoluteBoundaryFirstAt_innerBoundary
    (terminalInnerBoundary_subset_terminalDisc hn hstart)
  simpa [terminalOuterBoundary, discBoundary] using hfirst

/-- No strict-prefix vertex of a canonical terminal replacement word can hit
any strictly coarser profile inner boundary. -/
lemma trajectoryFrom_avoids_profileInnerBoundary_of_terminalFirstHit
    {n k N : ℕ} (hn : 1 ≤ n) (hk : k < n)
    {x start : Point} {omega : StepPath}
    (hstart : start ∈ terminalInnerBoundary n x)
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start omega N) :
    ∀ q < N, PlanarPotential.trajectoryFrom start omega q ∉
      profileInnerBoundary n k x := by
  intro q hq
  exact terminalDisc_avoids_profileInnerBoundary_of_lt hn hk
    (trajectoryFrom_mem_terminalDisc_of_firstHit hn hstart hfirst q hq.le)

lemma trajectoryFrom_avoids_profileOuterBoundary_of_terminalFirstHit
    {n k N : ℕ} (hn : 1 ≤ n) (hk : k < n)
    {x start : Point} {omega : StepPath}
    (hstart : start ∈ terminalInnerBoundary n x)
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start omega N) :
    ∀ q < N, PlanarPotential.trajectoryFrom start omega q ∉
      profileOuterBoundary n k x := by
  intro q hq
  exact terminalDisc_avoids_profileOuterBoundary_of_lt hn hk
    (trajectoryFrom_mem_terminalDisc_of_firstHit hn hstart hfirst q hq.le)

/-- Before its endpoint, a terminal replacement word avoids both boundaries
used by every strictly coarser alternating profile clock. -/
lemma trajectoryFrom_avoids_profileBoundaries_of_terminalFirstHit
    {n k N : ℕ} (hn : 1 ≤ n) (hk : k < n)
    {x start : Point} {omega : StepPath}
    (hstart : start ∈ terminalInnerBoundary n x)
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start omega N) :
    ∀ q < N,
      PlanarPotential.trajectoryFrom start omega q ∉ profileOuterBoundary n k x ∧
      PlanarPotential.trajectoryFrom start omega q ∉ profileInnerBoundary n k x := by
  intro q hq
  exact ⟨
    trajectoryFrom_avoids_profileOuterBoundary_of_terminalFirstHit
      hn hk hstart hfirst q hq,
    trajectoryFrom_avoids_profileInnerBoundary_of_terminalFirstHit
      hn hk hstart hfirst q hq⟩

/-- At the terminal index, the endpoint is on the profile inner boundary and
that boundary has not occurred earlier. -/
lemma terminalFirstHit_eq_profileInnerBoundary_at_self
    {n N : ℕ} {x start : Point} {omega : StepPath}
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start omega N) :
    PlanarPotential.trajectoryFrom start omega N ∈
        profileInnerBoundary n n x ∧
      ∀ q < N, PlanarPotential.trajectoryFrom start omega q ∉
        profileInnerBoundary n n x := by
  simpa [profileInnerBoundary, terminalOuterBoundary,
    AbsoluteBoundaryFirstAt] using hfirst

/-- Word-length specialization used by canonical stopped bridge codes. -/
lemma terminalWord_avoids_profileInnerBoundary_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n)
    {x start : Point} {word : StoppedWord}
    (hstart : start ∈ terminalInnerBoundary n x)
    (hfirst : AbsoluteBoundaryFirstAt
      (terminalOuterBoundary n x) start (extendStoppedWord word) word.1) :
    ∀ q < word.1,
      PlanarPotential.trajectoryFrom start (extendStoppedWord word) q ∉
        profileInnerBoundary n k x :=
  trajectoryFrom_avoids_profileInnerBoundary_of_terminalFirstHit
    hn hk hstart hfirst

end

end Erdos1165.TerminalSpliceProfileGeometry

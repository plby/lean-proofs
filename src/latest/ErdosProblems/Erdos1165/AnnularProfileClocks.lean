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

import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms
import ErdosProblems.Erdos1165.TerminalExcursionPathwise

/-!
# Literal intermediate-annulus clocks for a fixed Appendix-A profile

At scale `k`, a completed inward excursion runs from
`∂D(x,r_{n,k-1})` to `∂D(x,r_{n,k})`.  The complementary-skeleton
decomposition erases the following inner-to-outer piece, ending at the next
hit of `∂D(x,r_{n,k-1})`.  This file names those three literal finite clocks
and proves their endpoint support and completion before the global outer
exit.  These are the concrete clocks used by the stopped-word insertion
construction; no stopping-time or distributional premise is introduced.
-/

open Set

namespace Erdos1165.AnnularProfileClocks

noncomputable section

open ThickPoint TerminalExcursionPathwise

/-- Outer boundary of the `k`-th profile transition. -/
def profileOuterBoundary (n k : ℕ) (x : Point) : Set Point :=
  discBoundary x (scaleRadius n (k - 1))

/-- Inner boundary of the `k`-th profile transition. -/
def profileInnerBoundary (n k : ℕ) (x : Point) : Set Point :=
  discBoundary x (scaleRadius n k)

/-- Outer entrance time of the `j`-th inward excursion at scale `k`. -/
noncomputable def profileOuterHitTime
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : ℕ := by
  classical
  exact excursionStart s (profileOuterBoundary n k x)
    (profileInnerBoundary n k x) horizon j

/-- Inner completion time of the `j`-th inward excursion at scale `k`. -/
noncomputable def profileInnerHitTime
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : ℕ := by
  classical
  exact excursionFinish s (profileOuterBoundary n k x)
    (profileInnerBoundary n k x) horizon j

/-- End of the erased inner-to-outer gap following inward excursion `j`. -/
noncomputable def profileGapExitTime
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : ℕ :=
  profileOuterHitTime s n horizon x k (j + 1)

/-- Number of completed inward excursions at a fixed profile scale. -/
noncomputable def profileCompletedCount
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k : ℕ) : ℕ := by
  classical
  exact completedExcursionCount s (profileOuterBoundary n k x)
    (profileInnerBoundary n k x) horizon

lemma scaleRadius_le_scaleRadius_zero {n k : ℕ} (hk : k ≤ n) :
    scaleRadius n k ≤ scaleRadius n 0 := by
  rw [scaleRadius_of_le hk, scaleRadius_of_le (Nat.zero_le n)]
  unfold regularRadius
  apply mul_le_mul_of_nonneg_right
  · rw [Real.exp_le_exp]
    simpa only [Nat.cast_zero, sub_zero] using
      sub_le_self (n : ℝ) (Nat.cast_nonneg k)
  · positivity

/-- Any scale disc used in the internal profile stays well inside the global
outer disc, even after one nearest-neighbor step. -/
lemma adjacent_profileDisc_mem_globalDisc
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {x y z : Point}
    (hx : x ∈ candidateBox n)
    (hy : y ∈ disc x (scaleRadius n k)) (hyz : Adjacent y z) :
    z ∈ disc (0, 0) (outerScale n) := by
  let r : ℝ := scaleRadius n 0
  have hr1 : 1 ≤ r := one_le_scaleRadius_zero n hn
  have hr0 : 0 ≤ r := hr1.trans' zero_le_one
  have hkRadius : scaleRadius n k ≤ r := scaleRadius_le_scaleRadius_zero hk
  have hyDist : latticeDistance x y ≤ r := hy.trans hkRadius
  have hxy1 : |(((x.1 - y.1 : ℤ) : ℝ))| ≤ r :=
    (abs_fst_sub_le_latticeDistance x y).trans hyDist
  have hxy2 : |(((x.2 - y.2 : ℤ) : ℝ))| ≤ r :=
    (abs_snd_sub_le_latticeDistance x y).trans hyDist
  have hxAbs := candidate_coordinate_abs_le_three_radius hx
  have hy1 : |(y.1 : ℝ)| ≤ 4 * r := by
    calc
      |(y.1 : ℝ)| = |(x.1 : ℝ) - ((x.1 - y.1 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(x.1 : ℝ)| + |(((x.1 - y.1 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 4 * r := by dsimp only [r] at *; linarith
  have hy2 : |(y.2 : ℝ)| ≤ 4 * r := by
    calc
      |(y.2 : ℝ)| = |(x.2 : ℝ) - ((x.2 - y.2 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(x.2 : ℝ)| + |(((x.2 - y.2 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 4 * r := by dsimp only [r] at *; linarith
  have hyz1Nat : (y.1 - z.1).natAbs ≤ 1 := by
    unfold Adjacent at hyz
    omega
  have hyz2Nat : (y.2 - z.2).natAbs ≤ 1 := by
    unfold Adjacent at hyz
    omega
  have hyz1 : |(((y.1 - z.1 : ℤ) : ℝ))| ≤ 1 := by
    have hsquareInt : (y.1 - z.1) ^ 2 ≤ (1 : ℤ) ^ 2 :=
      Int.natAbs_le_iff_sq_le.mp (by simpa using hyz1Nat)
    have hsquare : (((y.1 - z.1 : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      exact_mod_cast hsquareInt
    nlinarith [sq_abs (((y.1 - z.1 : ℤ) : ℝ)),
      abs_nonneg (((y.1 - z.1 : ℤ) : ℝ))]
  have hyz2 : |(((y.2 - z.2 : ℤ) : ℝ))| ≤ 1 := by
    have hsquareInt : (y.2 - z.2) ^ 2 ≤ (1 : ℤ) ^ 2 :=
      Int.natAbs_le_iff_sq_le.mp (by simpa using hyz2Nat)
    have hsquare : (((y.2 - z.2 : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      exact_mod_cast hsquareInt
    nlinarith [sq_abs (((y.2 - z.2 : ℤ) : ℝ)),
      abs_nonneg (((y.2 - z.2 : ℤ) : ℝ))]
  have hz1 : |(z.1 : ℝ)| ≤ 5 * r := by
    calc
      |(z.1 : ℝ)| = |(y.1 : ℝ) - ((y.1 - z.1 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(y.1 : ℝ)| + |(((y.1 - z.1 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 5 * r := by linarith
  have hz2 : |(z.2 : ℝ)| ≤ 5 * r := by
    calc
      |(z.2 : ℝ)| = |(y.2 : ℝ) - ((y.2 - z.2 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(y.2 : ℝ)| + |(((y.2 - z.2 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 5 * r := by linarith
  change latticeDistance (0, 0) z ≤ outerScale n
  rw [outerScale_eq_sixteen_mul_radius_zero]
  unfold latticeDistance squaredDistance
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hz10 : 0 ≤ |(z.1 : ℝ)| := abs_nonneg _
    have hz20 : 0 ≤ |(z.2 : ℝ)| := abs_nonneg _
    have hz1sq : |(z.1 : ℝ)| ^ 2 = (z.1 : ℝ) ^ 2 := sq_abs _
    have hz2sq : |(z.2 : ℝ)| ^ 2 = (z.2 : ℝ) ^ 2 := sq_abs _
    push_cast
    nlinarith

lemma profileDisc_disjoint_globalBoundary
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) {x y : Point}
    (hx : x ∈ candidateBox n) (hy : y ∈ disc x (scaleRadius n k)) :
    y ∉ discBoundary (0, 0) (outerScale n) := by
  rintro ⟨_hyGlobal, z, hzOutside, hyz⟩
  exact hzOutside (adjacent_profileDisc_mem_globalDisc hn hk hx hy hyz)

lemma profileInnerHitTime_le_horizon_of_lt_count
    {s : WalkPath} {n horizon k j : ℕ} {x : Point}
    (hj : j < profileCompletedCount s n horizon x k) :
    profileInnerHitTime s n horizon x k j ≤ horizon := by
  classical
  unfold profileCompletedCount at hj
  unfold profileInnerHitTime
  exact finish_le_horizon_of_lt_completedExcursionCount s
    (profileOuterBoundary n k x) (profileInnerBoundary n k x) horizon hj

lemma excursionProfile_eq_profileCompletedCount
    (s : WalkPath) (n horizon : ℕ) (x : Point) {k : ℕ}
    (hkpos : 0 < k) (hk : k < n + 2) :
    excursionProfile s n horizon x ⟨k, hk⟩ =
      profileCompletedCount s n horizon x k := by
  classical
  unfold excursionProfile profileCompletedCount profileOuterBoundary
    profileInnerBoundary
  simp only [dif_neg hkpos.ne']

lemma fixedProfile_count_eq
    {s : WalkPath} {n horizon : ℕ} {x : Point} {profileDelta : ℝ}
    {m : AppendixFirstMoment.Profile n}
    (hfixed : AnnularProfileLiteralAtoms.FixedSuccessfulProfile n profileDelta m
      (excursionProfile s n horizon x))
    (i : Fin (n - 1)) :
    profileCompletedCount s n horizon x (AppendixFirstMoment.scaleIndex i) =
      m i := by
  have hkpos : 0 < AppendixFirstMoment.scaleIndex i := by
    simp [AppendixFirstMoment.scaleIndex]
  have hk : AppendixFirstMoment.scaleIndex i < n + 2 := by
    unfold AppendixFirstMoment.scaleIndex
    omega
  rw [← excursionProfile_eq_profileCompletedCount s n horizon x hkpos hk]
  exact hfixed.2.1 i

/-- Every inward excursion prescribed by a fixed internal profile is a
literal completed excursion before the stopping horizon. -/
lemma fixedProfile_innerHit_le
    {s : WalkPath} {n horizon : ℕ} {x : Point} {profileDelta : ℝ}
    {m : AppendixFirstMoment.Profile n}
    (hfixed : AnnularProfileLiteralAtoms.FixedSuccessfulProfile n profileDelta m
      (excursionProfile s n horizon x))
    (i : Fin (n - 1)) (j : Fin (m i)) :
    profileInnerHitTime s n horizon x (AppendixFirstMoment.scaleIndex i) j ≤
      horizon := by
  apply profileInnerHitTime_le_horizon_of_lt_count
  rw [fixedProfile_count_eq hfixed i]
  exact j.isLt

lemma profileOuterHit_mem_of_innerHit_le
    {s : WalkPath} {n horizon k j : ℕ} {x : Point}
    (hinner : profileInnerHitTime s n horizon x k j ≤ horizon) :
    s (profileOuterHitTime s n horizon x k j) ∈
      profileOuterBoundary n k x := by
  classical
  unfold profileInnerHitTime at hinner
  unfold profileOuterHitTime
  exact excursionStart_mem_outer_of_finish_le s
    (profileOuterBoundary n k x) (profileInnerBoundary n k x) horizon j hinner

lemma profileInnerHit_mem_of_le
    {s : WalkPath} {n horizon k j : ℕ} {x : Point}
    (hinner : profileInnerHitTime s n horizon x k j ≤ horizon) :
    s (profileInnerHitTime s n horizon x k j) ∈
      profileInnerBoundary n k x := by
  classical
  unfold profileInnerHitTime at hinner ⊢
  exact excursionFinish_mem_inner_of_le s
    (profileOuterBoundary n k x) (profileInnerBoundary n k x) horizon j hinner

lemma profileInnerHitTime_le_profileGapExitTime
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k j : ℕ) :
    profileInnerHitTime s n horizon x k j ≤
      profileGapExitTime s n horizon x k j := by
  classical
  unfold profileInnerHitTime profileGapExitTime profileOuterHitTime
  exact excursionFinish_le_next_start s
    (profileOuterBoundary n k x) (profileInnerBoundary n k x) horizon j

lemma profileGapExitTime_eq_firstHitThrough
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k j : ℕ) :
    profileGapExitTime s n horizon x k j =
      @firstHitThrough s (profileOuterBoundary n k x) (Classical.decPred _)
        (profileInnerHitTime s n horizon x k j) horizon := by
  classical
  unfold profileGapExitTime profileOuterHitTime profileInnerHitTime
    excursionStart
  rw [← excursionFinish_eq_iterate_succ s
    (profileOuterBoundary n k x) (profileInnerBoundary n k x) horizon j]

/-- Once an inward excursion at an internal profile scale is complete, the
following inner-to-outer piece is also complete before the global exit. -/
lemma profileGapExitTime_le_of_globalExit
    {s : WalkPath} {n horizon k j : ℕ} {x : Point}
    (hn : 1 ≤ n) (hkpos : 1 ≤ k) (hkn : k ≤ n)
    (hexit : IsOuterExitTime s n horizon)
    (hx : x ∈ candidateBox n)
    (hstep : ∀ q, Adjacent (s q) (s (q + 1)))
    (hinner : profileInnerHitTime s n horizon x k j ≤ horizon) :
    profileGapExitTime s n horizon x k j ≤ horizon := by
  classical
  have hinnerBoundary := profileInnerHit_mem_of_le hinner
  have hinnerDisc : s (profileInnerHitTime s n horizon x k j) ∈
      disc x (scaleRadius n (k - 1)) := by
    have hmem : s (profileInnerHitTime s n horizon x k j) ∈
        disc x (scaleRadius n k) := hinnerBoundary.1
    change latticeDistance x
      (s (profileInnerHitTime s n horizon x k j)) ≤ scaleRadius n (k - 1)
    change latticeDistance x
      (s (profileInnerHitTime s n horizon x k j)) ≤ scaleRadius n k at hmem
    exact hmem.trans (by
    rw [scaleRadius_of_le hkn, scaleRadius_of_le (by omega : k - 1 ≤ n)]
    unfold regularRadius
    apply mul_le_mul_of_nonneg_right
    · rw [Real.exp_le_exp]
      apply sub_le_sub_left
      exact_mod_cast Nat.sub_le k 1
    · positivity)
  have hout : s horizon ∉ disc x (scaleRadius n (k - 1)) := by
    intro hdisc
    exact (profileDisc_disjoint_globalBoundary hn (by omega : k - 1 ≤ n)
      hx hdisc) hexit.1
  have hcross := firstHitThrough_innerBoundary_le_of_exit s
    (disc x (scaleRadius n (k - 1))) hstep hinner hinnerDisc hout
  rw [profileGapExitTime_eq_firstHitThrough]
  change firstHitThrough s (innerBoundary (disc x (scaleRadius n (k - 1))))
    (profileInnerHitTime s n horizon x k j) horizon ≤ horizon
  convert hcross using 1

lemma profileGapExit_mem_outerBoundary
    {s : WalkPath} {n horizon k j : ℕ} {x : Point}
    (hexit : profileGapExitTime s n horizon x k j ≤ horizon) :
    s (profileGapExitTime s n horizon x k j) ∈
      profileOuterBoundary n k x := by
  classical
  unfold profileGapExitTime
  have hstart : profileOuterHitTime s n horizon x k (j + 1) ≤ horizon := hexit
  unfold profileOuterHitTime excursionStart at hstart ⊢
  exact firstHitThrough_mem_set_of_le s (profileOuterBoundary n k x)
    ((excursionStep s (profileOuterBoundary n k x)
      (profileInnerBoundary n k x) horizon)^[j + 1] 0) horizon hstart

lemma adjacent_shiftedWalk
    (start : ℕ) (omega : StepPath) (q : ℕ) :
    Adjacent (Proposition13Assembly.shiftedWalk start omega q)
      (Proposition13Assembly.shiftedWalk start omega (q + 1)) := by
  exact Proposition13Assembly.adjacent_trajectory_succ
    (shiftSteps start omega) q

/-- Concrete completion theorem for every erased gap prescribed by a fixed
internal profile. -/
lemma fixedProfile_gapExit_le
    {s : WalkPath} {n horizon : ℕ} {x : Point} {profileDelta : ℝ}
    {m : AppendixFirstMoment.Profile n}
    (hn : 1 ≤ n) (hexit : IsOuterExitTime s n horizon)
    (hx : x ∈ candidateBox n)
    (hstep : ∀ q, Adjacent (s q) (s (q + 1)))
    (hfixed : AnnularProfileLiteralAtoms.FixedSuccessfulProfile n profileDelta m
      (excursionProfile s n horizon x))
    (i : Fin (n - 1)) (j : Fin (m i)) :
    profileGapExitTime s n horizon x (AppendixFirstMoment.scaleIndex i) j ≤
      horizon := by
  apply profileGapExitTime_le_of_globalExit hn
    (by simp [AppendixFirstMoment.scaleIndex])
    (by
      unfold AppendixFirstMoment.scaleIndex
      omega)
    hexit hx hstep
  exact fixedProfile_innerHit_le hfixed i j

/-- Shifted-walk specialization used by the literal stopped profile atom. -/
lemma fixedProfile_gapExit_le_shiftedWalk
    {omega : StepPath} {start n horizon : ℕ}
    {x : Point} {profileDelta : ℝ} {m : AppendixFirstMoment.Profile n}
    (hn : 1 ≤ n)
    (hexit : IsOuterExitTime
      (Proposition13Assembly.shiftedWalk start omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : AnnularProfileLiteralAtoms.FixedSuccessfulProfile n profileDelta m
      (excursionProfile (Proposition13Assembly.shiftedWalk start omega)
        n horizon x))
    (i : Fin (n - 1)) (j : Fin (m i)) :
    profileGapExitTime (Proposition13Assembly.shiftedWalk start omega)
        n horizon x (AppendixFirstMoment.scaleIndex i) j ≤ horizon := by
  exact fixedProfile_gapExit_le hn hexit hx
    (adjacent_shiftedWalk start omega) hfixed i j

end

end Erdos1165.AnnularProfileClocks

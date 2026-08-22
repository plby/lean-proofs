/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalRenewal

/-!
# External local-time tails from Green-function estimates

This module turns the exact renewal identity for the retained-block external
walk into its strongest unconditional elementary Green-function comparison,
and records the additional increment hypothesis needed for a geometric tail
on the `G(n)` scale.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalRenewal

open ExternalWalk ExternalOnePoint LazyDecomposition

variable (o : Orientation)

lemma externalFirstReturnMassENNReal_toReal (n : ℕ) :
    (externalFirstReturnMassENNReal o n).toReal = externalFirstReturnMass o n := by
  rw [externalFirstReturnMassENNReal, externalFirstReturnMass,
    RenewalTail.firstReturnMass, ENNReal.toReal_sum]
  · rfl
  · intro k hk
    exact measure_ne_top _ _

lemma externalTruncatedGreen_toReal (n : ℕ) :
    (externalTruncatedGreen o n).toReal = externalTruncatedGreenReal o n := by
  rw [externalTruncatedGreen, externalTruncatedGreenReal,
    RenewalTail.truncatedGreen, ENNReal.toReal_sum]
  · rfl
  · intro k hk
    exact measure_ne_top _ _

lemma externalFirstReturnMassENNReal_ne_top (n : ℕ) :
    externalFirstReturnMassENNReal o n ≠ ∞ := by
  rw [externalFirstReturnMassENNReal, ENNReal.sum_ne_top]
  intro k hk
  exact measure_ne_top _ _

lemma externalTruncatedGreen_ne_top (n : ℕ) :
    externalTruncatedGreen o n ≠ ∞ := by
  rw [externalTruncatedGreen, ENNReal.sum_ne_top]
  intro k hk
  exact measure_ne_top _ _

lemma one_le_externalTruncatedGreen (n : ℕ) :
    1 ≤ externalTruncatedGreen o n := by
  rw [externalTruncatedGreen, Finset.sum_range_succ']
  have hset : externalReturnAt o 0 = Set.univ := by
    ext η
    simp [externalReturnAt, externalPosition_zero]
  simp [hset]

lemma externalFirstReturnMassENNReal_le_one (n : ℕ) :
    externalFirstReturnMassENNReal o n ≤ 1 := by
  rw [externalFirstReturnMassENNReal]
  calc
    (∑ k ∈ Finset.Icc 1 n, externalBlocks o (externalFirstReturnAt o k)) =
        externalBlocks o (⋃ k ∈ Finset.Icc 1 n, externalFirstReturnAt o k) := by
      symm
      apply measure_biUnion_finset
      · intro i hi j hj hij
        exact externalFirstReturnAt_pairwise_disjoint o hij
      · intro k hk
        exact measurableSet_externalFirstReturnAt o k
    _ ≤ externalBlocks o Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- The exact renewal identity gives the strongest unconditional elementary
comparison with truncated Green functions: the probability of a first
positive return by time `n`, multiplied by `G(n)`, is at most `G(2n) - 1`. -/
theorem externalFirstReturnMass_mul_green_le_ennreal (n : ℕ) :
    externalFirstReturnMassENNReal o n * externalTruncatedGreen o n ≤
      externalTruncatedGreen o (2 * n) - 1 := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (externalFirstReturnMassENNReal_ne_top o n)
      (externalTruncatedGreen_ne_top o n))
    (ENNReal.sub_ne_top (externalTruncatedGreen_ne_top o (2 * n)))).mp
  rw [ENNReal.toReal_mul, externalFirstReturnMassENNReal_toReal,
    externalTruncatedGreen_toReal,
    ENNReal.toReal_sub_of_le (one_le_externalTruncatedGreen o (2 * n))
      (externalTruncatedGreen_ne_top o (2 * n)),
    externalTruncatedGreen_toReal, ENNReal.toReal_one]
  exact externalFirstReturnMass_mul_green_le o n

/-- Ratio form of the exact finite renewal/last-exit bound.  This is
unconditional; replacing the numerator by `G(n) - c` requires a separate
increment estimate between horizons `n` and `2n`. -/
theorem externalFirstReturnMass_le_green_ratio (n : ℕ) :
    externalFirstReturnMassENNReal o n ≤
      (externalTruncatedGreen o (2 * n) - 1) / externalTruncatedGreen o n := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_externalTruncatedGreen o n))))
    (Or.inl (externalTruncatedGreen_ne_top o n))).2
  exact externalFirstReturnMass_mul_green_le_ennreal o n

/-- The ratio estimate combined with the probability bound `q(n) ≤ 1`.
This remains informative even if the comparable-horizon Green ratio exceeds
one. -/
theorem externalFirstReturnMass_le_min_green_ratio (n : ℕ) :
    externalFirstReturnMassENNReal o n ≤
      min 1 ((externalTruncatedGreen o (2 * n) - 1) /
        externalTruncatedGreen o n) := by
  exact le_min (externalFirstReturnMassENNReal_le_one o n)
    (externalFirstReturnMass_le_green_ratio o n)

/-- A quantitative Green-increment estimate converts the unconditional
`G(2n)/G(n)` renewal bound into the customary hitting estimate
`q(n) ≤ 1 - c/G(n)`.  Such an increment estimate is genuinely additional:
it does not follow from the renewal identity alone. -/
theorem externalFirstReturnMass_le_one_sub_green
    (n : ℕ) (c : ℝ≥0∞)
    (hincrement : externalTruncatedGreen o (2 * n) - 1 ≤
      externalTruncatedGreen o n - c) :
    externalFirstReturnMassENNReal o n ≤
      1 - c / externalTruncatedGreen o n := by
  have hG0 : externalTruncatedGreen o n ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_externalTruncatedGreen o n))
  have hGtop : externalTruncatedGreen o n ≠ ∞ :=
    externalTruncatedGreen_ne_top o n
  calc
    externalFirstReturnMassENNReal o n ≤
        (externalTruncatedGreen o n - c) / externalTruncatedGreen o n := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl hG0) (Or.inl hGtop)).2
      exact (externalFirstReturnMass_mul_green_le_ennreal o n).trans hincrement
    _ = externalTruncatedGreen o n / externalTruncatedGreen o n -
          c / externalTruncatedGreen o n := by
      exact ENNReal.sub_div fun _ _ ↦ hG0
    _ = 1 - c / externalTruncatedGreen o n := by
      rw [ENNReal.div_self hG0 hGtop]

/-- Fully unconditional local-time tail bound obtained from exact renewal.
The comparable horizon `2n` is forced by the finite renewal rectangle. -/
theorem externalOriginLocalTime_tail_le_green_ratio (r n : ℕ) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      ((externalTruncatedGreen o (2 * n) - 1) /
        externalTruncatedGreen o n) ^ r := by
  exact (externalReturnTail_le_firstReturnMass_pow o r n).trans
    (pow_le_pow_left' (externalFirstReturnMass_le_green_ratio o n) r)

/-- The strongest form obtained by also retaining that a hitting probability
is at most one. -/
theorem externalOriginLocalTime_tail_le_min_green_ratio (r n : ℕ) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      (min 1 ((externalTruncatedGreen o (2 * n) - 1) /
        externalTruncatedGreen o n)) ^ r := by
  exact (externalReturnTail_le_firstReturnMass_pow o r n).trans
    (pow_le_pow_left' (externalFirstReturnMass_le_min_green_ratio o n) r)

/-- Combine a Green-increment estimate and any explicit upper bound `H` on
`G(n)`.  This is the reusable finite-horizon form used with `H = C log n`:
the local-time tail is geometrically small on the Green-function scale. -/
theorem externalOriginLocalTime_tail_le_of_green_increment_and_bound
    (r n : ℕ) (c H : ℝ≥0∞)
    (hincrement : externalTruncatedGreen o (2 * n) - 1 ≤
      externalTruncatedGreen o n - c)
    (hgreen : externalTruncatedGreen o n ≤ H) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      (1 - c / H) ^ r := by
  have hhit := externalFirstReturnMass_le_one_sub_green o n c hincrement
  have hdiv : c / H ≤ c / externalTruncatedGreen o n :=
    ENNReal.div_le_div_left hgreen c
  have hbase : 1 - c / externalTruncatedGreen o n ≤ 1 - c / H :=
    tsub_le_tsub_left hdiv 1
  exact (externalOriginLocalTime_tail_le_geometric o r n c hhit).trans
    (pow_le_pow_left' hbase r)

/-- Explicit logarithmic-scale specialization.  The shift `n + 2` keeps the
logarithmic denominator positive even at the smallest horizons. -/
theorem externalOriginLocalTime_tail_le_logarithmic
    (r n : ℕ) (c : ℝ≥0∞) (C : ℝ)
    (hincrement : externalTruncatedGreen o (2 * n) - 1 ≤
      externalTruncatedGreen o n - c)
    (hgreen : externalTruncatedGreen o n ≤
      ENNReal.ofReal (C * Real.log (n + 2))) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      (1 - c / ENNReal.ofReal (C * Real.log (n + 2))) ^ r := by
  exact externalOriginLocalTime_tail_le_of_green_increment_and_bound
    o r n c (ENNReal.ofReal (C * Real.log (n + 2))) hincrement hgreen

/-- Threshold-indexed logarithmic form.  Since the visit at time zero is
automatic, a threshold of `k` visits has exponent `k - 1`. -/
theorem externalOriginLocalTime_tail_le_logarithmic_threshold
    (k n : ℕ) (hk : 0 < k) (c : ℝ≥0∞) (C : ℝ)
    (hincrement : externalTruncatedGreen o (2 * n) - 1 ≤
      externalTruncatedGreen o n - c)
    (hgreen : externalTruncatedGreen o n ≤
      ENNReal.ofReal (C * Real.log (n + 2))) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤
      (1 - c / ENNReal.ofReal (C * Real.log (n + 2))) ^ (k - 1) := by
  have hk_eq : k - 1 + 1 = k := by omega
  simpa only [hk_eq] using externalOriginLocalTime_tail_le_logarithmic
    o (k - 1) n c C hincrement hgreen

end Erdos1165.ExternalRenewal

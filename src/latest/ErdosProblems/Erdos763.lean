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

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 763

The detailed mathematical argument and its formalization plan are in
`tex/763.tex`.  We formalize the ordered additive convolution of the
indicator of an arbitrary set `A ⊆ ℕ` and prove that its summatory function
cannot differ from a positive linear function by `O(1)`.
-/

open Filter Metric Set
open scoped BigOperators Topology Asymptotics Real

namespace Erdos763

/-- The `ℕ`-valued indicator of a subset of the natural numbers. -/
noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  open scoped Classical in
  if n ∈ A then 1 else 0

/-- The ordered representation function `(1_A * 1_A)(n)`. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), indicator A a * indicator A (n - a)

/-- The summatory ordered representation function through `N`, inclusive. -/
noncomputable def summatoryRepresentationCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), representationCount A n

@[simp] lemma indicator_eq_one_iff {A : Set ℕ} {n : ℕ} :
    indicator A n = 1 ↔ n ∈ A := by
  classical
  simp [indicator]

@[simp] lemma indicator_le_one (A : Set ℕ) (n : ℕ) : indicator A n ≤ 1 := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

@[simp] lemma norm_indicator_cast (A : Set ℕ) (n : ℕ) :
    ‖(indicator A n : ℂ)‖ = indicator A n := by
  classical
  by_cases hn : n ∈ A <;> simp [indicator, hn]

/-! ## Bounded power series and Parseval on a circle -/

/-- The analytic function represented by a sequence of complex coefficients. -/
noncomputable def powerSeriesValue (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z ^ n

/-- The degree `< K` truncation of a coefficient sequence. -/
noncomputable def truncPolynomial (a : ℕ → ℂ) (r : ℝ) (K : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range K, Polynomial.monomial n (a n * (r : ℂ) ^ n)

lemma summable_norm_mul_pow_of_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ ↦ ‖a n * ((r : ℂ) * z) ^ n‖ := by
  have hgeom : Summable fun n : ℕ ↦ C * r ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by simpa [abs_of_nonneg hr0])).mul_left C
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) _ hgeom
  intro n
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n)
        (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
    _ ≤ C * r ^ n := by
      gcongr
      exact mul_le_of_le_one_right hr0 hz

lemma summable_mul_pow_of_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ ↦ a n * ((r : ℂ) * z) ^ n :=
  (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz).of_norm

lemma truncPolynomial_eval (a : ℕ → ℂ) (r : ℝ) (K : ℕ) (z : ℂ) :
    (truncPolynomial a r K).eval z =
      ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n := by
  rw [truncPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_monomial, mul_pow]
  ring

lemma truncPolynomial_coeff (a : ℕ → ℂ) (r : ℝ) (K n : ℕ) :
    (truncPolynomial a r K).coeff n =
      if n < K then a n * (r : ℂ) ^ n else 0 := by
  simp [truncPolynomial, Polynomial.coeff_monomial, Finset.mem_range]

lemma truncPolynomial_support_subset (a : ℕ → ℂ) (r : ℝ) (K : ℕ) :
    (truncPolynomial a r K).support ⊆ Finset.range K := by
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  rw [Finset.mem_range]
  by_contra hnot
  apply hn
  rw [truncPolynomial_coeff]
  simp [hnot]

lemma truncPolynomial_parseval (a : ℕ → ℂ) {r : ℝ} (hr0 : 0 ≤ r) (K : ℕ) :
    ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n) =
      Real.circleAverage
        (fun z : ℂ ↦ ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 := by
  let p := truncPolynomial a r K
  have havg :
      Real.circleAverage
          (fun z : ℂ ↦ ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2) 0 1 =
        Real.circleAverage (fun z : ℂ ↦ ‖p.eval z‖ ^ 2) 0 1 := by
    apply congrArg (fun f : ℂ → ℝ ↦ Real.circleAverage f 0 1)
    funext z
    dsimp only [p]
    rw [truncPolynomial_eval]
  rw [havg, ← p.sum_sq_norm_coeff_eq_circleAverage]
  have hsupp : p.support ⊆ Finset.range K := truncPolynomial_support_subset a r K
  rw [Finset.sum_subset hsupp]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [p, truncPolynomial_coeff, Finset.mem_range.mp hn, if_pos]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    ring
  · intro n hnrange hnsupp
    simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hnsupp
    simp [hnsupp]

lemma powerSeriesValue_continuousOn_sphere {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    ContinuousOn (fun z : ℂ ↦ powerSeriesValue a ((r : ℂ) * z)) (sphere 0 1) := by
  apply continuousOn_tsum (u := fun n : ℕ ↦ C * r ^ n)
  · intro n
    fun_prop
  · exact (summable_geometric_of_norm_lt_one (K := ℝ)
      (by simpa [abs_of_nonneg hr0])).mul_left C
  · intro n z hz
    have hznorm : ‖z‖ = 1 := by simpa using hz
    simpa [powerSeriesValue, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, hznorm] using
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hr0 n)

lemma powerSeriesValue_trunc_error {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) (K : ℕ) :
    ‖(∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n) -
        powerSeriesValue a ((r : ℂ) * z)‖ ≤ C * r ^ K / (1 - r) := by
  apply norm_sub_le_of_geometric_bound_of_hasSum hr1
      (f := fun n : ℕ ↦ a n * ((r : ℂ) * z) ^ n) ?_
      ((summable_mul_pow_of_bounded hC hr0 hr1 ha z hz).hasSum)
  intro n
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n)
        (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
    _ ≤ C * r ^ n := by
      gcongr
      exact mul_le_of_le_one_right hr0 hz

lemma powerSeriesValue_norm_le {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖powerSeriesValue a ((r : ℂ) * z)‖ ≤ C / (1 - r) := by
  calc
    ‖powerSeriesValue a ((r : ℂ) * z)‖ ≤ ∑' n : ℕ, ‖a n * ((r : ℂ) * z) ^ n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz)
    _ ≤ ∑' n : ℕ, C * r ^ n := by
      apply (summable_norm_mul_pow_of_bounded hC hr0 hr1 ha z hz).tsum_le_tsum
      · intro n
        rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0]
        calc
          ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
            exact mul_le_mul_of_nonneg_right (ha n)
              (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
          _ ≤ C * r ^ n := by
            gcongr
            exact mul_le_of_le_one_right hr0 hz
      · exact (summable_geometric_of_norm_lt_one (K := ℝ)
          (by simpa [abs_of_nonneg hr0])).mul_left C
    _ = C / (1 - r) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).tsum_eq]
      field_simp

lemma truncValue_norm_le {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ 1) (K : ℕ) :
    ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ≤ C / (1 - r) := by
  calc
    ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ≤
        ∑ n ∈ Finset.range K, C * r ^ n := by
      refine (norm_sum_le _ _).trans ?_
      gcongr with n hn
      rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr0]
      calc
        ‖a n‖ * (r * ‖z‖) ^ n ≤ C * (r * ‖z‖) ^ n := by
          exact mul_le_mul_of_nonneg_right (ha n)
            (pow_nonneg (mul_nonneg hr0 (norm_nonneg z)) n)
        _ ≤ C * r ^ n := by
          gcongr
          exact mul_le_of_le_one_right hr0 hz
    _ ≤ ∑' n : ℕ, C * r ^ n := by
      exact ((summable_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).mul_left C).sum_le_tsum
          (Finset.range K) (fun _ _ ↦ mul_nonneg hC (pow_nonneg hr0 _))
    _ = C / (1 - r) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg hr0])).tsum_eq]
      field_simp

lemma abs_circleAverage_sub_le {f g : ℂ → ℝ} {R B : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere 0 R))
    (hg : ContinuousOn g (sphere 0 R))
    (hB : ∀ z ∈ sphere (0 : ℂ) R, |f z - g z| ≤ B) :
    |Real.circleAverage f 0 R - Real.circleAverage g 0 R| ≤ B := by
  have hfi := hf.circleIntegrable hR
  have hgi := hg.circleIntegrable hR
  rw [← Real.circleAverage_sub hfi hgi]
  calc
    |Real.circleAverage (f - g) 0 R| ≤
        Real.circleAverage (fun z ↦ |(f - g) z|) 0 R :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun _ : ℂ ↦ B) 0 R := by
      apply Real.circleAverage_mono
      · exact (hf.sub hg).abs.circleIntegrable hR
      · exact continuousOn_const.circleIntegrable hR
      · intro z hz
        apply hB z
        simpa [abs_of_nonneg hR] using hz
    _ = B := Real.circleAverage_const B 0 R

lemma summable_sq_norm_mul_rpow {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    Summable fun n : ℕ ↦ ‖a n‖ ^ 2 * r ^ (2 * n) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun n : ℕ ↦ C ^ 2 * (r ^ 2) ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ)
      (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).mul_left (C ^ 2)
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)) _ hgeom
  intro n
  have hsq : ‖a n‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [ha n, norm_nonneg (a n)]
  calc
    ‖a n‖ ^ 2 * r ^ (2 * n) ≤ C ^ 2 * r ^ (2 * n) := by
      exact mul_le_mul_of_nonneg_right hsq (pow_nonneg hr0 _)
    _ = C ^ 2 * (r ^ 2) ^ n := by ring

lemma circleParseval_bounded {a : ℕ → ℂ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n, ‖a n‖ ≤ C) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖powerSeriesValue a ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n) := by
  let S : ℂ → ℂ := fun z ↦ powerSeriesValue a ((r : ℂ) * z)
  let P : ℕ → ℂ → ℂ := fun K z ↦
    ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n
  have hScont : ContinuousOn S (sphere 0 1) :=
    powerSeriesValue_continuousOn_sphere hC hr0 hr1 ha
  have hPcont (K : ℕ) : ContinuousOn (P K) (sphere 0 1) := by
    exact (by
      dsimp only [P]
      fun_prop : Continuous (P K)).continuousOn
  have hleft : Tendsto
      (fun K ↦ Real.circleAverage (fun z : ℂ ↦ ‖P K z‖ ^ 2) 0 1) atTop
      (𝓝 (Real.circleAverage (fun z : ℂ ↦ ‖S z‖ ^ 2) 0 1)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have herr : Tendsto
        (fun K : ℕ ↦ (C * r ^ K / (1 - r)) * (2 * (C / (1 - r)))) atTop (𝓝 0) := by
      have hp : Tendsto (fun K : ℕ ↦ r ^ K) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one
          (by simpa [abs_of_nonneg hr0])
      have hc : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
      have hp' : Tendsto (fun K : ℕ ↦ C * r ^ K / (1 - r)) atTop (𝓝 0) :=
        by simpa using (hc.mul hp).div_const (1 - r)
      simpa using hp'.mul_const (2 * (C / (1 - r)))
    exact squeeze_zero (g := fun K : ℕ ↦
      (C * r ^ K / (1 - r)) * (2 * (C / (1 - r))))
      (fun _ ↦ dist_nonneg) (fun K ↦ by
        rw [Real.dist_eq]
        apply abs_circleAverage_sub_le (R := (1 : ℝ)) (B :=
          (C * r ^ K / (1 - r)) * (2 * (C / (1 - r)))) zero_le_one
        · exact (hPcont K).norm.pow 2
        · exact hScont.norm.pow 2
        · intro z hz
          have hznorm : ‖z‖ ≤ 1 := le_of_eq (by simpa using hz)
          have htail := powerSeriesValue_trunc_error hC hr0 hr1 ha hznorm K
          have hPnorm := truncValue_norm_le hC hr0 hr1 ha hznorm K
          have hSnorm := powerSeriesValue_norm_le hC hr0 hr1 ha hznorm
          dsimp only [P, S]
          rw [abs_sub_comm]
          calc
            |‖powerSeriesValue a ((r : ℂ) * z)‖ ^ 2 -
                ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ ^ 2| =
                |‖powerSeriesValue a ((r : ℂ) * z)‖ -
                  ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖| *
                (‖powerSeriesValue a ((r : ℂ) * z)‖ +
                  ‖∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖) := by
              rw [sq_sub_sq, abs_mul,
                abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
              ring
            _ ≤ ‖powerSeriesValue a ((r : ℂ) * z) -
                  ∑ n ∈ Finset.range K, a n * ((r : ℂ) * z) ^ n‖ *
                  (2 * (C / (1 - r))) := by
              apply mul_le_mul
              · exact abs_norm_sub_norm_le _ _
              · linarith
              · positivity
              · positivity
            _ ≤ (C * r ^ K / (1 - r)) * (2 * (C / (1 - r))) := by
              apply mul_le_mul_of_nonneg_right
              · simpa only [norm_sub_rev] using htail
              · positivity) herr
  have hright : Tendsto
      (fun K ↦ ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 * r ^ (2 * n)) atTop
      (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n))) :=
    (summable_sq_norm_mul_rpow hC hr0 hr1 ha).hasSum.tendsto_sum_nat
  have hright' : Tendsto
      (fun K ↦ Real.circleAverage (fun z : ℂ ↦ ‖P K z‖ ^ 2) 0 1) atTop
      (𝓝 (∑' n : ℕ, ‖a n‖ ^ 2 * r ^ (2 * n))) := by
    apply hright.congr'
    filter_upwards [] with K
    exact truncPolynomial_parseval a hr0 K
  exact tendsto_nhds_unique hleft hright'

/-! ## The convolution series and the bounded-error identity -/

/-- The complex-valued indicator coefficients. -/
noncomputable def indicatorComplex (A : Set ℕ) (n : ℕ) : ℂ := indicator A n

/-- The real error after normalizing the summatory function by `c (n + 1)`. -/
noncomputable def summatoryError (A : Set ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  summatoryRepresentationCount A n - c * (n + 1)

lemma indicatorComplex_norm_le_one (A : Set ℕ) (n : ℕ) :
    ‖indicatorComplex A n‖ ≤ 1 := by
  simp [indicatorComplex]

lemma summatoryRepresentationCount_succ (A : Set ℕ) (n : ℕ) :
    summatoryRepresentationCount A (n + 1) =
      summatoryRepresentationCount A n + representationCount A (n + 1) := by
  simp [summatoryRepresentationCount, Finset.sum_range_succ]

lemma representationCount_zero (A : Set ℕ) :
    representationCount A 0 = summatoryRepresentationCount A 0 := by
  simp [representationCount, summatoryRepresentationCount]

lemma representationCount_cast_complex (A : Set ℕ) (n : ℕ) :
    (representationCount A n : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        indicatorComplex A k * indicatorComplex A (n - k) := by
  simp [representationCount, indicatorComplex, Nat.cast_sum, Nat.cast_mul]

lemma representationCount_eq_error_difference (A : Set ℕ) (c : ℝ) :
    ∀ n : ℕ,
      (representationCount A n : ℝ) = c + summatoryError A c n -
        if n = 0 then 0 else summatoryError A c (n - 1) := by
  intro n
  cases n with
  | zero =>
      simp [summatoryError, representationCount_zero]
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      simp only [Nat.succ_sub_one]
      rw [summatoryError, summatoryError, summatoryRepresentationCount_succ]
      push_cast
      ring

lemma summatoryError_bounded_of_isBigO {A : Set ℕ} {c : ℝ}
    (h : (fun N : ℕ ↦ (summatoryRepresentationCount A N : ℝ) - c * N) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, ‖summatoryError A c n‖ ≤ D := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C + ‖c‖, add_nonneg hC0 (norm_nonneg _), ?_⟩
  intro n
  have hn := hC n
  rw [summatoryError]
  have hid :
      (summatoryRepresentationCount A n : ℝ) - c * (n + 1) =
        ((summatoryRepresentationCount A n : ℝ) - c * n) - c := by
    push_cast
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans (by simpa [add_comm] using add_le_add_right hn ‖c‖)

lemma summable_norm_coeff_mul_pow {a : ℕ → ℂ} {D : ℝ} {z : ℂ}
    (hD : 0 ≤ D) (ha : ∀ n, ‖a n‖ ≤ D) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ ↦ ‖a n * z ^ n‖ := by
  have hgeom : Summable fun n : ℕ ↦ D * ‖z‖ ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by simpa using hz)).mul_left D
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg z) n)

lemma indicator_series_summable' (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ ↦ ‖indicatorComplex A n * z ^ n‖ := by
  exact summable_norm_coeff_mul_pow zero_le_one (indicatorComplex_norm_le_one A) hz

lemma indicatorSeries_sq {A : Set ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    powerSeriesValue (indicatorComplex A) z ^ 2 =
      powerSeriesValue (fun n ↦ (representationCount A n : ℂ)) z := by
  have hs := indicator_series_summable' A hz
  rw [pow_two, powerSeriesValue,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  apply tsum_congr
  intro n
  simp only [representationCount_cast_complex]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    indicatorComplex A k * z ^ k * (indicatorComplex A (n - k) * z ^ (n - k)) =
        indicatorComplex A k * indicatorComplex A (n - k) *
          (z ^ k * z ^ (n - k)) := by ring
    _ = indicatorComplex A k * indicatorComplex A (n - k) * z ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]

lemma shifted_error_hasSum {A : Set ℕ} {c D : ℝ} {z : ℂ}
    (hD : 0 ≤ D) (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ ↦ ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n)
      (z * powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) := by
  have hsum : Summable fun n : ℕ ↦ (summatoryError A c n : ℂ) * z ^ n := by
    exact (summable_norm_coeff_mul_pow hD (by simpa using he) hz).of_norm
  let g : ℕ → ℂ := fun n ↦
    ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n
  have htail : HasSum (fun n : ℕ ↦ g (n + 1))
      (z * powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) := by
    have hm := hsum.hasSum.mul_left z
    simpa [g, powerSeriesValue, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hm
  have hall := (hasSum_nat_add_iff (f := g) 1).mp htail
  simpa [g] using hall

lemma representation_series_identity {A : Set ℕ} {c D : ℝ} {z : ℂ}
    (hD : 0 ≤ D) (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hz : ‖z‖ < 1) :
    powerSeriesValue (fun n ↦ (representationCount A n : ℂ)) z =
      (c : ℂ) / (1 - z) + (1 - z) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  have heSum : Summable fun n : ℕ ↦ (summatoryError A c n : ℂ) * z ^ n := by
    exact (summable_norm_coeff_mul_pow hD (by simpa using he) hz).of_norm
  have hcSum : HasSum (fun n : ℕ ↦ (c : ℂ) * z ^ n) ((c : ℂ) / (1 - z)) := by
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hz).mul_left (c : ℂ)
  have hshift := shifted_error_hasSum (A := A) hD he hz
  have htotal := hcSum.add heSum.hasSum |>.sub hshift
  rw [powerSeriesValue, powerSeriesValue]
  calc
    (∑' n : ℕ, (representationCount A n : ℂ) * z ^ n) =
        ∑' n : ℕ, ((c : ℂ) * z ^ n + (summatoryError A c n : ℂ) * z ^ n -
          ((if n = 0 then 0 else summatoryError A c (n - 1)) : ℂ) * z ^ n) := by
      apply tsum_congr
      intro n
      have hrC : (representationCount A n : ℂ) =
          (c : ℂ) + (summatoryError A c n : ℂ) -
            (((if n = 0 then 0 else summatoryError A c (n - 1)) : ℝ) : ℂ) := by
        exact_mod_cast representationCount_eq_error_difference A c n
      rw [hrC]
      push_cast
      split_ifs <;> simp_all <;> ring
    _ = (c : ℂ) / (1 - z) +
        (∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n) -
          z * ∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n := htotal.tsum_eq
    _ = (c : ℂ) / (1 - z) + (1 - z) *
        ∑' n : ℕ, (summatoryError A c n : ℂ) * z ^ n := by ring

lemma indicatorSeries_sq_eq_main {A : Set ℕ} {c D : ℝ} {z : ℂ}
    (hD : 0 ≤ D) (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hz : ‖z‖ < 1) :
    powerSeriesValue (indicatorComplex A) z ^ 2 =
      (c : ℂ) / (1 - z) + (1 - z) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  rw [indicatorSeries_sq hz, representation_series_identity hD he hz]

/-! ## A finite geometric block and its integer coefficients -/

/-- `1 + z + ⋯ + z^(M-1)`. -/
def geometricBlock (M : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range M, z ^ k

/-- Coefficients of `geometricBlock M * indicatorSeries A`. -/
noncomputable def blockCoefficient (A : Set ℕ) (M n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0

lemma blockCoefficient_le (A : Set ℕ) (M n : ℕ) : blockCoefficient A M n ≤ M := by
  rw [blockCoefficient]
  calc
    (∑ k ∈ Finset.range M, if k ≤ n then indicator A (n - k) else 0) ≤
        ∑ _k ∈ Finset.range M, 1 := by
      gcongr with k hk
      split_ifs <;> simp
    _ = M := by simp

lemma cauchy_block_sum (A : Set ℕ) (M n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (if k < M then 1 else 0) * indicator A (n - k)) = blockCoefficient A M n := by
  rw [blockCoefficient]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro k hk
    rfl

lemma block_sequence_summable_norm (M : ℕ) (z : ℂ) :
    Summable fun k : ℕ ↦ ‖((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k‖ := by
  apply summable_of_ne_finset_zero (s := Finset.range M)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  simp [hk]

lemma block_sequence_tsum (M : ℕ) (z : ℂ) :
    (∑' k : ℕ, ((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) = geometricBlock M z := by
  rw [tsum_eq_sum (s := Finset.range M)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]

lemma blockSeries_identity {A : Set ℕ} (M : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    geometricBlock M z * powerSeriesValue (indicatorComplex A) z =
      powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ)) z := by
  have hBlock := block_sequence_summable_norm M z
  have hInd := indicator_series_summable' A hz
  rw [← block_sequence_tsum, powerSeriesValue,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hBlock hInd]
  apply tsum_congr
  intro n
  have hcast : (blockCoefficient A M n : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) := by
    simp [indicatorComplex]
    norm_cast
    simpa using (cauchy_block_sum A M n).symm
  change (∑ k ∈ Finset.range (n + 1),
      (((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) *
        (indicatorComplex A (n - k) * z ^ (n - k))) =
    (blockCoefficient A M n : ℂ) * z ^ n
  rw [hcast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    ((((if k < M then 1 else 0 : ℕ) : ℂ) * z ^ k) *
        (indicatorComplex A (n - k) * z ^ (n - k))) =
        (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) *
          (z ^ k * z ^ (n - k)) := by ring
    _ = (((if k < M then 1 else 0 : ℕ) : ℂ) * indicatorComplex A (n - k)) * z ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]

lemma blockCoefficient_complex_norm_le (A : Set ℕ) (M n : ℕ) :
    ‖(blockCoefficient A M n : ℂ)‖ ≤ M := by
  simpa using blockCoefficient_le A M n

lemma block_parseval {A : Set ℕ} (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑' n : ℕ, (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
  have hparse := circleParseval_bounded (a := fun n ↦ (blockCoefficient A M n : ℂ))
    (C := (M : ℝ)) (r := r) (Nat.cast_nonneg M) hr0 hr1
    (blockCoefficient_complex_norm_le A M)
  have hparse' :
      Real.circleAverage
          (fun z : ℂ ↦ ‖powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ))
            ((r : ℂ) * z)‖ ^ 2) 0 1 =
        ∑' n : ℕ, (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
    simpa using hparse
  rw [← hparse']
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hznorm : ‖z‖ = 1 := by simpa using hz
  change ‖geometricBlock M ((r : ℂ) * z) *
      powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2 =
    ‖powerSeriesValue (fun n ↦ (blockCoefficient A M n : ℂ)) ((r : ℂ) * z)‖ ^ 2
  rw [← blockSeries_identity M (by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm]
    simpa using hr1)]

lemma blockCoefficient_real_series_identity {A : Set ℕ} (M : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (blockCoefficient A M n : ℝ) * q ^ n) =
      (∑ k ∈ Finset.range M, q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n := by
  have hBlock : Summable fun k : ℕ ↦
      ‖((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k‖ := by
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]
  have hInd : Summable fun n : ℕ ↦ ‖(indicator A n : ℝ) * q ^ n‖ := by
    have hgeom : Summable fun n : ℕ ↦ q ^ n :=
      summable_geometric_of_norm_lt_one (K := ℝ) (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
    intro n
    rw [norm_mul, norm_pow]
    simp only [Real.norm_eq_abs, abs_of_nonneg hq0]
    have hind : ‖(indicator A n : ℝ)‖ ≤ 1 := by
      by_cases hn : n ∈ A <;> simp [indicator, hn]
    simpa using mul_le_mul_of_nonneg_right hind (pow_nonneg hq0 n)
  calc
    (∑' n : ℕ, (blockCoefficient A M n : ℝ) * q ^ n) =
        ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k) *
            ((indicator A (n - k) : ℝ) * q ^ (n - k)) := by
      apply tsum_congr
      intro n
      have hcast : (blockCoefficient A M n : ℝ) =
          ∑ k ∈ Finset.range (n + 1),
            (((if k < M then 1 else 0 : ℕ) : ℝ) * (indicator A (n - k) : ℝ)) := by
        norm_cast
        simpa using (cauchy_block_sum A M n).symm
      rw [hcast, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      push_cast
      have hp : q ^ k * q ^ (n - k) = q ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [← hp]
      ring
    _ = (∑' k : ℕ, ((if k < M then 1 else 0 : ℕ) : ℝ) * q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n :=
      (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hBlock hInd).symm
    _ = (∑ k ∈ Finset.range M, q ^ k) *
        ∑' n : ℕ, (indicator A n : ℝ) * q ^ n := by
      congr 1
      rw [tsum_eq_sum (s := Finset.range M)]
      · apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.mem_range.mp hk]
      · intro k hk
        simp only [Finset.mem_range, not_lt] at hk
        simp [hk]

lemma summable_real_coeff_mul_pow_of_bounded {a : ℕ → ℝ} {C q : ℝ}
    (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) (ha : ∀ n, |a n| ≤ C) :
    Summable fun n : ℕ ↦ a n * q ^ n := by
  have hgeom : Summable fun n : ℕ ↦ C * q ^ n :=
    (summable_geometric_of_norm_lt_one (K := ℝ) (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).mul_left C
  have habs : Summable fun n : ℕ ↦ ‖a n * q ^ n‖ := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hq0 n)
  exact habs.of_norm

lemma blockCoefficient_series_summable (A : Set ℕ) (M : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ ↦ (blockCoefficient A M n : ℝ) * q ^ n := by
  apply summable_real_coeff_mul_pow_of_bounded (C := M) (Nat.cast_nonneg M) hq0 hq1
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast blockCoefficient_le A M n

lemma blockCoefficient_sq_series_summable (A : Set ℕ) (M : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ ↦ (blockCoefficient A M n : ℝ) ^ 2 * r ^ (2 * n) := by
  simpa using summable_sq_norm_mul_rpow (a := fun n ↦ (blockCoefficient A M n : ℂ))
    (C := (M : ℝ)) (r := r) (Nat.cast_nonneg M) hr0 hr1
    (blockCoefficient_complex_norm_le A M)

lemma natCast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hn : n ≤ n * n := Nat.le_mul_self n
  exact_mod_cast (by simpa [pow_two] using hn)

lemma block_parseval_lower {A : Set ℕ} (M : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range M, (r ^ 2) ^ k) *
        (∑' n : ℕ, (indicator A n : ℝ) * (r ^ 2) ^ n) ≤
      Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 := by
  have hr2_0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hr2_1 : r ^ 2 < 1 := by nlinarith
  rw [block_parseval M hr0 hr1, ← blockCoefficient_real_series_identity M hr2_0 hr2_1]
  apply (blockCoefficient_series_summable A M hr2_0 hr2_1).tsum_le_tsum
  · intro n
    simpa [pow_mul] using
      mul_le_mul_of_nonneg_right (natCast_le_sq (blockCoefficient A M n))
        (pow_nonneg hr2_0 n)
  · exact blockCoefficient_sq_series_summable A M hr0 hr1

/-- The nonnegative real value of the indicator generating series on the real interval. -/
noncomputable def indicatorSeriesReal (A : Set ℕ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, (indicator A n : ℝ) * q ^ n

lemma indicator_real_series_summable (A : Set ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ ↦ (indicator A n : ℝ) * q ^ n := by
  apply summable_real_coeff_mul_pow_of_bounded (C := 1) zero_le_one hq0 hq1
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast indicator_le_one A n

lemma indicatorSeriesReal_nonneg (A : Set ℕ) {q : ℝ} (hq0 : 0 ≤ q) :
    0 ≤ indicatorSeriesReal A q := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 n)

lemma indicatorSeries_at_real {A : Set ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    powerSeriesValue (indicatorComplex A) (q : ℂ) = indicatorSeriesReal A q := by
  rw [powerSeriesValue, indicatorSeriesReal]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [indicatorComplex]

lemma errorSeries_norm_le {A : Set ℕ} {c D q : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)‖ ≤ D / (1 - q) := by
  simpa using powerSeriesValue_norm_le hD hq0 hq1 (fun n ↦ by simpa using he n)
    (z := (1 : ℂ)) (by norm_num)

lemma indicatorSeriesReal_sq_lower {A : Set ℕ} {c D q : ℝ} (_hc : 0 < c) (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    c / (1 - q) - D ≤ (indicatorSeriesReal A q) ^ 2 := by
  have hqnorm : ‖(q : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hid := indicatorSeries_sq_eq_main (A := A) (c := c) hD he hqnorm
  rw [indicatorSeries_at_real hq0 hq1] at hid
  have herr := errorSeries_norm_le hD he hq0 hq1
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hre :
      |(powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re| ≤
        D / (1 - q) :=
    (Complex.abs_re_le_norm _).trans herr
  apply_fun Complex.re at hid
  have hmain : ((c : ℂ) / ((1 : ℂ) - (q : ℂ))).re = c / (1 - q) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.ofReal_re]
  have hleft : ((indicatorSeriesReal A q : ℂ) ^ 2).re =
      (indicatorSeriesReal A q) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hprod :
      (((1 : ℂ) - (q : ℂ)) *
        powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re =
        (1 - q) *
          (powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re := by
    simp
  simp only [Complex.add_re] at hid
  rw [hleft, hmain, hprod] at hid
  have hpert :
      -D ≤ (1 - q) *
        (powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re := by
    have := (abs_le.mp hre).1
    calc
      -D = (1 - q) * (-(D / (1 - q))) := by field_simp
      _ ≤ (1 - q) *
          (powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) (q : ℂ)).re := by
        gcongr
  rw [hid]
  convert add_le_add_left hpert (c / (1 - q)) using 1 <;> ring

lemma geometricBlock_norm_le (M : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖geometricBlock M w‖ ≤ M := by
  rw [geometricBlock]
  calc
    ‖∑ k ∈ Finset.range M, w ^ k‖ ≤ ∑ k ∈ Finset.range M, ‖w ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range M, (1 : ℝ) := by
      gcongr with k hk
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw
    _ = M := by simp

lemma geometricBlock_circle_sq (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    Real.circleAverage (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z)‖ ^ 2) 0 1 =
      ∑ k ∈ Finset.range M, r ^ (2 * k) := by
  symm
  simpa [geometricBlock] using truncPolynomial_parseval (fun _ : ℕ ↦ (1 : ℂ)) hr0 M

lemma geometricBlock_circle_sq_le (M : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.circleAverage (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z)‖ ^ 2) 0 1 ≤ M := by
  rw [geometricBlock_circle_sq M hr0]
  calc
    (∑ k ∈ Finset.range M, r ^ (2 * k)) ≤ ∑ _k ∈ Finset.range M, (1 : ℝ) := by
      gcongr with k hk
      exact pow_le_one₀ hr0 hr1
    _ = M := by simp

/-- The reciprocal distance to the pole at `1`, in angular coordinates. -/
noncomputable def circleKernelAngle (r θ : ℝ) : ℝ :=
  ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖⁻¹

lemma circleKernel_den_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    0 < ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖ := by
  have hrev := abs_norm_sub_norm_le (1 : ℂ) ((r : ℂ) * circleMap 0 1 θ)
  have hle : 1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖ := by
    calc
      1 - r = |‖(1 : ℂ)‖ - ‖(r : ℂ) * circleMap 0 1 θ‖| := by
        simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
          norm_circleMap_zero, abs_of_nonneg]
        exact (abs_of_nonneg (sub_nonneg.mpr hr1.le)).symm
      _ ≤ ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖ := hrev
  exact (sub_pos.mpr hr1).trans_le hle

lemma circleKernelAngle_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (circleKernelAngle r) := by
  have hbase : Continuous fun θ : ℝ ↦
      ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖ := by fun_prop
  exact hbase.inv₀ (fun θ ↦ (circleKernel_den_pos hr0 hr1 θ).ne')

lemma circleKernelAngle_edge_le {r θ : ℝ} (hrhalf : 1 / 2 ≤ r) (hr1 : r < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    circleKernelAngle r θ ≤ 2 / (1 - r + θ / Real.pi) := by
  have hr0 : 0 ≤ r := by linarith
  let d := ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖
  have hdpos : 0 < d := circleKernel_den_pos hr0 hr1 θ
  have ha : 1 - r ≤ d := by
    have hrev := abs_norm_sub_norm_le (1 : ℂ) ((r : ℂ) * circleMap 0 1 θ)
    calc
      1 - r = |‖(1 : ℂ)‖ - ‖(r : ℂ) * circleMap 0 1 θ‖| := by
        simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
          norm_circleMap_zero, abs_of_nonneg, abs_of_nonneg (sub_nonneg.mpr hr1.le)]
      _ ≤ d := hrev
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have him : r * Real.sin θ ≤ d := by
    calc
      r * Real.sin θ =
          |((1 : ℂ) - (r : ℂ) * circleMap 0 1 θ).im| := by
        simp [circleMap_zero_im, abs_of_nonneg (mul_nonneg hr0 hsin0)]
      _ ≤ d := Complex.abs_im_le_norm _
  have hjordan := Real.mul_le_sin hθ0 hθ1
  have htheta : θ / Real.pi ≤ d := by
    have hpi : 0 < Real.pi := Real.pi_pos
    calc
      θ / Real.pi ≤ r * (2 / Real.pi * θ) := by
        field_simp
        nlinarith
      _ ≤ r * Real.sin θ := mul_le_mul_of_nonneg_left hjordan hr0
      _ ≤ d := him
  have hsumpos : 0 < 1 - r + θ / Real.pi := by positivity
  rw [circleKernelAngle, div_eq_mul_inv]
  change d⁻¹ ≤ 2 * (1 - r + θ / Real.pi)⁻¹
  rw [mul_comm 2 (1 - r + θ / Real.pi)⁻¹, le_inv_mul_iff₀ hsumpos,
    mul_inv_le_iff₀ hdpos]
  nlinarith

lemma circleKernelAngle_middle_le {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hθ0 : Real.pi / 2 ≤ θ) (hθ1 : θ ≤ Real.pi + Real.pi / 2) :
    circleKernelAngle r θ ≤ 1 := by
  let d := ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 θ‖
  have hdpos : 0 < d := circleKernel_den_pos hr0 hr1 θ
  have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hθ0 hθ1
  have hre : 1 ≤ ((1 : ℂ) - (r : ℂ) * circleMap 0 1 θ).re := by
    simp [circleMap_zero_re]
    nlinarith
  have hd : 1 ≤ d := hre.trans (Complex.re_le_norm _)
  rw [circleKernelAngle]
  exact (inv_le_one₀ hdpos).2 hd

lemma circleKernelAngle_symm (r θ : ℝ) :
    circleKernelAngle r (2 * Real.pi - θ) = circleKernelAngle r θ := by
  rw [circleKernelAngle, circleKernelAngle]
  congr 1
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub]

lemma edgeMajorant_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in 0..Real.pi / 2, 2 / (a + x / Real.pi)) =
      2 * Real.pi * Real.log (a + (Real.pi / 2) / Real.pi) -
        2 * Real.pi * Real.log a := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun y ↦ 2 * Real.pi * Real.log (a + y / Real.pi))
        (2 / (a + x / Real.pi)) x := by
    intro x hx
    have hx0 : 0 ≤ x := by
      have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
      exact hx'.1
    have harg : a + x / Real.pi ≠ 0 := by positivity
    have hraw := ((Real.hasDerivAt_log harg).comp x
      ((hasDerivAt_const x a).add ((hasDerivAt_id x).div_const Real.pi))).const_mul
        (2 * Real.pi)
    have hcoef : 2 * Real.pi * ((a + x / Real.pi)⁻¹ * (1 / Real.pi)) =
        2 / (a + x / Real.pi) := by field_simp [Real.pi_ne_zero]
    rw [← hcoef]
    simpa only [Function.comp_apply, Pi.add_apply, Pi.div_apply,
      id_eq, zero_add, one_div] using hraw
  have hint : IntervalIntegrable (fun x : ℝ ↦ 2 / (a + x / Real.pi)) MeasureTheory.volume
      0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_id.div_const Real.pi))
    intro x hx
    have hx0 : 0 ≤ x := by
      have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
      exact hx'.1
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (div_nonneg hx0 Real.pi_pos.le))
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

lemma edgeMajorant_integral_le_log_inv {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    (∫ x in 0..Real.pi / 2, 2 / (a + x / Real.pi)) ≤
      2 * Real.pi * Real.log a⁻¹ := by
  rw [edgeMajorant_integral ha, Real.log_inv]
  have hhalf : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by field_simp [Real.pi_ne_zero]
  rw [hhalf]
  have hlog : Real.log (a + 1 / 2) ≤ 0 :=
    Real.log_nonpos (by positivity) (by linarith)
  nlinarith [Real.pi_pos]

lemma circleKernel_average_le {r : ℝ} (hrhalf : 1 / 2 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ ↦ ‖(1 : ℂ) - (r : ℂ) * z‖⁻¹) 0 1 ≤
      2 * Real.log (1 - r)⁻¹ + 1 / 2 := by
  have hr0 : 0 ≤ r := by linarith
  have ha : 0 < 1 - r := sub_pos.mpr hr1
  have ha2 : 1 - r ≤ 1 / 2 := by linarith
  have hkcont := circleKernelAngle_continuous hr0 hr1
  have hkint (a b : ℝ) : IntervalIntegrable (circleKernelAngle r) MeasureTheory.volume a b :=
    hkcont.intervalIntegrable a b
  have hmajorInt : IntervalIntegrable (fun x : ℝ ↦ 2 / (1 - r + x / Real.pi))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.sub continuousOn_const |>.add (continuousOn_id.div_const Real.pi))
    intro x hx
    have hx0 : 0 ≤ x := by
      have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hx
      exact hx'.1
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sub_pos.mpr hr1)
      (div_nonneg hx0 Real.pi_pos.le))
  have hleft :
      (∫ x in 0..Real.pi / 2, circleKernelAngle r x) ≤
        2 * Real.pi * Real.log (1 - r)⁻¹ := by
    calc
      (∫ x in 0..Real.pi / 2, circleKernelAngle r x) ≤
          ∫ x in 0..Real.pi / 2, 2 / (1 - r + x / Real.pi) := by
        exact intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) (hkint _ _) hmajorInt
          (fun x hx ↦ circleKernelAngle_edge_le hrhalf hr1 hx.1.le hx.2.le)
      _ ≤ 2 * Real.pi * Real.log (1 - r)⁻¹ :=
        edgeMajorant_integral_le_log_inv ha ha2
  have hmiddle :
      (∫ x in Real.pi / 2..Real.pi + Real.pi / 2, circleKernelAngle r x) ≤ Real.pi := by
    calc
      (∫ x in Real.pi / 2..Real.pi + Real.pi / 2, circleKernelAngle r x) ≤
          ∫ _x in Real.pi / 2..Real.pi + Real.pi / 2, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on_of_le_Ioo (by linarith [Real.pi_pos])
          (hkint _ _) intervalIntegrable_const
          (fun x hx ↦ circleKernelAngle_middle_le hr0 hr1 hx.1.le hx.2.le)
      _ = Real.pi := by simp
  have hright :
      (∫ x in Real.pi + Real.pi / 2..2 * Real.pi, circleKernelAngle r x) ≤
        2 * Real.pi * Real.log (1 - r)⁻¹ := by
    calc
      (∫ x in Real.pi + Real.pi / 2..2 * Real.pi, circleKernelAngle r x) =
          ∫ x in Real.pi + Real.pi / 2..2 * Real.pi,
            circleKernelAngle r (2 * Real.pi - x) := by
        exact intervalIntegral.integral_congr fun x _hx ↦ (circleKernelAngle_symm r x).symm
      _ = ∫ x in 0..Real.pi / 2, circleKernelAngle r x := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
      _ ≤ 2 * Real.pi * Real.log (1 - r)⁻¹ := hleft
  have hint :
      (∫ x in 0..2 * Real.pi, circleKernelAngle r x) ≤
        4 * Real.pi * Real.log (1 - r)⁻¹ + Real.pi := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hkint 0 (Real.pi + Real.pi / 2)) (hkint (Real.pi + Real.pi / 2) (2 * Real.pi)),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hkint 0 (Real.pi / 2)) (hkint (Real.pi / 2) (Real.pi + Real.pi / 2))]
    nlinarith
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ * (∫ x in 0..2 * Real.pi, circleKernelAngle r x) ≤
    2 * Real.log (1 - r)⁻¹ + 1 / 2
  calc
    (2 * Real.pi)⁻¹ * (∫ x in 0..2 * Real.pi, circleKernelAngle r x) ≤
        (2 * Real.pi)⁻¹ * (4 * Real.pi * Real.log (1 - r)⁻¹ + Real.pi) := by
      gcongr
    _ = 2 * Real.log (1 - r)⁻¹ + 1 / 2 := by
      field_simp [Real.pi_ne_zero]
      ring

/-! ## The circle upper bound -/

lemma errorSeries_circle_sq_le {A : Set ℕ} {c D r : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ))
          ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      D ^ 2 / (1 - r ^ 2) := by
  have heC : ∀ n, ‖(summatoryError A c n : ℂ)‖ ≤ D := by
    intro n
    simpa using he n
  have hr2 : r ^ 2 < 1 := by nlinarith
  rw [circleParseval_bounded hD hr0 hr1 heC]
  calc
    (∑' n : ℕ, ‖(summatoryError A c n : ℂ)‖ ^ 2 * r ^ (2 * n)) ≤
        ∑' n : ℕ, D ^ 2 * (r ^ 2) ^ n := by
      apply (summable_sq_norm_mul_rpow hD hr0 hr1 heC).tsum_le_tsum
      · intro n
        have hsq : ‖(summatoryError A c n : ℂ)‖ ^ 2 ≤ D ^ 2 := by
          nlinarith [heC n, norm_nonneg (summatoryError A c n : ℂ)]
        simpa [pow_mul] using
          mul_le_mul_of_nonneg_right hsq (pow_nonneg (sq_nonneg r) n)
      · exact (summable_geometric_of_norm_lt_one (K := ℝ)
          (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).mul_left (D ^ 2)
    _ = D ^ 2 / (1 - r ^ 2) := by
      rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one (K := ℝ)
        (by simpa [abs_of_nonneg (sq_nonneg r)] using hr2)).tsum_eq]
      field_simp

lemma one_sub_mul_geometricBlock (M : ℕ) (z : ℂ) :
    (1 - z) * geometricBlock M z = 1 - z ^ M := by
  rw [geometricBlock, mul_comm]
  exact geom_sum_mul_neg z M

lemma block_master_identity {A : Set ℕ} {c D : ℝ} (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (M : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    (geometricBlock M z * powerSeriesValue (indicatorComplex A) z) ^ 2 =
      (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by
  rw [mul_pow, indicatorSeries_sq_eq_main hD he hz]
  have hg := one_sub_mul_geometricBlock M z
  calc
    geometricBlock M z ^ 2 *
          ((c : ℂ) / (1 - z) + (1 - z) *
            powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z) =
        (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
          ((1 - z) * geometricBlock M z) * geometricBlock M z *
            powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by ring
    _ = (c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z := by rw [hg]

lemma block_integrand_le {A : Set ℕ} {c D : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (M : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    ‖geometricBlock M z * powerSeriesValue (indicatorComplex A) z‖ ^ 2 ≤
      c * ‖geometricBlock M z‖ ^ 2 * ‖1 - z‖⁻¹ +
        2 * ‖geometricBlock M z‖ *
          ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
  have hpow : ‖z ^ M‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz.le
  calc
    ‖geometricBlock M z * powerSeriesValue (indicatorComplex A) z‖ ^ 2 =
        ‖(geometricBlock M z * powerSeriesValue (indicatorComplex A) z) ^ 2‖ := by
      rw [norm_pow]
    _ = ‖(c : ℂ) * geometricBlock M z ^ 2 / (1 - z) +
        (1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
      rw [block_master_identity hD he M hz]
    _ ≤ ‖(c : ℂ) * geometricBlock M z ^ 2 / (1 - z)‖ +
        ‖(1 - z ^ M) * geometricBlock M z *
          powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := norm_add_le _ _
    _ ≤ c * ‖geometricBlock M z‖ ^ 2 * ‖1 - z‖⁻¹ +
        2 * ‖geometricBlock M z‖ *
          ‖powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) z‖ := by
      simp only [norm_div, norm_mul, norm_pow]
      have hcabs : ‖(c : ℂ)‖ = c := by simpa [Real.norm_eq_abs, abs_of_nonneg hc]
      rw [hcabs, div_eq_mul_inv]
      have hsub : ‖(1 : ℂ) - z ^ M‖ ≤ 2 := by
        have hpow' : ‖z‖ ^ M ≤ 1 := by simpa only [norm_pow] using hpow
        calc
          ‖(1 : ℂ) - z ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ M‖ := norm_sub_le _ _
          _ ≤ 2 := by norm_num; linarith
      gcongr

lemma circleKernel_continuousOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun z : ℂ ↦ ‖(1 : ℂ) - (r : ℂ) * z‖⁻¹) (sphere 0 1) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro z hz hzero
    have hznorm : ‖z‖ = 1 := by simpa using hz
    have hcomplex : (1 : ℂ) - (r : ℂ) * z = 0 := norm_eq_zero.mp hzero
    have heq : (1 : ℂ) = (r : ℂ) * z := sub_eq_zero.mp hcomplex
    have heqnorm := congrArg norm heq
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm] at heqnorm
    linarith

lemma young_two_mul {α x y : ℝ} (hα : 0 < α) :
    2 * x * y ≤ α * x ^ 2 + y ^ 2 / α := by
  have heq : α * x ^ 2 + y ^ 2 / α = (α ^ 2 * x ^ 2 + y ^ 2) / α := by
    field_simp
  rw [heq, le_div_iff₀ hα]
  nlinarith [sq_nonneg (α * x - y)]

lemma block_circle_upper {A : Set ℕ} {c D α r : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) (hα : 0 < α)
    (hrhalf : 1 / 2 ≤ r) (hr1 : r < 1) (M : ℕ) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      c * M ^ 2 * (2 * Real.log (1 - r)⁻¹ + 1 / 2) +
        α * M + α⁻¹ * (D ^ 2 / (1 - r ^ 2)) := by
  have hr0 : 0 ≤ r := by linarith
  let H : ℂ → ℂ := fun z ↦ geometricBlock M ((r : ℂ) * z)
  let F : ℂ → ℂ := fun z ↦ powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)
  let E : ℂ → ℂ := fun z ↦
    powerSeriesValue (fun n ↦ (summatoryError A c n : ℂ)) ((r : ℂ) * z)
  let K : ℂ → ℝ := fun z ↦ ‖(1 : ℂ) - (r : ℂ) * z‖⁻¹
  have hHcont : ContinuousOn H (sphere 0 1) := by
    dsimp only [H, geometricBlock]
    fun_prop
  have hFcont : ContinuousOn F (sphere 0 1) :=
    powerSeriesValue_continuousOn_sphere zero_le_one hr0 hr1
      (indicatorComplex_norm_le_one A)
  have heC : ∀ n, ‖(summatoryError A c n : ℂ)‖ ≤ D := by
    intro n
    simpa using he n
  have hEcont : ContinuousOn E (sphere 0 1) :=
    powerSeriesValue_continuousOn_sphere hD hr0 hr1 heC
  have hKcont : ContinuousOn K (sphere 0 1) :=
    circleKernel_continuousOn hr0 hr1
  have hfint : CircleIntegrable (fun z ↦ ‖H z * F z‖ ^ 2) 0 1 :=
    (hHcont.mul hFcont).norm.pow 2 |>.circleIntegrable zero_le_one
  have hKint : CircleIntegrable K 0 1 := hKcont.circleIntegrable zero_le_one
  have hH2int : CircleIntegrable (fun z ↦ ‖H z‖ ^ 2) 0 1 :=
    hHcont.norm.pow 2 |>.circleIntegrable zero_le_one
  have hE2int : CircleIntegrable (fun z ↦ ‖E z‖ ^ 2) 0 1 :=
    hEcont.norm.pow 2 |>.circleIntegrable zero_le_one
  have hmajorInt : CircleIntegrable
      (fun z ↦ c * M ^ 2 * K z + (α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2)) 0 1 := by
    apply CircleIntegrable.add
    · exact hKint.const_mul _
    · exact (hH2int.const_mul _).add (hE2int.const_mul _)
  have hsingInt : CircleIntegrable (fun z ↦ c * M ^ 2 * K z) 0 1 :=
    hKint.const_mul _
  have hHpartInt : CircleIntegrable (fun z ↦ α * ‖H z‖ ^ 2) 0 1 :=
    hH2int.const_mul _
  have hEpartInt : CircleIntegrable (fun z ↦ α⁻¹ * ‖E z‖ ^ 2) 0 1 :=
    hE2int.const_mul _
  have hrestInt : CircleIntegrable
      (fun z ↦ α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2) 0 1 :=
    hHpartInt.add hEpartInt
  have hmono : Real.circleAverage (fun z ↦ ‖H z * F z‖ ^ 2) 0 1 ≤
      Real.circleAverage
        (fun z ↦ c * M ^ 2 * K z + (α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2)) 0 1 := by
    apply Real.circleAverage_mono hfint hmajorInt
    intro z hz
    have hznorm : ‖z‖ = 1 := by simpa using hz
    have hwle : ‖(r : ℂ) * z‖ ≤ 1 := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm, hr1.le]
    have hwlt : ‖(r : ℂ) * z‖ < 1 := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm, hr1]
    have hHle : ‖H z‖ ≤ M := by
      exact geometricBlock_norm_le M hwle
    have hHsq : ‖H z‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [norm_nonneg (H z), sq_nonneg ((M : ℝ) - ‖H z‖)]
    have hpoint := block_integrand_le hc hD he M hwlt
    change ‖H z * F z‖ ^ 2 ≤
      c * (M : ℝ) ^ 2 * K z + (α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2)
    calc
      ‖H z * F z‖ ^ 2 ≤ c * ‖H z‖ ^ 2 * K z + 2 * ‖H z‖ * ‖E z‖ := hpoint
      _ ≤ c * (M : ℝ) ^ 2 * K z +
          (α * ‖H z‖ ^ 2 + ‖E z‖ ^ 2 / α) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHsq hc) (inv_nonneg.mpr (norm_nonneg _))
        · exact young_two_mul hα
      _ = c * (M : ℝ) ^ 2 * K z +
          (α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2) := by
        rw [div_eq_inv_mul]
  calc
    Real.circleAverage (fun z ↦ ‖H z * F z‖ ^ 2) 0 1 ≤
        Real.circleAverage
          (fun z ↦ c * M ^ 2 * K z + (α * ‖H z‖ ^ 2 + α⁻¹ * ‖E z‖ ^ 2)) 0 1 := hmono
    _ = c * M ^ 2 * Real.circleAverage K 0 1 +
        (α * Real.circleAverage (fun z ↦ ‖H z‖ ^ 2) 0 1 +
          α⁻¹ * Real.circleAverage (fun z ↦ ‖E z‖ ^ 2) 0 1) := by
      rw [Real.circleAverage_fun_add hsingInt hrestInt,
        Real.circleAverage_fun_add hHpartInt hEpartInt]
      congr 1
      · rw [show (fun z ↦ c * (M : ℝ) ^ 2 * K z) =
            (c * (M : ℝ) ^ 2) • K by rfl, Real.circleAverage_smul]
        rfl
      · congr 1
        · rw [show (fun z ↦ α * ‖H z‖ ^ 2) =
              α • (fun z ↦ ‖H z‖ ^ 2) by rfl, Real.circleAverage_smul]
          rfl
        · rw [show (fun z ↦ α⁻¹ * ‖E z‖ ^ 2) =
              α⁻¹ • (fun z ↦ ‖E z‖ ^ 2) by rfl, Real.circleAverage_smul]
          rfl
    _ ≤ c * M ^ 2 * (2 * Real.log (1 - r)⁻¹ + 1 / 2) +
        (α * M + α⁻¹ * (D ^ 2 / (1 - r ^ 2))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (circleKernel_average_le hrhalf hr1)
          (mul_nonneg hc (sq_nonneg (M : ℝ))))
        (add_le_add
          (mul_le_mul_of_nonneg_left (geometricBlock_circle_sq_le M hr0 hr1.le) hα.le)
          (mul_le_mul_of_nonneg_left (errorSeries_circle_sq_le hD he hr0 hr1)
            (inv_nonneg.mpr hα.le)))
    _ = c * M ^ 2 * (2 * Real.log (1 - r)⁻¹ + 1 / 2) +
        α * M + α⁻¹ * (D ^ 2 / (1 - r ^ 2)) := by ring

/-! ## An explicit parameter choice -/

/-- The radius used in the final contradiction.  The large exponent leaves generous room
in all elementary estimates. -/
noncomputable def chosenRadius (M : ℕ) : ℝ := 1 - 1 / (M : ℝ) ^ 13

lemma geometricBlock_real_lower (M : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hclose : (M : ℝ) * (1 - q) ≤ 1 / 2) :
    (M : ℝ) / 2 ≤ ∑ k ∈ Finset.range M, q ^ k := by
  calc
    (M : ℝ) / 2 = ∑ _k ∈ Finset.range M, (1 / 2 : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ k ∈ Finset.range M, q ^ k := by
      gcongr with k hk
      have hkM : (k : ℝ) ≤ M := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
      have hbern := one_add_mul_sub_le_pow (a := q) (by linarith) k
      have hnonneg : 0 ≤ ((M : ℝ) - k) * (1 - q) :=
        mul_nonneg (sub_nonneg.mpr hkM) (sub_nonneg.mpr hq1)
      nlinarith

lemma chosenRadius_bounds {M : ℕ} (hM : 2 ≤ M) :
    1 / 2 ≤ chosenRadius M ∧ chosenRadius M < 1 := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hxpow : (2 : ℝ) ^ 13 ≤ (M : ℝ) ^ 13 :=
    pow_le_pow_left₀ (by norm_num) hx 13
  have hxp : 0 < (M : ℝ) ^ 13 := by positivity
  have ht : 1 / (M : ℝ) ^ 13 ≤ 1 / 2 := by
    rw [div_le_iff₀ hxp]
    norm_num at hxpow ⊢
    linarith
  have htpos : 0 < 1 / (M : ℝ) ^ 13 := by positivity
  constructor <;> simp only [chosenRadius] <;> linarith

lemma chosenRadius_sq_gap {M : ℕ} (hM : 2 ≤ M) :
    1 / (M : ℝ) ^ 13 ≤ 1 - chosenRadius M ^ 2 ∧
      1 - chosenRadius M ^ 2 ≤ 2 / (M : ℝ) ^ 13 := by
  have hb := chosenRadius_bounds hM
  have ht : 1 / (M : ℝ) ^ 13 = 1 - chosenRadius M := by
    simp [chosenRadius]
  constructor
  · rw [ht]
    have hr0 : 0 ≤ chosenRadius M := by linarith [hb.1]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hb.2.le)]
  · have ht2 : 2 / (M : ℝ) ^ 13 = 2 * (1 - chosenRadius M) := by
      rw [← ht]
      ring
    rw [ht2]
    nlinarith [sq_nonneg (1 - chosenRadius M)]

lemma chosenRadius_block_close {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) * (1 - chosenRadius M ^ 2) ≤ 1 / 2 := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hxp : 0 < (M : ℝ) := by linarith
  have hx12 : (2 : ℝ) ^ 12 ≤ (M : ℝ) ^ 12 :=
    pow_le_pow_left₀ (by norm_num) hx 12
  calc
    (M : ℝ) * (1 - chosenRadius M ^ 2) ≤
        (M : ℝ) * (2 / (M : ℝ) ^ 13) :=
      mul_le_mul_of_nonneg_left (chosenRadius_sq_gap hM).2 hxp.le
    _ ≤ 1 / 2 := by
      field_simp
      nlinarith [hx12]

lemma chosenRadius_kernel_bound {M : ℕ} (hM : 2 ≤ M) :
    2 * Real.log (1 - chosenRadius M)⁻¹ + 1 / 2 ≤ 27 * M := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hxp : 0 < (M : ℝ) := by linarith
  have hinv : (1 - chosenRadius M)⁻¹ = (M : ℝ) ^ 13 := by
    simp only [chosenRadius]
    field_simp
    ring
  rw [hinv, Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos hxp
  norm_num at hlog ⊢
  nlinarith

lemma chosenRadius_error_bound {D : ℝ} {M : ℕ} (hD : 0 ≤ D) (hM : 2 ≤ M) :
    (((D + 1) * (M : ℝ) ^ 6)⁻¹) *
        (D ^ 2 / (1 - chosenRadius M ^ 2)) ≤ D * (M : ℝ) ^ 7 := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hxp : 0 < (M : ℝ) := by linarith
  have ht : 0 < 1 / (M : ℝ) ^ 13 := by positivity
  have hden := (chosenRadius_sq_gap hM).1
  have hdenpos : 0 < 1 - chosenRadius M ^ 2 := lt_of_lt_of_le ht hden
  have hfrac : D ^ 2 / (1 - chosenRadius M ^ 2) ≤ D ^ 2 * (M : ℝ) ^ 13 := by
    calc
      D ^ 2 / (1 - chosenRadius M ^ 2) ≤ D ^ 2 / (1 / (M : ℝ) ^ 13) :=
        div_le_div_of_nonneg_left (sq_nonneg D) ht hden
      _ = D ^ 2 * (M : ℝ) ^ 13 := by field_simp
  have halpha : 0 < (D + 1) * (M : ℝ) ^ 6 :=
    mul_pos (by linarith) (pow_pos hxp _)
  calc
    ((D + 1) * (M : ℝ) ^ 6)⁻¹ * (D ^ 2 / (1 - chosenRadius M ^ 2)) ≤
        ((D + 1) * (M : ℝ) ^ 6)⁻¹ * (D ^ 2 * (M : ℝ) ^ 13) :=
      mul_le_mul_of_nonneg_left hfrac (inv_nonneg.mpr halpha.le)
    _ = (D ^ 2 / (D + 1)) * (M : ℝ) ^ 7 := by field_simp
    _ ≤ D * (M : ℝ) ^ 7 := by
      have hcoef : D ^ 2 / (D + 1) ≤ D := by
        rw [div_le_iff₀ (by linarith : 0 < D + 1)]
        nlinarith
      exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg hxp.le _)

lemma block_circle_upper_chosen {A : Set ℕ} {c D : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D)
    (he : ∀ n, ‖summatoryError A c n‖ ≤ D) {M : ℕ} (hM : 2 ≤ M) :
    Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((chosenRadius M : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((chosenRadius M : ℂ) * z)‖ ^ 2) 0 1 ≤
      (27 * c + 2 * D + 1) * (M : ℝ) ^ 7 := by
  have hb := chosenRadius_bounds hM
  have hupper := block_circle_upper hc hD he
    (mul_pos (by linarith : 0 < D + 1) (pow_pos (by
      have : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hM)
      exact this) 6)) hb.1 hb.2 M
    (α := (D + 1) * (M : ℝ) ^ 6)
  have hx : (1 : ℝ) ≤ M := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hM)
  have hx0 : (0 : ℝ) ≤ M := hx.trans' zero_le_one
  have hpow37 : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 7 :=
    pow_le_pow_right₀ hx (by norm_num)
  have hsing :
      c * (M : ℝ) ^ 2 * (2 * Real.log (1 - chosenRadius M)⁻¹ + 1 / 2) ≤
        27 * c * (M : ℝ) ^ 7 := by
    calc
      c * (M : ℝ) ^ 2 * (2 * Real.log (1 - chosenRadius M)⁻¹ + 1 / 2) ≤
          c * (M : ℝ) ^ 2 * (27 * (M : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (chosenRadius_kernel_bound hM)
          (mul_nonneg hc (pow_nonneg hx0 _))
      _ = 27 * c * (M : ℝ) ^ 3 := by ring
      _ ≤ 27 * c * (M : ℝ) ^ 7 :=
        mul_le_mul_of_nonneg_left hpow37 (mul_nonneg (by norm_num) hc)
  have halpha : ((D + 1) * (M : ℝ) ^ 6) * M =
      (D + 1) * (M : ℝ) ^ 7 := by ring
  calc
    Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((chosenRadius M : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((chosenRadius M : ℂ) * z)‖ ^ 2) 0 1 ≤
      c * M ^ 2 * (2 * Real.log (1 - chosenRadius M)⁻¹ + 1 / 2) +
        ((D + 1) * (M : ℝ) ^ 6) * M +
          ((D + 1) * (M : ℝ) ^ 6)⁻¹ *
            (D ^ 2 / (1 - chosenRadius M ^ 2)) := hupper
    _ ≤ 27 * c * (M : ℝ) ^ 7 + (D + 1) * (M : ℝ) ^ 7 +
        D * (M : ℝ) ^ 7 := by
      nlinarith [hsing, chosenRadius_error_bound hD hM, halpha]
    _ = (27 * c + 2 * D + 1) * (M : ℝ) ^ 7 := by ring

lemma block_circle_lower_chosen {A : Set ℕ} {c D L : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (he : ∀ n, ‖summatoryError A c n‖ ≤ D) {M : ℕ} (hM : 2 ≤ M)
    (hlarge : 2 * (L ^ 2 + D) ≤ c * M) :
    (L / 2) * (M : ℝ) ^ 7 ≤
      Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((chosenRadius M : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((chosenRadius M : ℂ) * z)‖ ^ 2) 0 1 := by
  let r := chosenRadius M
  let q := r ^ 2
  have hb := chosenRadius_bounds hM
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith [hb.1]
  have hrpos : 0 < r := by dsimp only [r]; linarith [hb.1]
  have hr1 : r < 1 := by simpa only [r] using hb.2
  have hq0 : 0 ≤ q := sq_nonneg r
  have hq1 : q < 1 := by
    dsimp only [q]
    nlinarith [mul_pos hrpos (sub_pos.mpr hr1)]
  have hH : (M : ℝ) / 2 ≤ ∑ k ∈ Finset.range M, q ^ k := by
    apply geometricBlock_real_lower M hq0 hq1.le
    simpa [q, r] using chosenRadius_block_close hM
  have hx : (1 : ℝ) ≤ M := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hM)
  have hxp : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hx
  have hx12 : (1 : ℝ) ≤ (M : ℝ) ^ 12 := by
    simpa using pow_le_pow_left₀ zero_le_one hx 12
  have hgapUpper : 1 - q ≤ 2 / (M : ℝ) ^ 13 := by
    simpa [q, r] using (chosenRadius_sq_gap hM).2
  have hgapPos : 0 < 1 - q := sub_pos.mpr hq1
  have hmain : c * (M : ℝ) ^ 13 / 2 ≤ c / (1 - q) := by
    rw [le_div_iff₀ hgapPos]
    calc
      c * (M : ℝ) ^ 13 / 2 * (1 - q) ≤
          c * (M : ℝ) ^ 13 / 2 * (2 / (M : ℝ) ^ 13) :=
        mul_le_mul_of_nonneg_left hgapUpper (by positivity)
      _ = c := by field_simp
  have hscale : (L ^ 2 + D) * (M : ℝ) ^ 12 ≤ c * (M : ℝ) ^ 13 / 2 := by
    have hbase : L ^ 2 + D ≤ c * (M : ℝ) / 2 := by
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa [mul_comm] using hlarge)
    calc
      (L ^ 2 + D) * (M : ℝ) ^ 12 ≤
          (c * (M : ℝ) / 2) * (M : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg hxp.le _)
      _ = c * (M : ℝ) ^ 13 / 2 := by ring
  have hDscale : D ≤ D * (M : ℝ) ^ 12 := by
    nlinarith [mul_le_mul_of_nonneg_left hx12 hD]
  have htarget : L ^ 2 * (M : ℝ) ^ 12 ≤ c / (1 - q) - D := by
    nlinarith [hmain, hscale, hDscale]
  have hFsq := indicatorSeriesReal_sq_lower hc hD he hq0 hq1
  have hF : L * (M : ℝ) ^ 6 ≤ indicatorSeriesReal A q := by
    have hF0 := indicatorSeriesReal_nonneg A hq0
    have htarget0 : 0 ≤ L * (M : ℝ) ^ 6 :=
      mul_nonneg hL (pow_nonneg hxp.le _)
    have hsquares : (L * (M : ℝ) ^ 6) ^ 2 ≤ (indicatorSeriesReal A q) ^ 2 := by
      calc
        (L * (M : ℝ) ^ 6) ^ 2 = L ^ 2 * (M : ℝ) ^ 12 := by ring
        _ ≤ c / (1 - q) - D := htarget
        _ ≤ (indicatorSeriesReal A q) ^ 2 := hFsq
    nlinarith [sq_nonneg (indicatorSeriesReal A q - L * (M : ℝ) ^ 6)]
  have hlower := block_parseval_lower (A := A) M hr0 hb.2
  calc
    (L / 2) * (M : ℝ) ^ 7 = ((M : ℝ) / 2) * (L * (M : ℝ) ^ 6) := by ring
    _ ≤ (∑ k ∈ Finset.range M, q ^ k) * indicatorSeriesReal A q := by
      apply mul_le_mul hH hF
      · exact mul_nonneg hL (pow_nonneg hxp.le _)
      · exact Finset.sum_nonneg fun k _ ↦ pow_nonneg hq0 k
    _ ≤ Real.circleAverage
        (fun z : ℂ ↦ ‖geometricBlock M ((r : ℂ) * z) *
          powerSeriesValue (indicatorComplex A) ((r : ℂ) * z)‖ ^ 2) 0 1 := by
      simpa [q, indicatorSeriesReal] using hlower

/-! ## Resolution of Erdős Problem 763 -/

/-- **Erdős Problem 763 (Erdős--Fuchs).**  No subset of the natural numbers has an
ordered two-fold representation function whose summatory function differs from `cN` by a
bounded amount for a positive constant `c`. -/
theorem erdos_763 :
    ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
      (fun N : ℕ ↦ (summatoryRepresentationCount A N : ℝ) - c * N) =O[atTop]
        (fun _N : ℕ ↦ (1 : ℝ)) := by
  rintro ⟨A, c, hc, hbounded⟩
  obtain ⟨D, hD, he⟩ := summatoryError_bounded_of_isBigO hbounded
  let L : ℝ := 2 * (27 * c + 2 * D + 2)
  have hL : 0 < L := by
    dsimp only [L]
    nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt (max 2 (2 * (L ^ 2 + D) / c))
  have hM2 : 2 ≤ M := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hM))
  have hlarge : 2 * (L ^ 2 + D) ≤ c * M := by
    have hratio : 2 * (L ^ 2 + D) / c < (M : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hM
    have hmul := (div_lt_iff₀ hc).mp hratio
    nlinarith
  have hlower := block_circle_lower_chosen hc hD hL.le he hM2 hlarge
  have hupper := block_circle_upper_chosen hc.le hD he hM2
  have hpow : 0 < (M : ℝ) ^ 7 := by
    positivity
  have hboth : (L / 2) * (M : ℝ) ^ 7 ≤
      (27 * c + 2 * D + 1) * (M : ℝ) ^ 7 := hlower.trans hupper
  dsimp only [L] at hboth
  nlinarith

#print axioms erdos_763

end Erdos763

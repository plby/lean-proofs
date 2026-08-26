/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.FiniteBetaProductRatio

/-!
# The numerical beta-sieve estimate through dimension nine

The reusable beta-sieve combinatorics in `Erdos851` is stated with a final
numerical specialization to dimensions at most two.  This file proves the
corresponding numerical estimate needed for the affine forms in
Erdos 946.  No sieve or number-theoretic input occurs here.
-/

namespace Erdos946.DimensionEightBeta

open Erdos851
open Erdos851.BetaSieveFundamental
open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteRecursiveBridge
open List

/-- For `0 ≤ κ ≤ 9`, the beta-100 product-ratio loss is at most `6/5` per
chain coordinate. -/
theorem betaRatio_rpow_dimension_le_six_fifths {κ : ℝ}
    (_hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9) :
    Real.rpow betaRatio κ ≤ 6 / 5 := by
  calc
    Real.rpow betaRatio κ ≤ Real.rpow betaRatio (9 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num [betaRatio]) hκ8
    _ = betaRatio ^ (9 : ℕ) := Real.rpow_natCast _ _
    _ ≤ 6 / 5 := by norm_num [betaRatio]

theorem betaRatio_rpow_dimension_mul_le_eight {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9) (r : ℕ) :
    Real.rpow betaRatio (κ * r) ≤ (6 / 5 : ℝ) ^ r := by
  calc
    Real.rpow betaRatio (κ * r) = (Real.rpow betaRatio κ) ^ r :=
      Real.rpow_mul_natCast (by norm_num [betaRatio]) κ r
    _ ≤ (6 / 5 : ℝ) ^ r := pow_le_pow_left₀
      (Real.rpow_nonneg (by norm_num [betaRatio]) _)
      (betaRatio_rpow_dimension_le_six_fifths hκ0 hκ8) r

/-- In sieve dimension at most nine, the stronger cutoff condition
`log A ≤ κ r / 99` makes the full depth majorant geometrically decreasing
with ratio `9/10`.

This is the same calculation as the dimension-two `1/4` estimate in
`Erdos851`, with the exact rational inequalities adjusted to dimension
eight. -/
theorem betaDepthMajorant_le_four_fifths_pow
    {A κ : ℝ} (r : ℕ) (hA : 1 ≤ A)
    (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9)
    (hlogA : Real.log A ≤ κ * r / 99) :
    betaDepthMajorant A κ r ≤ A * (9 / 10 : ℝ) ^ r := by
  have hlogc0 : 0 ≤ Real.log betaRatio :=
    Real.log_nonneg (by norm_num [betaRatio])
  have hkr0 : 0 ≤ κ * (r : ℝ) := mul_nonneg hκ0 (by positivity)
  have hlogterm :
      κ * (r : ℝ) * Real.log betaRatio ≤ 2 * κ * (r : ℝ) / 99 := by
    calc
      κ * (r : ℝ) * Real.log betaRatio ≤
          κ * (r : ℝ) * (2 / 99) :=
        mul_le_mul_of_nonneg_left log_betaRatio_le hkr0
      _ = 2 * κ * (r : ℝ) / 99 := by ring
  have hbase0 : 0 ≤
      Real.log A + κ * (r : ℝ) * Real.log betaRatio :=
    add_nonneg (Real.log_nonneg hA) (mul_nonneg hkr0 hlogc0)
  have hbase : Real.log A + κ * (r : ℝ) * Real.log betaRatio ≤
      3 * κ * (r : ℝ) / 99 := by linarith
  have hpowbase :
      (Real.log A + κ * (r : ℝ) * Real.log betaRatio) ^ r ≤
        (3 * κ * (r : ℝ) / 99) ^ r :=
    pow_le_pow_left₀ hbase0 hbase r
  have hratio := betaRatio_rpow_dimension_mul_le_eight hκ0 hκ8 r
  have hfac := self_pow_div_factorial_le_eleven_quarters_pow r
  have hA0 : 0 ≤ A := hA.trans' (by norm_num)
  have hpowers :
      (6 / 5 : ℝ) ^ r * (3 * κ * (r : ℝ) / 99) ^ r =
        (2 * κ / 55 : ℝ) ^ r * (r : ℝ) ^ r := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  have hpowers' :
      (2 * κ / 55 : ℝ) ^ r * (11 / 4 : ℝ) ^ r =
        (κ / 10 : ℝ) ^ r := by
    rw [← mul_pow]
    congr 1
    ring
  have hbaseFourFifths : (κ / 10 : ℝ) ≤ 9 / 10 := by linarith
  have hbaseFinal0 : 0 ≤ (κ / 10 : ℝ) := by positivity
  unfold betaDepthMajorant
  calc
    A * Real.rpow betaRatio (κ * ↑r) *
          (Real.log A + κ * ↑r * Real.log betaRatio) ^ r /
          ↑r.factorial ≤
        A * (6 / 5 : ℝ) ^ r * (3 * κ * (r : ℝ) / 99) ^ r /
          (r.factorial : ℝ) := by
      gcongr
    _ = A * (2 * κ / 55 : ℝ) ^ r *
          ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      rw [mul_assoc, hpowers]
      ring
    _ ≤ A * (2 * κ / 55 : ℝ) ^ r * (11 / 4 : ℝ) ^ r := by
      gcongr
    _ = A * (κ / 10 : ℝ) ^ r := by
      rw [mul_assoc, hpowers']
    _ ≤ A * (9 / 10 : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbaseFinal0 hbaseFourFifths r) hA0

/-- A finite tail of powers of `9/10`, starting at `s`, is at most ten
times its first term. -/
theorem sum_four_fifths_pow_add_le (s m : ℕ) :
    (∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ (s + i)) ≤
      10 * (9 / 10 : ℝ) ^ s := by
  have hsum :
      (∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ i) ≤ 10 := by
    calc
      (∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ i) ≤
          ∑' i : ℕ, (9 / 10 : ℝ) ^ i := by
        exact (summable_geometric_of_norm_lt_one (by norm_num :
          ‖(9 / 10 : ℝ)‖ < 1)).sum_le_tsum (Finset.range m)
            (fun i _hi => by positivity)
      _ = (1 - (9 / 10 : ℝ))⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)
      _ = 10 := by norm_num
  calc
    (∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ (s + i)) =
        (9 / 10 : ℝ) ^ s * ∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ i := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ (9 / 10 : ℝ) ^ s * 10 := by gcongr
    _ = 10 * (9 / 10 : ℝ) ^ s := by ring

/-- Summed dimension-eight depth majorant. -/
theorem sum_betaDepthMajorant_le_eight
    {A κ : ℝ} (s m : ℕ) (hA : 1 ≤ A)
    (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9)
    (hlogA : ∀ i < m,
      Real.log A ≤ κ * (s + i : ℕ) / 99) :
    (∑ i ∈ Finset.range m, betaDepthMajorant A κ (s + i)) ≤
      10 * A * (9 / 10 : ℝ) ^ s := by
  calc
    (∑ i ∈ Finset.range m, betaDepthMajorant A κ (s + i)) ≤
        ∑ i ∈ Finset.range m, A * (9 / 10 : ℝ) ^ (s + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact betaDepthMajorant_le_four_fifths_pow (s + i) hA hκ0 hκ8
        (hlogA i (Finset.mem_range.mp hi))
    _ = A * ∑ i ∈ Finset.range m, (9 / 10 : ℝ) ^ (s + i) := by
      rw [Finset.mul_sum]
    _ ≤ A * (10 * (9 / 10 : ℝ) ^ s) := by
      gcongr
      exact sum_four_fifths_pow_add_le s m
    _ = 10 * A * (9 / 10 : ℝ) ^ s := by ring

/-- Dimension-eight version of the finite geometric first-failure bound. -/
theorem evalFailureTerms_le_geometric_eight
    {α : Type*} (x : α → ℝ)
    (terms : List (List α × List α))
    {V A κ : ℝ} {start fuel : ℕ}
    (hV : 0 ≤ V) (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9)
    (hlen : ∀ t ∈ terms, t.1.length ≤ fuel)
    (hratio : HasDepthProductRatio x terms V A κ start fuel)
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ κ * r / 99) :
    evalFailureTerms x terms ≤
      V * (10 * A * (9 / 10 : ℝ) ^ start) := by
  rw [← sum_depthFailureMass_eq_eval x terms fuel hlen]
  calc
    (∑ r ∈ Finset.range (fuel + 1), depthFailureMass x terms r) ≤
        ∑ r ∈ Finset.range (fuel + 1),
          if start ≤ r then V * betaDepthMajorant A κ r else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hratio r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    _ ≤ ∑ r ∈ Finset.range (fuel + 1),
          if start ≤ r then V * (A * (9 / 10 : ℝ) ^ r) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      split
      · gcongr
        exact betaDepthMajorant_le_four_fifths_pow r hA hκ0 hκ8
          (hlogA r (by assumption)
            (Nat.le_of_lt_succ (Finset.mem_range.mp hr)))
      · rfl
    _ = V * A * ∑ r ∈ Finset.Ico start (fuel + 1),
          (9 / 10 : ℝ) ^ r := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.range (fuel + 1)).filter (fun r => start ≤ r) =
            Finset.Ico start (fuel + 1) := by
        ext r
        simp [and_comm]
      rw [hfilter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ ≤ V * A * (10 * (9 / 10 : ℝ) ^ start) := by
      gcongr
      have hrewrite :
          (∑ r ∈ Finset.Ico start (fuel + 1), (9 / 10 : ℝ) ^ r) =
            ∑ i ∈ Finset.range (fuel + 1 - start),
              (9 / 10 : ℝ) ^ (start + i) := by
        rw [Finset.sum_Ico_eq_sum_range]
      rw [hrewrite]
      exact sum_four_fifths_pow_add_le start (fuel + 1 - start)
    _ = V * (10 * A * (9 / 10 : ℝ) ^ start) := by ring

/-- Prefix product-ratio estimates imply dimension-eight bounds for the
recursive Rosser main terms. -/
theorem rosserMainTerms_bounds_of_prefixProductRatio_eight
    {α : Type*} [DecidableEq α]
    (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P : List α}
    (upperCutoff lowerCutoff : ℕ → List α) {A κ : ℝ} {start : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hfuel : P.length ≤ fuel)
    (hupperPrefix : ∀ r ≤ fuel, upperCutoff r <+: P)
    (hlowerPrefix : ∀ r ≤ fuel, lowerCutoff r <+: P)
    (hupperChain : ∀ r ≤ fuel,
      ∀ t ∈ upperFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ upperCutoff r)
    (hlowerChain : ∀ r ≤ fuel,
      ∀ t ∈ lowerFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ lowerCutoff r)
    (hupperStart : ∀ t ∈ upperFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hlowerStart : ∀ t ∈ lowerFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9)
    (hupperProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (upperCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlowerProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (lowerCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ κ * r / 99) :
    let eta := 10 * A * (9 / 10 : ℝ) ^ start
    (1 - eta) * buchstabProduct x P ≤
        rosserLowerEval stop x fuel selected P ∧
      rosserUpperEval stop x fuel selected P ≤
        (1 + eta) * buchstabProduct x P := by
  dsimp only
  have huRatio := upper_hasDepthProductRatio_of_prefixProductRatio
    stop x fuel selected upperCutoff hx0 hx1 hPnodup rfl
    hupperPrefix hupperChain hupperStart hA hupperProduct
  have hlRatio := lower_hasDepthProductRatio_of_prefixProductRatio
    stop x fuel selected lowerCutoff hx0 hx1 hPnodup rfl
    hlowerPrefix hlowerChain hlowerStart hA hlowerProduct
  have hlength := failureTerms_length_bounds stop fuel selected P
  have hV : 0 ≤ buchstabProduct x P := by
    unfold buchstabProduct
    apply List.prod_nonneg
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact sub_nonneg.mpr (hx1 a ha).le
  have huEval := evalFailureTerms_le_geometric_eight x
    (upperFailureTerms stop fuel selected P)
    hV hA hκ0 hκ8
    (fun t ht => (hlength.1 t ht).2) huRatio hlogA
  have hlEval := evalFailureTerms_le_geometric_eight x
    (lowerFailureTerms stop fuel selected P)
    hV hA hκ0 hκ8
    (fun t ht => (hlength.2 t ht).2) hlRatio hlogA
  rw [(eval_failureTerms_eq_boundary stop x fuel selected P).1] at huEval
  rw [(eval_failureTerms_eq_boundary stop x fuel selected P).2] at hlEval
  obtain ⟨hupperEq, hlowerEq⟩ :=
    rosser_eval_sub_product_eq_boundary stop x fuel selected P hfuel
  constructor <;> linarith

/-- Increasing-list form used by the concrete finite sieve. -/
theorem finiteMainTerms_bounds_of_prefixProductRatio_eight
    (Astop : List ℕ → Prop) [DecidablePred Astop]
    (g : ℕ → ℝ) (P : List ℕ)
    (upperCutoff lowerCutoff : ℕ → List ℕ) {A κ : ℝ} {start : ℕ}
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p < 1)
    (hPnodup : P.Nodup)
    (hupperPrefix : ∀ r ≤ P.length, upperCutoff r <+: P.reverse)
    (hlowerPrefix : ∀ r ≤ P.length, lowerCutoff r <+: P.reverse)
    (hupperChain : ∀ r ≤ P.length,
      ∀ t ∈ upperFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
        t.1.length = r → t.1 <+ upperCutoff r)
    (hlowerChain : ∀ r ≤ P.length,
      ∀ t ∈ lowerFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
        t.1.length = r → t.1 <+ lowerCutoff r)
    (hupperStart : ∀ t ∈
        upperFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
      start ≤ t.1.length)
    (hlowerStart : ∀ t ∈
        lowerFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
      start ≤ t.1.length)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ8 : κ ≤ 9)
    (hupperProduct : ∀ r ≤ P.length, start ≤ r →
      (buchstabProduct g (upperCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlowerProduct : ∀ r ≤ P.length, start ≤ r →
      (buchstabProduct g (lowerCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlogA : ∀ r, start ≤ r → r ≤ P.length →
      Real.log A ≤ κ * r / 99) :
    let eta := 10 * A * (9 / 10 : ℝ) ^ start
    (1 - eta) * finiteEulerProduct g P ≤ lowerMainTerm Astop g P ∧
      upperMainTerm Astop g P ≤
        (1 + eta) * finiteEulerProduct g P := by
  have h := rosserMainTerms_bounds_of_prefixProductRatio_eight
    (fun s => decide (Astop s.reverse)) g P.length []
    upperCutoff lowerCutoff hg0
    (fun p hp => hg1 p (by simpa using hp))
    (by simpa using hPnodup : P.reverse.Nodup) (by simp)
    hupperPrefix hlowerPrefix hupperChain hlowerChain
    hupperStart hlowerStart hA hκ0 hκ8
    hupperProduct hlowerProduct hlogA
  rw [← lowerMainTerm_eq_rosserLowerEval Astop g P,
    ← upperMainTerm_eq_rosserUpperEval Astop g P] at h
  simpa [finiteEulerProduct, buchstabProduct, List.map_reverse] using h

end Erdos946.DimensionEightBeta

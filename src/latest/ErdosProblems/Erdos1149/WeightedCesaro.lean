/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Weighted Cesàro transfer

This file records the real-variable summation-by-parts argument used in the
sublinear part of Erdős Problem 1149.  An ordinary Cesàro limit is unchanged
by nonnegative increasing weights, provided the last weight has controlled
size relative to the total weight.
-/

namespace Erdos1149

open Filter
open scoped BigOperators

noncomputable section

/-- Total mass of the first `N` weights. -/
def weightPrefix (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w n

/-- Weighted sum of the first `N` values. -/
def weightedPrefix (w q : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w n * q n

/-- Finite summation by parts, with the first unused weight as boundary term. -/
lemma weightedCesaro_sum_by_parts_unused (w f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, w n * f n) =
      w N * (∑ n ∈ Finset.range N, f n) +
        ∑ n ∈ Finset.range N,
          (w n - w (n + 1)) *
            (∑ j ∈ Finset.range (n + 1), f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hsum : (∑ n ∈ Finset.range (N + 1), f n) =
          (∑ n ∈ Finset.range N, f n) + f N := by
        rw [Finset.sum_range_succ]
      rw [hsum]
      ring

/-- Finite summation by parts, with the last used weight as boundary term. -/
lemma weightedCesaro_sum_by_parts (w f : ℕ → ℝ) (N : ℕ) :
    weightedPrefix w f (N + 1) =
      w N * (∑ n ∈ Finset.range (N + 1), f n) -
        ∑ n ∈ Finset.range N,
          (w (n + 1) - w n) *
            (∑ j ∈ Finset.range (n + 1), f j) := by
  change (∑ n ∈ Finset.range (N + 1), w n * f n) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    weightedCesaro_sum_by_parts_unused]
  have hneg :
      (∑ n ∈ Finset.range N,
          (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), f j)) =
        -∑ n ∈ Finset.range N,
          (w (n + 1) - w n) * (∑ j ∈ Finset.range (n + 1), f j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hneg]
  ring

/-- Telescoping sum of consecutive weight differences. -/
lemma weightedCesaro_sum_weight_differences (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (w (n + 1) - w n) = w N - w 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Increment weights associated with the inverse-power blocks. -/
def rpowIncrementWeight (beta : ℝ) (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) ^ beta - (m : ℝ) ^ beta

lemma rpowIncrementWeight_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) (m : ℕ) :
    0 ≤ rpowIncrementWeight beta m := by
  unfold rpowIncrementWeight
  exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg m)
    (by norm_num) hbeta)

lemma rpowIncrementWeight_mono {beta : ℝ} (hbeta : 1 ≤ beta) :
    Monotone (rpowIncrementWeight beta) := by
  apply monotone_nat_of_le_succ
  intro m
  have hslope := (convexOn_rpow hbeta).slope_mono_adjacent
    (x := (m : ℝ)) (y := (m + 1 : ℕ)) (z := (m + 2 : ℕ))
    (by simp) (by
      show (0 : ℝ) ≤ (m + 2 : ℕ)
      exact_mod_cast (Nat.zero_le (m + 2))) (by norm_num) (by norm_num)
  unfold rpowIncrementWeight
  norm_num at hslope ⊢
  have heq : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
  rw [heq]
  linarith

lemma weightPrefix_rpowIncrementWeight {beta : ℝ} (hbeta : 0 < beta) (N : ℕ) :
    weightPrefix (rpowIncrementWeight beta) N = (N : ℝ) ^ beta := by
  unfold weightPrefix
  induction N with
  | zero => simp [Real.zero_rpow hbeta.ne']
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold rpowIncrementWeight
      ring

lemma rpowIncrementWeight_le_deriv {beta : ℝ}
    (hbeta : 1 ≤ beta) (N : ℕ) :
    rpowIncrementWeight beta N ≤
      beta * (((N + 1 : ℕ) : ℝ) ^ (beta - 1)) := by
  have hslope := (convexOn_rpow hbeta).slope_le_of_hasDerivAt
    (x := (N : ℝ)) (y := ((N + 1 : ℕ) : ℝ))
    (by simp) (by
      show (0 : ℝ) ≤ (N + 1 : ℕ)
      exact_mod_cast Nat.zero_le (N + 1)) (by norm_num)
    (Real.hasDerivAt_rpow_const (Or.inr hbeta))
  unfold rpowIncrementWeight
  simpa [slope, div_eq_mul_inv] using hslope

lemma succ_mul_rpowIncrementWeight_div_rpow_le {beta : ℝ}
    (hbeta : 1 ≤ beta) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) * rpowIncrementWeight beta N /
        (((N + 1 : ℕ) : ℝ) ^ beta) ≤ beta := by
  have hw := rpowIncrementWeight_le_deriv hbeta N
  have hbase : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hpow : (0 : ℝ) < (((N + 1 : ℕ) : ℝ) ^ beta) :=
    Real.rpow_pos_of_pos hbase _
  calc
    ((N + 1 : ℕ) : ℝ) * rpowIncrementWeight beta N /
        (((N + 1 : ℕ) : ℝ) ^ beta) ≤
      ((N + 1 : ℕ) : ℝ) *
          (beta * (((N + 1 : ℕ) : ℝ) ^ (beta - 1))) /
        (((N + 1 : ℕ) : ℝ) ^ beta) := by
          gcongr
    _ = beta := by
      rw [Real.rpow_sub_one hbase.ne']
      field_simp

/-- A generic weighted-Cesàro theorem for increasing nonnegative weights.

The boundary hypothesis is deliberately stated with the first unused prefix:
`(N+1) * w N / W (N+1) ≤ B`.  It is exactly what summation by parts needs.
-/
theorem tendsto_weightedAverage_of_tendsto_cesaro
    (w q : ℕ → ℝ) (L : ℝ)
    (hq : Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.range N, q n) / (N : ℝ))
      atTop (nhds L))
    (hw0 : ∀ n, 0 ≤ w n)
    (hwmono : Monotone w)
    (hWtop : Tendsto (weightPrefix w) atTop atTop)
    (hboundary : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ((N + 1 : ℕ) : ℝ) * w N / weightPrefix w (N + 1) ≤ B) :
    Tendsto
      (fun N : ℕ ↦ weightedPrefix w q N / weightPrefix w N)
      atTop (nhds L) := by
  obtain ⟨B, hB0, hB⟩ := hboundary
  let e : ℕ → ℝ := fun n ↦ q n - L
  let A : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.range N, e n
  have hcenter : Tendsto (fun N : ℕ ↦ A N / (N : ℝ)) atTop (nhds 0) := by
    have hsub : Tendsto
        (fun N : ℕ ↦ (∑ n ∈ Finset.range N, q n) / (N : ℝ) - L)
        atTop (nhds 0) := by
      simpa using hq.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L) atTop (nhds L))
    apply hsub.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun N hN ↦ hN⟩] with N hN
    simp only [A, e, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  have hshift : Tendsto
      (fun N : ℕ ↦ weightedPrefix w q (N + 1) /
        weightPrefix w (N + 1)) atTop (nhds L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / (4 * (B + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨K, hKraw⟩ := (Metric.tendsto_atTop.1 hcenter) δ hδ
    have hK : ∀ N ≥ K, |A N / (N : ℝ)| < δ := by
      intro N hN
      simpa only [Real.dist_eq, sub_zero] using hKraw N hN
    let C : ℝ := ∑ n ∈ Finset.range K,
      (w (n + 1) - w n) * |A (n + 1)|
    have hC0 : 0 ≤ C := by
      dsimp [C]
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (sub_nonneg.mpr (hwmono (Nat.le_succ n)))
        (abs_nonneg _)
    have hCevent : ∀ᶠ N : ℕ in atTop,
        C / weightPrefix w (N + 1) < ε / 2 := by
      have ht : Tendsto
          (fun N : ℕ ↦ C / weightPrefix w (N + 1))
          atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (hWtop.comp (tendsto_add_atTop_nat 1))
      obtain ⟨K', hK'⟩ := (Metric.tendsto_atTop.1 ht) (ε / 2) (half_pos hε)
      refine eventually_atTop.2 ⟨K', fun N hN ↦ ?_⟩
      have hval := hK' N hN
      rw [Real.dist_eq, sub_zero] at hval
      exact (le_abs_self (C / weightPrefix w (N + 1))).trans_lt hval
    obtain ⟨K', hK'⟩ := eventually_atTop.1 hCevent
    have hWpositive : ∀ᶠ N : ℕ in atTop, 0 < weightPrefix w (N + 1) := by
      have hevent : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < weightPrefix w N :=
        hWtop.eventually (eventually_gt_atTop 0)
      exact (hWtop.comp (tendsto_add_atTop_nat 1)).eventually
        (eventually_gt_atTop 0)
    obtain ⟨K'', hK''⟩ := eventually_atTop.1 hWpositive
    refine ⟨max K (max K' K''), fun N hN ↦ ?_⟩
    have hNK : K ≤ N := (le_max_left K (max K' K'')).trans hN
    have hNK' : K ≤ N + 1 := hNK.trans (Nat.le_succ N)
    have hCN := hK' N ((le_max_left K' K'').trans
      ((le_max_right K (max K' K'')).trans hN))
    have hWpos := hK'' N ((le_max_right K' K'').trans
      ((le_max_right K (max K' K'')).trans hN))
    have hAN : |A (N + 1)| < δ * (N + 1 : ℕ) := by
      have hraw := hK (N + 1) hNK'
      have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      rw [abs_div, abs_of_pos hpos] at hraw
      exact (div_lt_iff₀ hpos).mp hraw
    have hsum :
        ∑ n ∈ Finset.range N,
            (w (n + 1) - w n) * |A (n + 1)| ≤
          C + δ * (N + 1 : ℕ) * w N := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun n ↦ n < K)]
      apply add_le_add
      · dsimp [C]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact hn.2
        · intro n hnN hnnot
          exact mul_nonneg (sub_nonneg.mpr (hwmono (Nat.le_succ n)))
            (abs_nonneg _)
      · calc
          ∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
              (w (n + 1) - w n) * |A (n + 1)| ≤
            ∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
              (w (n + 1) - w n) * (δ * (N + 1 : ℕ)) := by
                apply Finset.sum_le_sum
                intro n hn
                have hnK : K ≤ n + 1 := by
                  simp only [Finset.mem_filter, Finset.mem_range] at hn
                  omega
                have hraw := hK (n + 1) hnK
                have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
                rw [abs_div, abs_of_pos hnpos] at hraw
                have hnle : (n + 1 : ℕ) ≤ N := by
                  simpa using (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
                have hAn : |A (n + 1)| ≤ δ * (N + 1 : ℕ) := by
                  calc
                    |A (n + 1)| ≤ δ * (n + 1 : ℕ) :=
                      ((div_lt_iff₀ hnpos).mp hraw).le
                    _ ≤ δ * (N + 1 : ℕ) := by
                      apply mul_le_mul_of_nonneg_left _ hδ.le
                      exact_mod_cast hnle.trans (Nat.le_succ N)
                exact mul_le_mul_of_nonneg_left hAn
                  (sub_nonneg.mpr (hwmono (Nat.le_succ n)))
          _ = δ * (N + 1 : ℕ) *
              (∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
                (w (n + 1) - w n)) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro n hn
                  ring
          _ ≤ δ * (N + 1 : ℕ) *
              (∑ n ∈ Finset.range N, (w (n + 1) - w n)) := by
                apply mul_le_mul_of_nonneg_left
                · apply Finset.sum_le_sum_of_subset_of_nonneg
                  · exact Finset.filter_subset _ _
                  · intro n hn hnnot
                    exact sub_nonneg.mpr (hwmono (Nat.le_succ n))
                · positivity
          _ ≤ δ * (N + 1 : ℕ) * w N := by
                rw [weightedCesaro_sum_weight_differences]
                gcongr
                exact sub_le_self _ (hw0 0)
    have habel := weightedCesaro_sum_by_parts w e N
    have hcenterBound :
        |weightedPrefix w e (N + 1)| ≤
          2 * δ * (N + 1 : ℕ) * w N + C := by
      rw [habel]
      calc
        |w N * A (N + 1) -
            ∑ n ∈ Finset.range N,
              (w (n + 1) - w n) * A (n + 1)| ≤
          w N * |A (N + 1)| +
            ∑ n ∈ Finset.range N,
              (w (n + 1) - w n) * |A (n + 1)| := by
                calc
                  _ ≤ |w N * A (N + 1)| +
                      |∑ n ∈ Finset.range N,
                        (w (n + 1) - w n) * A (n + 1)| := abs_sub _ _
                  _ ≤ w N * |A (N + 1)| +
                      ∑ n ∈ Finset.range N,
                        (w (n + 1) - w n) * |A (n + 1)| := by
                          rw [abs_mul, abs_of_nonneg (hw0 N)]
                          gcongr
                          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                          apply Finset.sum_le_sum
                          intro n hn
                          rw [abs_mul, abs_of_nonneg
                            (sub_nonneg.mpr (hwmono (Nat.le_succ n)))]
        _ ≤ w N * (δ * (N + 1 : ℕ)) +
            (C + δ * (N + 1 : ℕ) * w N) :=
          add_le_add (mul_le_mul_of_nonneg_left hAN.le (hw0 N)) hsum
        _ = 2 * δ * (N + 1 : ℕ) * w N + C := by ring
    rw [Real.dist_eq]
    have hrewrite :
        weightedPrefix w q (N + 1) / weightPrefix w (N + 1) - L =
          weightedPrefix w e (N + 1) / weightPrefix w (N + 1) := by
      calc
        weightedPrefix w q (N + 1) / weightPrefix w (N + 1) - L =
            (weightedPrefix w q (N + 1) -
              L * weightPrefix w (N + 1)) / weightPrefix w (N + 1) := by
                field_simp [hWpos.ne']
        _ = weightedPrefix w e (N + 1) / weightPrefix w (N + 1) := by
          congr 1
          simp only [weightedPrefix, e, mul_sub, Finset.sum_sub_distrib,
            ← Finset.sum_mul, weightPrefix]
          ring
    rw [hrewrite, abs_div, abs_of_pos hWpos]
    calc
      |weightedPrefix w e (N + 1)| / weightPrefix w (N + 1) ≤
          (2 * δ * (N + 1 : ℕ) * w N + C) /
            weightPrefix w (N + 1) :=
        div_le_div_of_nonneg_right hcenterBound hWpos.le
      _ = 2 * δ *
            (((N + 1 : ℕ) : ℝ) * w N / weightPrefix w (N + 1)) +
          C / weightPrefix w (N + 1) := by ring
      _ ≤ 2 * δ * B + C / weightPrefix w (N + 1) := by
        gcongr
        exact hB N
      _ < ε := by
        have hhalf : 2 * δ * B ≤ ε / 2 := by
          dsimp [δ]
          have hden : 0 < B + 1 := by linarith
          calc
            2 * (ε / (4 * (B + 1))) * B =
                (ε / 2) * (B / (B + 1)) := by
                  field_simp
                  ring
            _ ≤ ε / 2 := by
              apply mul_le_of_le_one_right (by positivity)
              exact (div_le_one hden).mpr (by linarith)
        linarith
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- Direct power-increment specialization of weighted Càsaro transfer. -/
theorem tendsto_rpowIncrementWeighted_of_tendsto_cesaro
    (q : ℕ → ℝ) (L beta : ℝ) (hbeta : 1 < beta)
    (hq : Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.range N, q n) / (N : ℝ))
      atTop (nhds L)) :
    Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.range N, rpowIncrementWeight beta n * q n) /
          ((N : ℝ) ^ beta))
      atTop (nhds L) := by
  have hWtop : Tendsto (weightPrefix (rpowIncrementWeight beta)) atTop atTop := by
    have hr : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ beta) atTop atTop :=
      (tendsto_rpow_atTop (lt_trans zero_lt_one hbeta)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)
    apply hr.congr'
    exact Filter.Eventually.of_forall fun N ↦
      (weightPrefix_rpowIncrementWeight (lt_trans zero_lt_one hbeta) N).symm
  have htransfer := tendsto_weightedAverage_of_tendsto_cesaro
    (rpowIncrementWeight beta) q L hq
    (rpowIncrementWeight_nonneg (lt_trans zero_lt_one hbeta).le)
    (rpowIncrementWeight_mono hbeta.le) hWtop
    ⟨beta, le_trans zero_le_one hbeta.le, fun N ↦ by
      rw [weightPrefix_rpowIncrementWeight (lt_trans zero_lt_one hbeta)]
      exact succ_mul_rpowIncrementWeight_div_rpow_le hbeta.le N⟩
  convert htransfer using 1
  · funext N
    rw [weightPrefix_rpowIncrementWeight (lt_trans zero_lt_one hbeta)]
    rfl

/-- Logarithmic endpoint errors are negligible compared with any strictly
higher real power of the endpoint. -/
theorem tendsto_nat_mul_log_div_rpow_zero {beta : ℝ} (hbeta : 1 < beta) :
    Tendsto
      (fun M : ℕ ↦ (M : ℝ) * Real.log (M : ℝ) / (M : ℝ) ^ beta)
      atTop (nhds 0) := by
  have hsmall : Tendsto
      (fun M : ℕ ↦ Real.log (M : ℝ) / (M : ℝ) ^ (beta - 1))
      atTop (nhds 0) := by
    have h :=
      (isLittleO_log_rpow_atTop (sub_pos.mpr hbeta)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun M : ℕ ↦ (M : ℝ)) atTop atTop)
    change Tendsto
      ((fun x : ℝ ↦ Real.log x / x ^ (beta - 1)) ∘
        (fun M : ℕ ↦ (M : ℝ))) atTop (nhds 0)
    exact h
  apply hsmall.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun M hM ↦ hM⟩] with M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.rpow_sub_one hMpos.ne']
  field_simp

/-- A single inverse-power block has negligible relative width. -/
theorem tendsto_rpow_terminal_width_div_zero (beta : ℝ) :
    Tendsto
      (fun M : ℕ ↦
        (((M + 1 : ℕ) : ℝ) ^ beta - (M : ℝ) ^ beta) /
          (M : ℝ) ^ beta)
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun M : ℕ ↦ (((M + 1 : ℕ) : ℝ) / (M : ℝ)))
      atTop (nhds 1) := by
    have h : Tendsto (fun M : ℕ ↦ (1 : ℝ) + 1 / (M : ℝ))
        atTop (nhds (1 + 0)) := (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun M : ℕ ↦ (1 : ℝ) / M) atTop (nhds 0)))
    have heq : (fun M : ℕ ↦ (1 : ℝ) + 1 / (M : ℝ)) =ᶠ[atTop]
        (fun M : ℕ ↦ (((M + 1 : ℕ) : ℝ) / (M : ℝ))) := by
      filter_upwards [eventually_atTop.2 ⟨1, fun M hM ↦ hM⟩] with M hM
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
      field_simp
      push_cast
      ring
    simpa only [add_zero] using h.congr' heq
  have hrpow : Tendsto
      (fun M : ℕ ↦ ((((M + 1 : ℕ) : ℝ) / (M : ℝ)) ^ beta))
      atTop (nhds 1) := by
    simpa using hratio.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  have hsub := hrpow.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  have heq :
      (fun M : ℕ ↦
        (((M + 1 : ℕ) : ℝ) ^ beta - (M : ℝ) ^ beta) /
          (M : ℝ) ^ beta) =ᶠ[atTop]
      (fun M : ℕ ↦ (((M + 1 : ℕ) : ℝ) / (M : ℝ)) ^ beta - 1) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun M hM ↦ hM⟩] with M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    rw [Real.div_rpow (by positivity) hMpos.le]
    field_simp
  simpa using hsub.congr' heq.symm

end

end Erdos1149

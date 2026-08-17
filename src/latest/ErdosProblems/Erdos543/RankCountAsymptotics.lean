/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.Asymptotics
import ErdosProblems.Erdos543.MomentBounds

/-!
# Uniform asymptotic bounds for the rank decomposition

This file turns the finite rank-counting envelopes into fixed power savings.
The truncation radius is `floor ((log N)^(1/3))`.  Every estimate below is
uniform in the natural moment order `r` below that radius.
-/

open Filter
open scoped Topology

namespace Erdos543

/-- The moment range used in the growing-order Bonferroni argument. -/
noncomputable def momentRadius (N : ℕ) : ℕ :=
  Nat.floor (Real.log (N : ℝ) ^ ((1 : ℝ) / 3))

/-- The subpolynomial factor which absorbs the number of possible spans and
the geometric loss from replacing `2^k - 1` by `2^k`. -/
noncomputable def rankEntropyEnvelope (r : ℕ) : ℝ :=
  (r : ℝ) * (2 : ℝ) ^ (r * r + r)

/-- The relative lower-rank-pattern error occurring in the full-rank term. -/
noncomputable def lowerRankPatternRelativeEnvelope
    (g : ℕ → ℝ) (N r : ℕ) : ℝ :=
  (r : ℝ) * (2 : ℝ) ^ (r * r) *
    ((2 : ℝ) ^ cutoffSize g N) ^ (r - 1) /
      (((2 : ℝ) ^ cutoffSize g N - 1) ^ r)

/-- The relative sharp low-rank contribution after division by the leading
factorial-moment term. -/
noncomputable def incidenceLowRankRelativeEnvelope
    (g : ℕ → ℝ) (N r : ℕ) : ℝ :=
  (r : ℝ) * (2 : ℝ) ^ (r * r) *
    ((3 : ℝ) / 4) ^ cutoffSize g N *
    (N : ℝ) / ((2 : ℝ) ^ cutoffSize g N - 1) *
    (((2 : ℝ) ^ cutoffSize g N /
      ((2 : ℝ) ^ cutoffSize g N - 1)) ^ (r - 1))

lemma log_three_eighths_le_neg_seven_fifths_log_two :
    Real.log ((3 : ℝ) / 8) ≤ -(7 / 5 : ℝ) * Real.log 2 := by
  have hpow : (2 : ℝ) ^ 7 < ((8 : ℝ) / 3) ^ 5 := by norm_num
  have hlog := Real.strictMonoOn_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ 7)
    (by positivity : (0 : ℝ) < ((8 : ℝ) / 3) ^ 5) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hinv : ((3 : ℝ) / 8) = ((8 : ℝ) / 3)⁻¹ := by norm_num
  rw [hinv, Real.log_inv]
  nlinarith

/-- Eventually the rounded cutoff is at least nine tenths of its logarithmic
main term.  This deliberately leaves ample room for an arbitrary
`o(log log N)` perturbation. -/
lemma eventually_nine_tenths_log_div_log_two_le_cutoffSize
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      (9 / 10 : ℝ) * Real.log (N : ℝ) / Real.log 2 ≤
        (cutoffSize g N : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < (1 : ℝ) / (10 * Real.log 2) := by positivity
  have hb := (isLittleO_log_of_tendsto_div hg).bound hc
  filter_upwards [hb,
      tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0),
      eventually_cutoffArgument_pos hg] with N hbound hlog harg
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog.le] at hbound
  have hgLower : -(1 / (10 * Real.log 2) * Real.log (N : ℝ)) ≤ g N :=
    (neg_le_of_abs_le hbound)
  have hgLower' := mul_le_mul_of_nonneg_right hgLower hlog2.le
  have hraw : (9 / 10 : ℝ) * Real.log (N : ℝ) / Real.log 2 ≤
      cutoffArgument g N := by
    rw [cutoffArgument]
    field_simp at hgLower' ⊢
    nlinarith
  exact hraw.trans (by
    rw [cutoffSize]
    exact Nat.le_ceil _)

/-- The Boolean cube at the cutoff contains at least `N^(9/10)` points. -/
lemma eventually_rpow_nine_tenths_le_pow_cutoff
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (9 / 10 : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_nine_tenths_log_div_log_two_le_cutoffSize hg,
      eventually_gt_atTop (0 : ℕ)] with N hcut hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hexp : (9 / 10 : ℝ) * Real.log (N : ℝ) ≤
      (cutoffSize g N : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hcut hlog2.le
    field_simp at this
    nlinarith
  calc
    (N : ℝ) ^ (9 / 10 : ℝ) =
        Real.exp ((9 / 10 : ℝ) * Real.log (N : ℝ)) := by
      rw [Real.rpow_def_of_pos hNreal]
      congr 1
      ring
    _ ≤ Real.exp ((cutoffSize g N : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr hexp
    _ = (2 : ℝ) ^ cutoffSize g N := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The sharp cube-intersection base supplies more than a full power of `N`
after the cutoff lower bound is inserted. -/
lemma eventually_three_eighths_pow_cutoff_le_rpow_neg
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      ((3 : ℝ) / 8) ^ cutoffSize g N ≤
        (N : ℝ) ^ (-(63 / 50 : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 < (3 / 8 : ℝ) := by norm_num
  filter_upwards [eventually_nine_tenths_log_div_log_two_le_cutoffSize hg,
      eventually_gt_atTop (0 : ℕ)] with N hcut hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcut' : (9 / 10 : ℝ) * Real.log (N : ℝ) ≤
      (cutoffSize g N : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hcut hlog2.le
    field_simp at this
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left
    log_three_eighths_le_neg_seven_fifths_log_two
    (Nat.cast_nonneg (cutoffSize g N) : (0 : ℝ) ≤ _)
  have hexp : (cutoffSize g N : ℝ) * Real.log (3 / 8 : ℝ) ≤
      (-(63 / 50 : ℝ)) * Real.log (N : ℝ) := by
    nlinarith
  calc
    ((3 : ℝ) / 8) ^ cutoffSize g N =
        Real.exp ((cutoffSize g N : ℝ) * Real.log (3 / 8 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    _ ≤ Real.exp ((-(63 / 50 : ℝ)) * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr hexp
    _ = (N : ℝ) ^ (-(63 / 50 : ℝ)) := by
      rw [Real.rpow_def_of_pos hNreal]
      congr 1
      ring

lemma eventually_log_rpow_two_thirds_le
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ ((2 : ℝ) / 3) ≤ c * Real.log (N : ℝ) := by
  have hb := (isLittleO_log_rpow_log_rpow_nat
    (a := (2 : ℝ) / 3) (b := 1) (by norm_num)).bound hc
  filter_upwards [hb,
      tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)] with N hN hlog
  have hlog0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hlog
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _),
    Real.rpow_one, Real.norm_of_nonneg hlog0] at hN
  exact hN

/-- Uniformly for `r ≤ floor ((log N)^(1/3))`, all span-counting and
denominator-loss factors are bounded by `N^(1/100)`. -/
lemma eventually_rankEntropyEnvelope_le_rpow
    : ∀ᶠ N : ℕ in atTop, ∀ r : ℕ,
      r ≤ momentRadius N →
      rankEntropyEnvelope r ≤ (N : ℝ) ^ (1 / 100 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < (1 : ℝ) / (300 * Real.log 2) := by positivity
  filter_upwards [eventually_log_rpow_two_thirds_le _ hc,
      tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop (0 : ℕ)] with N hsmall hlog hN
  intro r hr
  have hrad : (r : ℝ) ≤ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have hcast : (r : ℝ) ≤ (momentRadius N : ℝ) := by exact_mod_cast hr
    exact hcast.trans (by
      rw [momentRadius]
      exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hlog) _))
  have hrnonneg : (0 : ℝ) ≤ r := by positivity
  have hthird_nonneg : 0 ≤ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hsq : (Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) =
      Real.log (N : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hlog)]
    norm_num
  have hrsq : (r : ℝ) ^ 2 ≤
      Real.log (N : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← hsq]
    exact pow_le_pow_left₀ hrnonneg hrad 2
  have hthird_le : Real.log (N : ℝ) ^ ((1 : ℝ) / 3) ≤
      Real.log (N : ℝ) ^ ((2 : ℝ) / 3) := by
    exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hrexp : ((r * r + 2 * r : ℕ) : ℝ) * Real.log 2 ≤
      (1 / 100 : ℝ) * Real.log (N : ℝ) := by
    push_cast
    have : (r : ℝ) * r + 2 * r ≤
        3 * (Real.log (N : ℝ) ^ ((2 : ℝ) / 3)) := by
      nlinarith [hrsq, hrad.trans hthird_le]
    calc
      ((r : ℝ) * r + 2 * r) * Real.log 2 ≤
          (3 * Real.log (N : ℝ) ^ ((2 : ℝ) / 3)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right this hlog2.le
      _ ≤ (1 / 100 : ℝ) * Real.log (N : ℝ) := by
        have hs := mul_le_mul_of_nonneg_left hsmall
          (show (0 : ℝ) ≤ 3 * Real.log 2 by positivity)
        calc
          3 * Real.log (N : ℝ) ^ ((2 : ℝ) / 3) * Real.log 2 =
              (3 * Real.log 2) * Real.log (N : ℝ) ^ ((2 : ℝ) / 3) := by ring
          _ ≤ (3 * Real.log 2) *
              ((1 / (300 * Real.log 2)) * Real.log (N : ℝ)) := hs
          _ = (1 / 100 : ℝ) * Real.log (N : ℝ) := by
            field_simp
            ring
  have hnat : r ≤ 2 ^ r := Nat.le_of_lt r.lt_two_pow_self
  have hent : rankEntropyEnvelope r ≤
      (2 : ℝ) ^ (r * r + 2 * r) := by
    rw [rankEntropyEnvelope]
    norm_cast
    calc
      r * 2 ^ (r * r + r) ≤ 2 ^ r * 2 ^ (r * r + r) :=
        Nat.mul_le_mul_right _ hnat
      _ = 2 ^ (r * r + 2 * r) := by rw [← pow_add]; congr 1; omega
  refine hent.trans ?_
  calc
    (2 : ℝ) ^ (r * r + 2 * r) =
        Real.exp (((r * r + 2 * r : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp ((1 / 100 : ℝ) * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr hrexp
    _ = (N : ℝ) ^ (1 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
      congr 1
      ring

/-- The growing moment radius is eventually smaller than the number of
independent coordinates at the proposed cutoff. -/
lemma eventually_momentRadius_le_cutoffSize
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, momentRadius N ≤ cutoffSize g N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < (9 : ℝ) / (10 * Real.log 2) := by positivity
  filter_upwards [eventually_log_rpow_two_thirds_le _ hc,
      eventually_nine_tenths_log_div_log_two_le_cutoffSize hg,
      tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)]
      with N hsmall hcut hlog
  have hlog0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hlog
  have hradius : (momentRadius N : ℝ) ≤
      Real.log (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [momentRadius]
    exact Nat.floor_le (Real.rpow_nonneg hlog0 _)
  have hthird : Real.log (N : ℝ) ^ ((1 : ℝ) / 3) ≤
      Real.log (N : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hcoeff : (9 : ℝ) / (10 * Real.log 2) * Real.log (N : ℝ) =
      (9 / 10 : ℝ) * Real.log (N : ℝ) / Real.log 2 := by
    field_simp
  have hreal : (momentRadius N : ℝ) ≤ (cutoffSize g N : ℝ) := by
    calc
      (momentRadius N : ℝ) ≤ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) := hradius
      _ ≤ Real.log (N : ℝ) ^ ((2 : ℝ) / 3) := hthird
      _ ≤ (9 : ℝ) / (10 * Real.log 2) * Real.log (N : ℝ) := hsmall
      _ = (9 / 10 : ℝ) * Real.log (N : ℝ) / Real.log 2 := hcoeff
      _ ≤ (cutoffSize g N : ℝ) := hcut
  exact_mod_cast hreal

/-- Consequently the moment radius also fits inside the family of nonempty
coordinate subsets, whose cardinality is `2^k - 1`. -/
lemma eventually_momentRadius_le_nonemptyCube
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop,
      momentRadius N ≤ 2 ^ cutoffSize g N - 1 := by
  filter_upwards [eventually_momentRadius_le_cutoffSize hg] with N hN
  exact hN.trans (by
    have hlt : cutoffSize g N < 2 ^ cutoffSize g N :=
      (cutoffSize g N).lt_two_pow_self
    omega)

/-! ## Finite denominator estimates -/

lemma half_two_pow_le_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ k / 2 ≤ (2 : ℝ) ^ k - 1 := by
  have hq : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    norm_cast
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  linarith

lemma two_pow_sub_one_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < (2 : ℝ) ^ k - 1 := by
  have hq : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    norm_cast
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  linarith

lemma two_pow_div_sub_one_le_two {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1) ≤ 2 := by
  exact (div_le_iff₀ (two_pow_sub_one_pos hk)).2 (by
    have := half_two_pow_le_two_pow_sub_one hk
    nlinarith)

lemma inv_two_pow_sub_one_le_two_div {k : ℕ} (hk : 1 ≤ k) :
    1 / ((2 : ℝ) ^ k - 1) ≤ 2 / (2 : ℝ) ^ k := by
  have hq : 0 < (2 : ℝ) ^ k := by positivity
  rw [div_le_div_iff₀ (two_pow_sub_one_pos hk) hq]
  have := half_two_pow_le_two_pow_sub_one hk
  nlinarith

lemma sq_le_rankEntropyEnvelope {r : ℕ} :
    (r : ℝ) ^ 2 ≤ rankEntropyEnvelope r := by
  have hnat : r ≤ 2 ^ (r * r + r) := by
    exact (Nat.le_of_lt r.lt_two_pow_self).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  rw [rankEntropyEnvelope, pow_two]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnat) (Nat.cast_nonneg r)

/-- Algebraic form of the lower-rank pattern-count loss. -/
lemma lowerRankPatternRelativeEnvelope_le
    {g : ℕ → ℝ} {N r : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ cutoffSize g N) :
    lowerRankPatternRelativeEnvelope g N r ≤
      2 * rankEntropyEnvelope r / (2 : ℝ) ^ cutoffSize g N := by
  let q : ℝ := (2 : ℝ) ^ cutoffSize g N
  let D : ℝ := q - 1
  have hq : 0 < q := by positivity
  have hD : 0 < D := by
    simpa [q, D] using two_pow_sub_one_pos hk
  have hinv : 1 / D ≤ 2 / q := by
    simpa [q, D] using inv_two_pow_sub_one_le_two_div hk
  have hratio : q / D ≤ 2 := by
    simpa [q, D] using two_pow_div_sub_one_le_two hk
  have hratioPow : (q / D) ^ (r - 1) ≤ (2 : ℝ) ^ (r - 1) :=
    pow_le_pow_left₀ (div_nonneg hq.le hD.le) hratio (r - 1)
  have hpowmono : (2 : ℝ) ^ (r - 1) ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [lowerRankPatternRelativeEnvelope]
  change (r : ℝ) * 2 ^ (r * r) * q ^ (r - 1) / D ^ r ≤ _
  have hDpow : D ^ r = D ^ (r - 1) * D := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
  calc
    (r : ℝ) * 2 ^ (r * r) * q ^ (r - 1) / D ^ r =
        ((r : ℝ) * 2 ^ (r * r)) * (1 / D) * (q / D) ^ (r - 1) := by
      rw [hDpow, div_pow]
      field_simp
    _ ≤ ((r : ℝ) * 2 ^ (r * r)) * (2 / q) * (2 : ℝ) ^ (r - 1) := by
      gcongr
    _ ≤ ((r : ℝ) * 2 ^ (r * r)) * (2 / q) * (2 : ℝ) ^ r := by
      gcongr
    _ = 2 * rankEntropyEnvelope r / q := by
      rw [rankEntropyEnvelope, pow_add]
      ring

/-- Algebraic form of the sharp low-rank incidence loss. -/
lemma incidenceLowRankRelativeEnvelope_le
    {g : ℕ → ℝ} {N r : ℕ} (hk : 1 ≤ cutoffSize g N) :
    incidenceLowRankRelativeEnvelope g N r ≤
      2 * rankEntropyEnvelope r * (N : ℝ) *
        ((3 : ℝ) / 8) ^ cutoffSize g N := by
  let q : ℝ := (2 : ℝ) ^ cutoffSize g N
  let D : ℝ := q - 1
  have hq : 0 < q := by positivity
  have hD : 0 < D := by
    simpa [q, D] using two_pow_sub_one_pos hk
  have hinv : 1 / D ≤ 2 / q := by
    simpa [q, D] using inv_two_pow_sub_one_le_two_div hk
  have hratio : q / D ≤ 2 := by
    simpa [q, D] using two_pow_div_sub_one_le_two hk
  have hratioPow : (q / D) ^ (r - 1) ≤ (2 : ℝ) ^ (r - 1) :=
    pow_le_pow_left₀ (div_nonneg hq.le hD.le) hratio (r - 1)
  have hpowmono : (2 : ℝ) ^ (r - 1) ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)
  have hbase : (3 / 4 : ℝ) ^ cutoffSize g N / q =
      (3 / 8 : ℝ) ^ cutoffSize g N := by
    rw [show q = (2 : ℝ) ^ cutoffSize g N by rfl, ← div_pow]
    congr 1
    norm_num
  rw [incidenceLowRankRelativeEnvelope]
  change (r : ℝ) * 2 ^ (r * r) * (3 / 4 : ℝ) ^ cutoffSize g N *
      (N : ℝ) / D * (q / D) ^ (r - 1) ≤ _
  calc
    (r : ℝ) * 2 ^ (r * r) * (3 / 4 : ℝ) ^ cutoffSize g N *
        (N : ℝ) / D * (q / D) ^ (r - 1) =
        ((r : ℝ) * 2 ^ (r * r)) * (3 / 4 : ℝ) ^ cutoffSize g N *
          (N : ℝ) * (1 / D) * (q / D) ^ (r - 1) := by ring
    _ ≤ ((r : ℝ) * 2 ^ (r * r)) * (3 / 4 : ℝ) ^ cutoffSize g N *
          (N : ℝ) * (2 / q) * (2 : ℝ) ^ (r - 1) := by
      gcongr
    _ ≤ ((r : ℝ) * 2 ^ (r * r)) * (3 / 4 : ℝ) ^ cutoffSize g N *
          (N : ℝ) * (2 / q) * (2 : ℝ) ^ r := by
      gcongr
    _ = 2 * rankEntropyEnvelope r * (N : ℝ) *
          ((3 : ℝ) / 8) ^ cutoffSize g N := by
      rw [rankEntropyEnvelope, pow_add]
      calc
        ((r : ℝ) * 2 ^ (r * r)) * (3 / 4 : ℝ) ^ cutoffSize g N *
            (N : ℝ) * (2 / q) * 2 ^ r =
            2 * ((r : ℝ) * (2 ^ (r * r) * 2 ^ r)) * (N : ℝ) *
              ((3 / 4 : ℝ) ^ cutoffSize g N / q) := by ring
        _ = 2 * ((r : ℝ) * (2 ^ (r * r) * 2 ^ r)) * (N : ℝ) *
              (3 / 8 : ℝ) ^ cutoffSize g N := by rw [hbase]

lemma cutoff_collision_relative_le
    {g : ℕ → ℝ} {N r : ℕ} (hk : 1 ≤ cutoffSize g N) :
    (r : ℝ) ^ 2 / ((2 : ℝ) ^ cutoffSize g N - 1) ≤
      2 * rankEntropyEnvelope r / (2 : ℝ) ^ cutoffSize g N := by
  have hinv := inv_two_pow_sub_one_le_two_div hk
  have hD0 : 0 ≤ 1 / ((2 : ℝ) ^ cutoffSize g N - 1) := by
    exact one_div_nonneg.mpr (two_pow_sub_one_pos hk).le
  have hE0 : 0 ≤ rankEntropyEnvelope r := by
    rw [rankEntropyEnvelope]
    positivity
  calc
    (r : ℝ) ^ 2 / ((2 : ℝ) ^ cutoffSize g N - 1) =
        (r : ℝ) ^ 2 * (1 / ((2 : ℝ) ^ cutoffSize g N - 1)) := by ring
    _ ≤ rankEntropyEnvelope r * (1 / ((2 : ℝ) ^ cutoffSize g N - 1)) :=
      mul_le_mul_of_nonneg_right sq_le_rankEntropyEnvelope hD0
    _ ≤ rankEntropyEnvelope r * (2 / (2 : ℝ) ^ cutoffSize g N) :=
      mul_le_mul_of_nonneg_left hinv hE0
    _ = 2 * rankEntropyEnvelope r / (2 : ℝ) ^ cutoffSize g N := by ring

/-! ## Bridges to the finite factorial-moment bound -/

lemma explicitLowerRankTerm_eq_relativeEnvelope
    (g : ℕ → ℝ) (N r : ℕ) :
    (((r * 2 ^ (r * r) * (2 ^ cutoffSize g N) ^ (r - 1) : ℕ) : ℝ) /
        (((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) ^ r)) =
      lowerRankPatternRelativeEnvelope g N r := by
  rw [lowerRankPatternRelativeEnvelope]
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub Nat.one_le_two_pow]
  norm_num

/-- After normalization by the main factorial-moment term, the last-term
bound for `incidenceLowRankEnvelope` is exactly the sharp relative envelope
defined above. -/
lemma incidenceLowRankEnvelope_div_le_relativeEnvelope
    {g : ℕ → ℝ} {N r m : ℕ}
    (hN : 0 < N) (hm : 0 < m) (hr : 1 ≤ r)
    (hk : 1 ≤ cutoffSize g N)
    (hNq : (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N) :
    incidenceLowRankEnvelope N (cutoffSize g N) r m /
        (((m : ℝ) * (2 ^ cutoffSize g N - 1 : ℕ) / N) ^ r) ≤
      incidenceLowRankRelativeEnvelope g N r := by
  let k := cutoffSize g N
  let q : ℝ := (2 : ℝ) ^ k
  let D : ℝ := q - 1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hD : 0 < D := by simpa [k, q, D] using two_pow_sub_one_pos hk
  have hMcast : (((2 ^ k - 1 : ℕ) : ℝ)) = D := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    simp [q, D]
  have htheta : 0 < (((m : ℝ) * (2 ^ k - 1 : ℕ) / N) ^ r) := by
    rw [hMcast]
    positivity
  have hlast := incidenceLowRankEnvelope_le_last
    (p := N) (k := k) (r := r) (m := m) hN (by simpa [k] using hNq)
  calc
    incidenceLowRankEnvelope N k r m /
          (((m : ℝ) * (2 ^ k - 1 : ℕ) / N) ^ r) ≤
        ((m : ℝ) ^ r * (2 : ℝ) ^ (r * r) * (3 / 4 : ℝ) ^ k * r *
          ((q / N) ^ (r - 1))) /
          (((m : ℝ) * (2 ^ k - 1 : ℕ) / N) ^ r) := by
      apply div_le_div_of_nonneg_right
      · simpa [q] using hlast
      · exact htheta.le
    _ = incidenceLowRankRelativeEnvelope g N r := by
      rw [incidenceLowRankRelativeEnvelope]
      change _ = (r : ℝ) * 2 ^ (r * r) * (3 / 4 : ℝ) ^ k *
        (N : ℝ) / D * (q / D) ^ (r - 1)
      rw [hMcast]
      have hDpow : D ^ r = D ^ (r - 1) * D := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega]
        rw [pow_succ]
      have hNpow : (N : ℝ) ^ r = (N : ℝ) ^ (r - 1) * N := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega]
        rw [pow_succ]
      have hthetaPow : ((m : ℝ) * D / N) ^ r =
          (m : ℝ) ^ r * D ^ r / (N : ℝ) ^ r := by
        rw [div_pow, mul_pow]
      have hqNpow : (q / (N : ℝ)) ^ (r - 1) =
          q ^ (r - 1) / (N : ℝ) ^ (r - 1) := by rw [div_pow]
      have hqDpow : (q / D) ^ (r - 1) =
          q ^ (r - 1) / D ^ (r - 1) := by rw [div_pow]
      rw [hthetaPow, hDpow, hNpow, hqNpow, hqDpow]
      field_simp [hmR.ne', hNR.ne', hD.ne']

/-! ## Uniform power savings -/

lemma eventually_one_le_cutoffSize
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ cutoffSize g N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_nine_tenths_log_div_log_two_le_cutoffSize hg,
      tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop ((20 / 9 : ℝ) * Real.log 2))] with N hcut hlog
  have hone : (1 : ℝ) ≤ (9 / 10 : ℝ) * Real.log (N : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    nlinarith
  exact_mod_cast hone.trans hcut

lemma eventually_two_le_rpow_nine_hundredths :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (9 / 100 : ℝ) := by
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 100)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)

lemma eventually_two_le_rpow_one_twentieth :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)

lemma two_mul_small_div_large_le {N E q : ℝ}
    (hN : 0 < N) (hE : E ≤ N ^ (1 / 100 : ℝ))
    (hq : N ^ (9 / 10 : ℝ) ≤ q)
    (_hE0 : 0 ≤ E) (_hq0 : 0 < q)
    (htwo : 2 ≤ N ^ (9 / 100 : ℝ)) :
    2 * E / q ≤ N ^ (-(4 / 5 : ℝ)) := by
  calc
    2 * E / q ≤ 2 * N ^ (1 / 100 : ℝ) / N ^ (9 / 10 : ℝ) := by
      exact div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hE (by norm_num))
        (Real.rpow_pos_of_pos hN _) hq
    _ = 2 * N ^ (-(89 / 100 : ℝ)) := by
      rw [show 2 * N ^ (1 / 100 : ℝ) / N ^ (9 / 10 : ℝ) =
        2 * (N ^ (1 / 100 : ℝ) / N ^ (9 / 10 : ℝ)) by ring,
        ← Real.rpow_sub hN]
      congr 1
      norm_num
    _ ≤ N ^ (9 / 100 : ℝ) * N ^ (-(89 / 100 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN.le _)
    _ = N ^ (-(4 / 5 : ℝ)) := by
      rw [← Real.rpow_add hN]
      congr 1
      norm_num

lemma two_mul_entropy_mul_decay_le {N E d : ℝ}
    (hN : 0 < N) (hE : E ≤ N ^ (1 / 100 : ℝ))
    (hd : d ≤ N ^ (-(63 / 50 : ℝ)))
    (_hE0 : 0 ≤ E) (hd0 : 0 ≤ d)
    (htwo : 2 ≤ N ^ (1 / 20 : ℝ)) :
    2 * E * N * d ≤ N ^ (-(1 / 5 : ℝ)) := by
  calc
    2 * E * N * d ≤
        2 * N ^ (1 / 100 : ℝ) * N * N ^ (-(63 / 50 : ℝ)) := by
      gcongr
    _ = 2 * N ^ (-(1 / 4 : ℝ)) := by
      calc
        2 * N ^ (1 / 100 : ℝ) * N * N ^ (-(63 / 50 : ℝ)) =
            2 * ((N ^ (1 / 100 : ℝ) * N ^ (1 : ℝ)) *
              N ^ (-(63 / 50 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = 2 * (N ^ ((1 / 100 : ℝ) + 1) * N ^ (-(63 / 50 : ℝ))) := by
          rw [← Real.rpow_add hN]
        _ = 2 * N ^ (((1 / 100 : ℝ) + 1) + (-(63 / 50 : ℝ))) := by
          rw [← Real.rpow_add hN]
        _ = 2 * N ^ (-(1 / 4 : ℝ)) := by norm_num
    _ ≤ N ^ (1 / 20 : ℝ) * N ^ (-(1 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN.le _)
    _ = N ^ (-(1 / 5 : ℝ)) := by
      rw [← Real.rpow_add hN]
      congr 1
      norm_num

/-- All three relative errors needed in the factorial-moment decomposition
have a fixed power saving, uniformly throughout the growing moment range. -/
theorem eventually_uniform_rank_count_power_savings
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → r ≤ momentRadius N →
      (r : ℝ) ^ 2 / ((2 : ℝ) ^ cutoffSize g N - 1) ≤
          (N : ℝ) ^ (-(4 / 5 : ℝ)) ∧
      lowerRankPatternRelativeEnvelope g N r ≤
          (N : ℝ) ^ (-(4 / 5 : ℝ)) ∧
      incidenceLowRankRelativeEnvelope g N r ≤
          (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
  filter_upwards [eventually_one_le_cutoffSize hg,
      eventually_rankEntropyEnvelope_le_rpow,
      eventually_rpow_nine_tenths_le_pow_cutoff hg,
      eventually_three_eighths_pow_cutoff_le_rpow_neg hg,
      eventually_two_le_rpow_nine_hundredths,
      eventually_two_le_rpow_one_twentieth,
      eventually_gt_atTop (0 : ℕ)] with N hk hent hq hdec htwo9 htwo5 hN
  intro r hr hrad
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hE0 : 0 ≤ rankEntropyEnvelope r := by
    rw [rankEntropyEnvelope]
    positivity
  have hq0 : 0 < (2 : ℝ) ^ cutoffSize g N := by positivity
  have hcommon : 2 * rankEntropyEnvelope r / (2 : ℝ) ^ cutoffSize g N ≤
      (N : ℝ) ^ (-(4 / 5 : ℝ)) :=
    two_mul_small_div_large_le hNreal (hent r hrad) hq hE0 hq0 htwo9
  refine ⟨(cutoff_collision_relative_le hk).trans hcommon,
    (lowerRankPatternRelativeEnvelope_le hr hk).trans hcommon, ?_⟩
  exact (incidenceLowRankRelativeEnvelope_le hk).trans
    (two_mul_entropy_mul_decay_le hNreal (hent r hrad) hdec hE0
      (by positivity) htwo5)

/-- Direct interface for `abs_rankStratifiedMoment_sub_leading_le_explicit`.
In the nontrivial branch `N ≤ 2^k`, its entire relative-error coefficient is
at most three times `N^(-1/5)`, uniformly for all positive moments below the
growing radius and for every positive target multiplicity `m`. -/
theorem eventually_uniform_explicit_moment_error
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ r m : ℕ,
      1 ≤ r → r ≤ momentRadius N → 0 < m →
      (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
      (r : ℝ) ^ 2 / ((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) +
          (((r * 2 ^ (r * r) * (2 ^ cutoffSize g N) ^ (r - 1) : ℕ) : ℝ) /
            (((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) ^ r)) +
          incidenceLowRankEnvelope N (cutoffSize g N) r m /
            (((m : ℝ) * (2 ^ cutoffSize g N - 1 : ℕ) / N) ^ r) ≤
        3 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
  filter_upwards [eventually_uniform_rank_count_power_savings hg,
      eventually_one_le_cutoffSize hg,
      eventually_ge_atTop (1 : ℕ)] with N hs hk hN
  intro r m hr hrad hm hNq
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hpowCompare : (N : ℝ) ^ (-(4 / 5 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hN
    · norm_num
  have hs' := hs r hr hrad
  have hcollision :
      (r : ℝ) ^ 2 / ((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) ≤
        (N : ℝ) ^ (-(4 / 5 : ℝ)) := by
    convert hs'.1 using 1
    norm_num [Nat.cast_sub Nat.one_le_two_pow]
  have hlower :
      (((r * 2 ^ (r * r) * (2 ^ cutoffSize g N) ^ (r - 1) : ℕ) : ℝ) /
          (((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) ^ r)) ≤
        (N : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [explicitLowerRankTerm_eq_relativeEnvelope]
    exact hs'.2.1
  have hinc :
      incidenceLowRankEnvelope N (cutoffSize g N) r m /
          (((m : ℝ) * (2 ^ cutoffSize g N - 1 : ℕ) / N) ^ r) ≤
        (N : ℝ) ^ (-(1 / 5 : ℝ)) :=
    (incidenceLowRankEnvelope_div_le_relativeEnvelope hNpos hm hr hk hNq).trans
      hs'.2.2
  nlinarith

end Erdos543

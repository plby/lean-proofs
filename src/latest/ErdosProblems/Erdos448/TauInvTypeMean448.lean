import ErdosProblems.Erdos448.HalberstamComplete448
import UnitFractions.ForMathlib.BasicEstimates

/-!
Mean values of nonnegative multiplicative functions whose prime-power values
are uniformly close to `1 / (nu + 1)`.  The local error is stated in the
`C * log p / p` form used in the Erdős--Tenenbaum argument.  Since the error
is divided by one further power of `p` in an Euler factor, its total
contribution is bounded by a convergent prime sum.
-/

open scoped BigOperators
open Finset

namespace TauInvTypeMean448

/-! ## Clean elementary/Mertens inputs

These lemmas are kept here so that this reusable mean-value package does not
transitively import either `Erdos202` or `Util.MertensThird`, whose source
files contain enlarged computational-limit settings. -/

/-- A positive global constant in the clean weak Mertens upper bound from
`UnitFractions.ForMathlib.BasicEstimates`. -/
noncomputable def cleanMertensConstant : ℝ :=
  Classical.choose weak_mertens_third_upper_all

lemma cleanMertensConstant_pos : 0 < cleanMertensConstant :=
  (Classical.choose_spec weak_mertens_third_upper_all).1

lemma partialEulerProduct_le_cleanMertens (N : ℕ) (hN : 2 ≤ N) :
    partial_euler_product N ≤ cleanMertensConstant * Real.log (N : ℝ) := by
  have h := (Classical.choose_spec weak_mertens_third_upper_all).2
    (N : ℝ) (by exact_mod_cast hN)
  have hprod : 0 ≤ partial_euler_product N :=
    zero_le_one.trans partial_euler_trivial_lower_bound
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  change partial_euler_product N ≤
    Classical.choose weak_mertens_third_upper_all * Real.log (N : ℝ)
  simpa [Real.norm_of_nonneg hprod, Real.norm_of_nonneg hlog] using h

/-- Coefficient-one reciprocal-prime bound with a clean, non-explicit
Mertens constant. -/
theorem reciprocal_prime_sum_upper (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)) ≤
        Real.log (cleanMertensConstant * Real.log (N : ℝ)) := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hterm : ∀ p ∈ P,
      (1 : ℝ) / (p : ℝ) ≤ -Real.log (1 - 1 / (p : ℝ)) := by
    intro p hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    have hpos : 0 < (1 : ℝ) - 1 / (p : ℝ) := by
      exact sub_pos.mpr (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpCast)
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith
  have hsumLog :
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (partial_euler_product N) := by
    calc
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ P, -Real.log (1 - 1 / (p : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = Real.log (∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹) := by
        rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro p hp
          have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
          have hne : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 :=
            ne_of_gt (sub_pos.mpr
              (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpCast))
          rw [Real.log_inv]
        · intro p hp
          have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hpCast : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
          exact inv_ne_zero (ne_of_gt (sub_pos.mpr
            (by simpa [one_div] using inv_lt_one_of_one_lt₀ hpCast)))
      _ = Real.log (partial_euler_product N) := by
        simp [P, partial_euler_product]
  have hprodPos : 0 < partial_euler_product N :=
    zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hupper := partialEulerProduct_le_cleanMertens N (by omega)
  have hlogUpper := Real.log_le_log hprodPos hupper
  simpa [P] using hsumLog.trans hlogUpper

/-- Finite telescoping estimate for the convergent secondary Euler term. -/
lemma sum_Icc_two_inv_mul_pred (M : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 2 M,
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) = 1 - 1 / (M : ℝ) := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases hM0 : M = 0
      · subst M
        simp
      · have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1), ih hMpos]
        have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
        have hMsR : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp [hMR, hMsR]
        ring

lemma sum_Icc_two_inv_mul_pred_le_one (M : ℕ) :
    (∑ n ∈ Finset.Icc 2 M,
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
  by_cases hM : 1 ≤ M
  · rw [sum_Icc_two_inv_mul_pred M hM]
    exact sub_le_self _ (by positivity)
  · have : M = 0 := by omega
    subst M
    simp

lemma dyadic_weight_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) =
      4 - (((2 * n + 4 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hpow]
      ring

lemma dyadic_weight_sum_le_four (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k)) ≤ 4 := by
  rw [dyadic_weight_sum_eq]
  exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

lemma prime_log_div_sq_dyadic_block_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
  classical
  let B : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcard : B.card ≤ 2 ^ k := by
    calc
      B.card ≤ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card :=
        Finset.card_filter_le _ _
      _ = 2 ^ k := by rw [Nat.card_Ico, pow_succ]; omega
  have hpoint : ∀ p ∈ B,
      Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
        (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
    intro p hp
    have hpB := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpB.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpB.2.pos
    have hlow : ((2 ^ k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpIco.1
    have hupp : (p : ℝ) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
      exact_mod_cast hpIco.2.le
    have hlog : Real.log (p : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      calc
        Real.log (p : ℝ) ≤ Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) :=
          Real.log_le_log hpPos hupp
        _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
          rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num,
            Real.log_pow]
    have hlowSq : (((2 ^ k : ℕ) : ℝ)) ^ 2 ≤ (p : ℝ) ^ 2 := by gcongr
    have hnumNonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (by positivity) hlog2
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ 2
          ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) / (p : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ ≤ (((k + 1 : ℕ) : ℝ) * Real.log 2) /
            (((2 ^ k : ℕ) : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_left hnumNonneg (by positivity) hlowSq
      _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) := by
          rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num, ← pow_mul]
          simp [Nat.mul_comm]
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ B, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ ≤ ∑ p ∈ B,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k) :=
      Finset.sum_le_sum hpoint
    _ = (B.card : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ k : ℕ) : ℝ) *
          ((((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ (2 * k)) := by
      gcongr
    _ = (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      rw [show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k by norm_num]
      have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k by
        rw [two_mul, pow_add]]
      field_simp [hpow]

theorem sum_primesLE_log_div_sq_le (Y : ℕ) :
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
      4 * Real.log 2 := by
  classical
  let S : Finset ℕ := Nat.primesLE Y
  let T : Finset ℕ := Finset.range (Nat.log 2 Y + 1)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    have hpS := Nat.mem_primesLE.mp hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right hpS.1))
  have hdecomp :
      (∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) =
        ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun p : ℕ => Real.log (p : ℝ) / (p : ℝ) ^ 2)
  have hfiber : ∀ k ∈ T,
      (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpS := Nat.mem_primesLE.mp hpFilter.1
      have hpPrime : Nat.Prime p := hpS.2
      have hpNe : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hpFilter.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr
          ⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpNe,
            by simpa [hlog, Nat.succ_eq_add_one] using
              Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩,
          hpPrime⟩
    · intro p hp _hnot
      have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
        (sq_nonneg _)
  calc
    (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) / (p : ℝ) ^ 2)
        = ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2 := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          Real.log (p : ℝ) / (p : ℝ) ^ 2 := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            Real.log (p : ℝ) / (p : ℝ) ^ 2 := Finset.sum_le_sum hfiber
    _ ≤ ∑ k ∈ T,
          (((k + 1 : ℕ) : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      exact Finset.sum_le_sum (fun k hk => prime_log_div_sq_dyadic_block_le k)
    _ = Real.log 2 *
          ∑ k ∈ T, (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ Real.log 2 * 4 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [T] using dyadic_weight_sum_le_four (Nat.log 2 Y + 1))
        (Real.log_nonneg (by norm_num))
    _ = 4 * Real.log 2 := by ring

/-- The logarithmic-error version of the `tau`-inverse local type. -/
structure IsTauInverseLogType (w : ℕ → ℝ) (C : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  map_zero : w 0 = 0
  map_one : w 1 = 1
  map_mul_of_coprime : ∀ {m n : ℕ}, m.Coprime n → w (m * n) = w m * w n
  nonneg : ∀ n, 0 ≤ w n
  prime_pow_close : ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
    |w (p ^ nu) - 1 / (((nu + 1 : ℕ) : ℝ))| ≤
      C * Real.log (p : ℝ) / (p : ℝ)

/-- The source-paper version, with a power-saving prime-power error. -/
structure IsTauInversePowType (w : ℕ → ℝ) (C delta : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  delta_pos : 0 < delta
  map_zero : w 0 = 0
  map_one : w 1 = 1
  map_mul_of_coprime : ∀ {m n : ℕ}, m.Coprime n → w (m * n) = w m * w n
  nonneg : ∀ n, 0 ≤ w n
  prime_pow_close : ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
    |w (p ^ nu) - 1 / (((nu + 1 : ℕ) : ℝ))| ≤
      C * (p : ℝ) ^ (-delta)

lemma IsTauInverseLogType.prime_pow_upper
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    w (p ^ nu) ≤ 1 / (((nu + 1 : ℕ) : ℝ)) +
      C * Real.log (p : ℝ) / (p : ℝ) := by
  have h := (abs_le.mp (hw.prime_pow_close hp hnu)).2
  linarith

lemma IsTauInverseLogType.prime_pow_le_one_add_C
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    w (p ^ nu) ≤ 1 + C := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : Real.log (p : ℝ) ≤ (p : ℝ) :=
    Real.log_le_self hpR.le
  have hratio : Real.log (p : ℝ) / (p : ℝ) ≤ 1 :=
    (div_le_one hpR).2 hlog
  have hbase : 1 / (((nu + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  calc
    w (p ^ nu) ≤ 1 / (((nu + 1 : ℕ) : ℝ)) +
        C * Real.log (p : ℝ) / (p : ℝ) := hw.prime_pow_upper hp hnu
    _ ≤ 1 + C := by
      have := mul_le_mul_of_nonneg_left hratio hw.C_nonneg
      have herr : C * Real.log (p : ℝ) / (p : ℝ) ≤ C := by
        calc
          C * Real.log (p : ℝ) / (p : ℝ) =
              C * (Real.log (p : ℝ) / (p : ℝ)) := by ring
          _ ≤ C * 1 := this
          _ = C := by ring
      linarith

lemma IsTauInversePowType.prime_pow_upper
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    w (p ^ nu) ≤ 1 / (((nu + 1 : ℕ) : ℝ)) +
      C * (p : ℝ) ^ (-delta) := by
  have h := (abs_le.mp (hw.prime_pow_close hp hnu)).2
  linarith

lemma IsTauInversePowType.prime_pow_le_one_add_C
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu) :
    w (p ^ nu) ≤ 1 + C := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have herr : (p : ℝ) ^ (-delta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hw.delta_pos.le)
  have hbase : 1 / (((nu + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  calc
    w (p ^ nu) ≤ 1 / (((nu + 1 : ℕ) : ℝ)) +
        C * (p : ℝ) ^ (-delta) := hw.prime_pow_upper hp hnu
    _ ≤ 1 + C := by
      have := mul_le_mul_of_nonneg_left herr hw.C_nonneg
      linarith

/-- The comparison series for one local Euler factor. -/
noncomputable def localMajorant (C : ℝ) (p j : ℕ) : ℝ :=
  if j = 0 then 1
  else (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) * ((p : ℝ)⁻¹) ^ j

lemma localMajorant_nonneg {C : ℝ} (hC : 0 ≤ C)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 ≤ localMajorant C p j := by
  unfold localMajorant
  split_ifs
  · norm_num
  · have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    positivity

lemma localMajorant_summable {C : ℝ} (_hC : 0 ≤ C)
    {p : ℕ} (hp : p.Prime) :
    Summable (localMajorant C p) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  let a : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
  have hgeom : Summable (fun j : ℕ => a * ((p : ℝ)⁻¹) ^ j) :=
    (summable_geometric_of_norm_lt_one hr).mul_left a
  have hsingle : Summable
      (fun j : ℕ => if j = 0 then 1 - a else 0) :=
    (hasSum_ite_eq 0 (1 - a)).summable
  have heq : localMajorant C p =
      fun j : ℕ => a * ((p : ℝ)⁻¹) ^ j +
        if j = 0 then 1 - a else 0 := by
    funext j
    by_cases hj : j = 0
    · subst j
      simp [localMajorant, a]
    · simp [localMajorant, a, hj]
  rw [heq]
  exact hgeom.add hsingle

lemma localMajorant_tsum {C : ℝ} {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, localMajorant C p j) =
      1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
        ((p : ℝ) - 1) := by
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  let a : ℝ := 1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)
  have hgeom : Summable (fun j : ℕ => a * ((p : ℝ)⁻¹) ^ j) :=
    (summable_geometric_of_norm_lt_one hr).mul_left a
  have hsingle : Summable
      (fun j : ℕ => if j = 0 then 1 - a else 0) :=
    (hasSum_ite_eq 0 (1 - a)).summable
  have heq : localMajorant C p =
      fun j : ℕ => a * ((p : ℝ)⁻¹) ^ j +
        if j = 0 then 1 - a else 0 := by
    funext j
    by_cases hj : j = 0
    · subst j
      simp [localMajorant, a]
    · simp [localMajorant, a, hj]
  rw [heq, hgeom.tsum_add hsingle, tsum_mul_left,
    tsum_geometric_of_norm_lt_one hr]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  simp only [tsum_ite_eq]
  dsimp [a]
  field_simp [hp0, hp1]
  ring

lemma local_term_le_majorant
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    w (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤ localMajorant C p j := by
  by_cases hj : j = 0
  · subst j
    simp [localMajorant, hw.map_one]
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hpjR : 0 < (((p ^ j : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.pow_pos hp.pos : 0 < p ^ j)
    have hhalf : 1 / (((j + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast (show 2 ≤ j + 1 by omega))
    calc
      w (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤
          (1 / (((j + 1 : ℕ) : ℝ)) +
            C * Real.log (p : ℝ) / (p : ℝ)) /
              (((p ^ j : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right (hw.prime_pow_upper hp hj1) hpjR.le
      _ ≤ (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
              (((p ^ j : ℕ) : ℝ)) := by
        gcongr
      _ = localMajorant C p j := by
        simp only [localMajorant, if_neg hj]
        norm_num [div_eq_mul_inv, inv_pow]

lemma localEuler_summable
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => w (p ^ j) / (((p ^ j : ℕ) : ℝ))) := by
  rw [← summable_norm_iff]
  apply Summable.of_nonneg_of_le
      (fun j => norm_nonneg _)
      (fun j => ?_)
      (localMajorant_summable hw.C_nonneg hp)
  rw [Real.norm_of_nonneg (div_nonneg (hw.nonneg _) (by positivity))]
  exact local_term_le_majorant hw hp j

lemma localEuler_le_exp
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp (1 / (2 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) +
        C * Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hsum := Summable.tsum_le_tsum
    (fun j => local_term_le_majorant hw hp j)
    (localEuler_summable hw hp)
    (localMajorant_summable hw.C_nonneg hp)
  rw [localMajorant_tsum hp] at hsum
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  let x : ℝ := 1 / (2 * (p : ℝ)) +
    1 / ((p : ℝ) * ((p : ℝ) - 1)) +
    C * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpR.le
  have hx :
      (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
          ((p : ℝ) - 1) ≤ x := by
    dsimp [x]
    have hdiff :
        x - (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
            ((p : ℝ) - 1) =
          1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
      dsimp [x]
      field_simp [hp0, hp1]
      ring
    rw [← sub_nonneg]
    rw [hdiff]
    positivity
  calc
    (∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
        1 + (1 / 2 + C * Real.log (p : ℝ) / (p : ℝ)) /
          ((p : ℝ) - 1) := hsum
    _ ≤ 1 + x := by simpa [add_comm] using add_le_add_left hx 1
    _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
    _ = Real.exp (1 / (2 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) +
        C * Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1))) := rfl

/-- Local Euler-factor estimate for the source-paper power error. -/
lemma localEulerPow_le_exp
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp (1 / (2 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) +
        2 * C * (p : ℝ) ^ (-(1 + delta))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  let D : ℝ := C * (p : ℝ) ^ (-delta)
  let Cp : ℝ := D * (p : ℝ) / Real.log (p : ℝ)
  have hD : 0 ≤ D := mul_nonneg hw.C_nonneg (by positivity)
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCpEq : Cp * Real.log (p : ℝ) / (p : ℝ) = D := by
    dsimp [Cp]
    field_simp [hpR.ne', hp1.ne']
  have hpoint : ∀ j : ℕ,
      w (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤ localMajorant Cp p j := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [localMajorant, hw.map_one]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      have hpjR : 0 < (((p ^ j : ℕ) : ℝ)) := by
        exact_mod_cast (Nat.pow_pos hp.pos : 0 < p ^ j)
      have hhalf : 1 / (((j + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (show 2 ≤ j + 1 by omega))
      calc
        w (p ^ j) / (((p ^ j : ℕ) : ℝ)) ≤
            (1 / (((j + 1 : ℕ) : ℝ)) + D) /
              (((p ^ j : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right (hw.prime_pow_upper hp hj1) hpjR.le
        _ ≤ (1 / 2 + D) / (((p ^ j : ℕ) : ℝ)) := by gcongr
        _ = localMajorant Cp p j := by
          simp only [localMajorant, if_neg hj]
          rw [hCpEq]
          norm_num [div_eq_mul_inv, inv_pow]
  have hlocalSummable : Summable
      (fun j : ℕ => w (p ^ j) / (((p ^ j : ℕ) : ℝ))) := by
    rw [← summable_norm_iff]
    apply Summable.of_nonneg_of_le
        (fun j => norm_nonneg _)
        (fun j => ?_)
        (localMajorant_summable hCp hp)
    rw [Real.norm_of_nonneg (div_nonneg (hw.nonneg _) (by positivity))]
    exact hpoint j
  have hsum := Summable.tsum_le_tsum hpoint hlocalSummable
    (localMajorant_summable hCp hp)
  rw [localMajorant_tsum hp, hCpEq] at hsum
  have hp1R : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := hpR.ne'
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hDdiv : D / ((p : ℝ) - 1) ≤
      2 * C * (p : ℝ) ^ (-(1 + delta)) := by
    have hpcomp : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    have hinvcomp : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) :=
      (div_le_div_iff₀ (sub_pos.mpr hp1R) hpR).2 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hinvcomp hD
    have hrpow : (p : ℝ) ^ (-delta) / (p : ℝ) =
        (p : ℝ) ^ (-(1 + delta)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one p, ← Real.rpow_add hpR]
      congr 1
      ring
    calc
      D / ((p : ℝ) - 1) = D * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ D * (2 / (p : ℝ)) := hmul
      _ = 2 * C * (p : ℝ) ^ (-(1 + delta)) := by
        dsimp [D]
        rw [show C * (p : ℝ) ^ (-delta) * (2 / (p : ℝ)) =
          2 * C * ((p : ℝ) ^ (-delta) / (p : ℝ)) by ring, hrpow]
  let x : ℝ := 1 / (2 * (p : ℝ)) +
    1 / ((p : ℝ) * ((p : ℝ) - 1)) +
    2 * C * (p : ℝ) ^ (-(1 + delta))
  have hx : (1 / 2 + D) / ((p : ℝ) - 1) ≤ x := by
    have hhalfpart : (1 / 2 : ℝ) / ((p : ℝ) - 1) ≤
        1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [← sub_nonneg]
      have heq :
          (1 / (2 * (p : ℝ)) +
              1 / ((p : ℝ) * ((p : ℝ) - 1))) -
              (1 / 2 : ℝ) / ((p : ℝ) - 1) =
            1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
        field_simp [hp0, hpm1]
        ring
      rw [heq]
      positivity
    dsimp [x]
    rw [add_div]
    linarith
  calc
    (∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
        1 + (1 / 2 + D) / ((p : ℝ) - 1) := hsum
    _ ≤ 1 + x := by simpa [add_comm] using add_le_add_left hx 1
    _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
    _ = Real.exp (1 / (2 * (p : ℝ)) +
        1 / ((p : ℝ) * ((p : ℝ) - 1)) +
        2 * C * (p : ℝ) ^ (-(1 + delta))) := rfl

lemma error_prime_term_le
    {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : p.Prime) :
    C * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      2 * C * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  rw [div_le_iff₀ (mul_pos hp0 hp1), div_eq_mul_inv]
  field_simp [hp0.ne', hp1.ne']
  have hprod := mul_le_mul_of_nonneg_left
    (show (p : ℝ) ≤ 2 * ((p : ℝ) - 1) by linarith)
    (mul_nonneg hC hlog)
  nlinarith

/-- Uniform Euler-product estimate for a logarithmic-error `tau`-inverse
weight. -/
theorem eulerProduct_le
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log
        (cleanMertensConstant * Real.log (N : ℝ)) +
        1 + 8 * C * Real.log 2) := by
  classical
  let P : Finset ℕ := (N + 1).primesBelow
  have hP : P = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [P, Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hpN, hp⟩
  have hprod :
      (∏ p ∈ P, ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
        ∏ p ∈ P, Real.exp (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          C * Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hpP
      exact tsum_nonneg fun j => div_nonneg (hw.nonneg _) (by positivity)
    · intro p hpP
      exact localEuler_le_exp hw (Nat.prime_of_mem_primesBelow hpP)
  have hrec := reciprocal_prime_sum_upper N hN
  have hsecond :
      (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
    have hsub : P ⊆ Finset.Icc 2 N := by
      intro p hp
      have hp' := Nat.mem_primesBelow.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, Nat.le_of_lt_succ hp'.1⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        exact div_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith))))).trans
      (sum_Icc_two_inv_mul_pred_le_one N)
  have herr :
      (∑ p ∈ P, C * Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1))) ≤ 8 * C * Real.log 2 := by
    calc
      (∑ p ∈ P, C * Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1))) ≤
          ∑ p ∈ P, 2 * C *
            (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
        exact Finset.sum_le_sum fun p hp =>
          error_prime_term_le hw.C_nonneg (Nat.prime_of_mem_primesBelow hp)
      _ = 2 * C * ∑ p ∈ P,
          (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * C * (4 * Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hw.C_nonneg)
        rw [hP]
        have hset : (Finset.Icc 1 N).filter Nat.Prime = Nat.primesLE N := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
          constructor
          · rintro ⟨⟨_, hpN⟩, hp⟩
            exact ⟨hpN, hp⟩
          · rintro ⟨hpN, hp⟩
            exact ⟨⟨hp.one_le, hpN⟩, hp⟩
        rw [hset]
        exact sum_primesLE_log_div_sq_le N
      _ = 8 * C * Real.log 2 := by ring
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) =
        ∏ p ∈ P, ∑' j : ℕ,
          w (p ^ j) / (((p ^ j : ℕ) : ℝ)) := rfl
    _ ≤ ∏ p ∈ P, Real.exp (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          C * Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1))) := hprod
    _ = Real.exp (∑ p ∈ P, (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          C * Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)))) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) +
          1 + 8 * C * Real.log 2) := by
      rw [Real.exp_le_exp]
      simp_rw [add_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hfirst : (∑ p ∈ P, 1 / (2 * (p : ℝ))) ≤
          (1 / 2 : ℝ) * Real.log
            (cleanMertensConstant * Real.log (N : ℝ)) := by
        calc
          (∑ p ∈ P, 1 / (2 * (p : ℝ))) =
              (1 / 2 : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ ≤ (1 / 2 : ℝ) * Real.log
              (cleanMertensConstant * Real.log (N : ℝ)) := by
            gcongr
            simpa [hP] using hrec
      linarith

/-- Uniform convergent contribution of a source-paper `p^(-delta)` error. -/
noncomputable def powErrorConstant (C delta : ℝ) : ℝ :=
  ∑' n : ℕ, 2 * C * (n : ℝ) ^ (-(1 + delta))

lemma powError_summable {C delta : ℝ} (hdelta : 0 < delta) :
    Summable (fun n : ℕ => 2 * C * (n : ℝ) ^ (-(1 + delta))) := by
  apply Summable.mul_left
  exact Real.summable_nat_rpow.mpr (by linarith)

lemma powErrorConstant_nonneg {C delta : ℝ} (hC : 0 ≤ C) :
    0 ≤ powErrorConstant C delta := by
  unfold powErrorConstant
  exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity)

theorem eulerProductPow_le
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log
        (cleanMertensConstant * Real.log (N : ℝ)) +
        1 + powErrorConstant C delta) := by
  classical
  let P : Finset ℕ := (N + 1).primesBelow
  have hP : P = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [P, Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hpN, hp⟩
  have hprod :
      (∏ p ∈ P, ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) ≤
        ∏ p ∈ P, Real.exp (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          2 * C * (p : ℝ) ^ (-(1 + delta))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hpP
      exact tsum_nonneg fun j => div_nonneg (hw.nonneg _) (by positivity)
    · intro p hpP
      exact localEulerPow_le_exp hw (Nat.prime_of_mem_primesBelow hpP)
  have hrec := reciprocal_prime_sum_upper N hN
  have hsecond :
      (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
    have hsub : P ⊆ Finset.Icc 2 N := by
      intro p hp
      have hp' := Nat.mem_primesBelow.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, Nat.le_of_lt_succ hp'.1⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        exact div_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith))))).trans
      (sum_Icc_two_inv_mul_pred_le_one N)
  have herr :
      (∑ p ∈ P, 2 * C * (p : ℝ) ^ (-(1 + delta))) ≤
        powErrorConstant C delta := by
    unfold powErrorConstant
    exact (powError_summable hw.delta_pos).sum_le_tsum P
      (fun n hn => mul_nonneg (mul_nonneg (by norm_num) hw.C_nonneg) (by positivity))
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, w (p ^ j) / (((p ^ j : ℕ) : ℝ))) =
        ∏ p ∈ P, ∑' j : ℕ,
          w (p ^ j) / (((p ^ j : ℕ) : ℝ)) := rfl
    _ ≤ ∏ p ∈ P, Real.exp (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          2 * C * (p : ℝ) ^ (-(1 + delta))) := hprod
    _ = Real.exp (∑ p ∈ P, (1 / (2 * (p : ℝ)) +
          1 / ((p : ℝ) * ((p : ℝ) - 1)) +
          2 * C * (p : ℝ) ^ (-(1 + delta)))) := by rw [Real.exp_sum]
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) +
          1 + powErrorConstant C delta) := by
      rw [Real.exp_le_exp]
      simp_rw [add_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hfirst : (∑ p ∈ P, 1 / (2 * (p : ℝ))) ≤
          (1 / 2 : ℝ) * Real.log
            (cleanMertensConstant * Real.log (N : ℝ)) := by
        calc
          (∑ p ∈ P, 1 / (2 * (p : ℝ))) =
              (1 / 2 : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ ≤ (1 / 2 : ℝ) * Real.log
              (cleanMertensConstant * Real.log (N : ℝ)) := by
            gcongr
            simpa [hP] using hrec
      linarith

/-- Explicit square-root logarithmic saving for every nonnegative
multiplicative logarithmic-error `tau`-inverse weight. -/
theorem mean_le_sqrt_log
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
      ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
        Real.exp (1 + 8 * C * Real.log 2) *
          Real.sqrt cleanMertensConstant) *
        (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  have hC1 : 0 ≤ 1 + C := by linarith [hw.C_nonneg]
  have hhr := HalberstamComplete448.halberstam_richert_explicit
    w hw.map_zero hw.map_one hw.map_mul_of_coprime hw.nonneg
    (1 + C) 1 hC1 (by norm_num) (by norm_num)
    (fun p hp j => by
      simpa using hw.prime_pow_le_one_add_C hp (show 1 ≤ j + 1 by omega))
    N (by omega)
  have heuler := eulerProduct_le hw N hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hN))
  have hfac : 0 ≤
      (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg hC1
      (show (0 : ℝ) ≤ 1 by norm_num)
    positivity
  have hraw := hhr.trans (mul_le_mul_of_nonneg_left heuler hfac)
  have hthree : 0 < cleanMertensConstant * Real.log (N : ℝ) :=
    mul_pos cleanMertensConstant_pos hlogN
  have hexp_half :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) =
        Real.sqrt (cleanMertensConstant * Real.log (N : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hthree]
    congr 1
    ring
  have hsqrt_mul :
      Real.sqrt (cleanMertensConstant * Real.log (N : ℝ)) =
        Real.sqrt cleanMertensConstant * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_mul cleanMertensConstant_pos.le]
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.mpr hlogN
  let s : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hs : 0 < s := by simpa [s] using hsqrt_pos
  have hsquare : s ^ 2 = Real.log (N : ℝ) := by
    simpa [s] using Real.sq_sqrt hlogN.le
  have hquot :
      (N : ℝ) / Real.log (N : ℝ) * s = (N : ℝ) / s := by
    rw [← hsquare]
    field_simp [hs.ne']
  have hexp_split :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) +
          1 + 8 * C * Real.log 2) =
        Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) *
          Real.exp (1 + 8 * C * Real.log 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
          Real.exp ((1 / 2 : ℝ) * Real.log
            (cleanMertensConstant * Real.log (N : ℝ)) +
            1 + 8 * C * Real.log 2) := hraw
    _ = ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
          Real.exp (1 + 8 * C * Real.log 2) *
            Real.sqrt cleanMertensConstant) *
          (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      rw [hexp_split, hexp_half, hsqrt_mul]
      change
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (Real.sqrt cleanMertensConstant * s *
                Real.exp (1 + 8 * C * Real.log 2)) =
            (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + 8 * C * Real.log 2) *
                Real.sqrt cleanMertensConstant *
              (N : ℝ) / s
      calc
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (Real.sqrt cleanMertensConstant * s *
                Real.exp (1 + 8 * C * Real.log 2)) =
            (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + 8 * C * Real.log 2) *
                Real.sqrt cleanMertensConstant *
              ((N : ℝ) / Real.log (N : ℝ) * s) := by ring
        _ = (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + 8 * C * Real.log 2) *
                Real.sqrt cleanMertensConstant *
              ((N : ℝ) / s) := by rw [hquot]
        _ = ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + 8 * C * Real.log 2) *
                Real.sqrt cleanMertensConstant) *
              (N : ℝ) / s := by ring

/-- Square-root logarithmic saving for the source-paper `p^(-delta)` class. -/
theorem meanPow_le_sqrt_log
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
      ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
        Real.exp (1 + powErrorConstant C delta) *
          Real.sqrt cleanMertensConstant) *
        (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  have hC1 : 0 ≤ 1 + C := by linarith [hw.C_nonneg]
  have hhr := HalberstamComplete448.halberstam_richert_explicit
    w hw.map_zero hw.map_one hw.map_mul_of_coprime hw.nonneg
    (1 + C) 1 hC1 (by norm_num) (by norm_num)
    (fun p hp j => by
      simpa using hw.prime_pow_le_one_add_C hp (show 1 ≤ j + 1 by omega))
    N (by omega)
  have heuler := eulerProductPow_le hw N hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hN))
  have hfac : 0 ≤
      (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hm := HalberstamScratch.explicitMassConstant_nonneg hC1
      (show (0 : ℝ) ≤ 1 by norm_num)
    positivity
  have hraw := hhr.trans (mul_le_mul_of_nonneg_left heuler hfac)
  have hthree : 0 < cleanMertensConstant * Real.log (N : ℝ) :=
    mul_pos cleanMertensConstant_pos hlogN
  have hexp_half :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) =
        Real.sqrt (cleanMertensConstant * Real.log (N : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hthree]
    congr 1
    ring
  have hsqrt_mul :
      Real.sqrt (cleanMertensConstant * Real.log (N : ℝ)) =
        Real.sqrt cleanMertensConstant * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_mul cleanMertensConstant_pos.le]
  let s : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.mpr hlogN
  have hsquare : s ^ 2 = Real.log (N : ℝ) := by
    simpa [s] using Real.sq_sqrt hlogN.le
  have hquot :
      (N : ℝ) / Real.log (N : ℝ) * s = (N : ℝ) / s := by
    rw [← hsquare]
    field_simp [hs.ne']
  have hexp_split :
      Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ)) +
          1 + powErrorConstant C delta) =
        Real.exp ((1 / 2 : ℝ) * Real.log
          (cleanMertensConstant * Real.log (N : ℝ))) *
          Real.exp (1 + powErrorConstant C delta) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
          Real.exp ((1 / 2 : ℝ) * Real.log
            (cleanMertensConstant * Real.log (N : ℝ)) +
            1 + powErrorConstant C delta) := hraw
    _ = ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
          Real.exp (1 + powErrorConstant C delta) *
            Real.sqrt cleanMertensConstant) *
          (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      rw [hexp_split, hexp_half, hsqrt_mul]
      change
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (Real.sqrt cleanMertensConstant * s *
                Real.exp (1 + powErrorConstant C delta)) =
            (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + powErrorConstant C delta) *
                Real.sqrt cleanMertensConstant *
              (N : ℝ) / s
      calc
        (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
              (Real.sqrt cleanMertensConstant * s *
                Real.exp (1 + powErrorConstant C delta)) =
            (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + powErrorConstant C delta) *
                Real.sqrt cleanMertensConstant *
              ((N : ℝ) / Real.log (N : ℝ) * s) := by ring
        _ = (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + powErrorConstant C delta) *
                Real.sqrt cleanMertensConstant *
              ((N : ℝ) / s) := by rw [hquot]
        _ = ((HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
              Real.exp (1 + powErrorConstant C delta) *
                Real.sqrt cleanMertensConstant) *
              (N : ℝ) / s := by ring

/-- The constant in `mean_le_sqrt_log`, named for dyadic consumers. -/
noncomputable def meanConstant (C : ℝ) : ℝ :=
  (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
    Real.exp (1 + 8 * C * Real.log 2) *
      Real.sqrt cleanMertensConstant

lemma meanConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ meanConstant C := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show 0 ≤ 1 + C by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold meanConstant
  positivity

noncomputable def powMeanConstant (C delta : ℝ) : ℝ :=
  (HalberstamScratch.explicitMassConstant (1 + C) 1 + 1) *
    Real.exp (1 + powErrorConstant C delta) *
      Real.sqrt cleanMertensConstant

lemma powMeanConstant_nonneg {C delta : ℝ} (hC : 0 ≤ C) :
    0 ≤ powMeanConstant C delta := by
  have hm := HalberstamScratch.explicitMassConstant_nonneg
    (show 0 ≤ 1 + C by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  unfold powMeanConstant
  positivity

/-- Dyadic form of the ordinary mean bound.  This is the exact `k^(-1/2)`
input expected for the output correction weight in the third
Erdős--Tenenbaum mean-value application. -/
theorem mean_dyadic_le
    {w : ℕ → ℝ} {C : ℝ} (hw : IsTauInverseLogType w C)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 (2 ^ (k + 2)), w n) ≤
      (4 * meanConstant C / Real.sqrt (Real.log 2)) *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
  let N : ℕ := 2 ^ (k + 2)
  have hN : 3 ≤ N := by
    dsimp [N]
    have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hmain := mean_le_sqrt_log hw N hN
  change (∑ n ∈ Finset.Icc 1 N, w n) ≤ _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlogN : Real.log (N : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [N]
    rw [show (((2 ^ (k + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 2) by norm_num,
      Real.log_pow]
  have hlogs : (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rw [hlogN]
    gcongr
    norm_num
  have hsqrtSmallPos : 0 < Real.sqrt ((k : ℝ) * Real.log 2) :=
    Real.sqrt_pos.mpr (mul_pos hkR hlog2)
  have hsqrtBigPos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.mpr ((mul_pos hkR hlog2).trans_le hlogs)
  have hsqrtLe : Real.sqrt ((k : ℝ) * Real.log 2) ≤
      Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_le_sqrt hlogs
  have hdiv :
      meanConstant C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) ≤
        meanConstant C * (N : ℝ) /
          Real.sqrt ((k : ℝ) * Real.log 2) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg (meanConstant_nonneg hw.C_nonneg) (Nat.cast_nonneg N))
      hsqrtSmallPos hsqrtLe
  have hNcast : (N : ℝ) = 4 * ((2 ^ k : ℕ) : ℝ) := by
    dsimp [N]
    norm_num [pow_add]
    ring
  have hsqrtMul :
      Real.sqrt ((k : ℝ) * Real.log 2) =
        Real.sqrt (k : ℝ) * Real.sqrt (Real.log 2) := by
    rw [Real.sqrt_mul hkR.le]
  have hinvSqrt :
      (Real.sqrt (k : ℝ))⁻¹ = (k : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    have hk0 : 0 ≤ (k : ℝ) := hkR.le
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hk0]
  calc
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
        meanConstant C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      simpa [meanConstant] using hmain
    _ ≤ meanConstant C * (N : ℝ) /
          Real.sqrt ((k : ℝ) * Real.log 2) := hdiv
    _ = (4 * meanConstant C / Real.sqrt (Real.log 2)) *
          ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [hNcast, hsqrtMul, ← hinvSqrt]
      field_simp [Real.sqrt_ne_zero'.mpr hlog2,
        Real.sqrt_ne_zero'.mpr hkR]

/-- Dyadic `k^(-1/2)` mean bound for the source-paper power-error class. -/
theorem meanPow_dyadic_le
    {w : ℕ → ℝ} {C delta : ℝ} (hw : IsTauInversePowType w C delta)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 (2 ^ (k + 2)), w n) ≤
      (4 * powMeanConstant C delta / Real.sqrt (Real.log 2)) *
        ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
  let N : ℕ := 2 ^ (k + 2)
  have hN : 3 ≤ N := by
    dsimp [N]
    have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hmain := meanPow_le_sqrt_log hw N hN
  change (∑ n ∈ Finset.Icc 1 N, w n) ≤ _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlogN : Real.log (N : ℝ) = ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [N]
    rw [show (((2 ^ (k + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 2) by norm_num,
      Real.log_pow]
  have hlogs : (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rw [hlogN]
    gcongr
    norm_num
  have hsqrtSmallPos : 0 < Real.sqrt ((k : ℝ) * Real.log 2) :=
    Real.sqrt_pos.mpr (mul_pos hkR hlog2)
  have hsqrtLe : Real.sqrt ((k : ℝ) * Real.log 2) ≤
      Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_le_sqrt hlogs
  have hdiv :
      powMeanConstant C delta * (N : ℝ) /
          Real.sqrt (Real.log (N : ℝ)) ≤
        powMeanConstant C delta * (N : ℝ) /
          Real.sqrt ((k : ℝ) * Real.log 2) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg (powMeanConstant_nonneg hw.C_nonneg) (Nat.cast_nonneg N))
      hsqrtSmallPos hsqrtLe
  have hNcast : (N : ℝ) = 4 * ((2 ^ k : ℕ) : ℝ) := by
    dsimp [N]
    norm_num [pow_add]
    ring
  have hsqrtMul :
      Real.sqrt ((k : ℝ) * Real.log 2) =
        Real.sqrt (k : ℝ) * Real.sqrt (Real.log 2) := by
    rw [Real.sqrt_mul hkR.le]
  have hinvSqrt :
      (Real.sqrt (k : ℝ))⁻¹ = (k : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hkR.le]
  calc
    (∑ n ∈ Finset.Icc 1 N, w n) ≤
        powMeanConstant C delta * (N : ℝ) /
          Real.sqrt (Real.log (N : ℝ)) := by
      simpa [powMeanConstant] using hmain
    _ ≤ powMeanConstant C delta * (N : ℝ) /
          Real.sqrt ((k : ℝ) * Real.log 2) := hdiv
    _ = (4 * powMeanConstant C delta / Real.sqrt (Real.log 2)) *
          ((2 ^ k : ℕ) : ℝ) * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [hNcast, hsqrtMul, ← hinvSqrt]
      field_simp [Real.sqrt_ne_zero'.mpr hlog2,
        Real.sqrt_ne_zero'.mpr hkR]

end TauInvTypeMean448

#print axioms TauInvTypeMean448.mean_le_sqrt_log
#print axioms TauInvTypeMean448.mean_dyadic_le
#print axioms TauInvTypeMean448.meanPow_le_sqrt_log
#print axioms TauInvTypeMean448.meanPow_dyadic_le

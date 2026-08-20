/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Sqrt

/-!
# Erdős Problem 518: arithmetic for the Chen--Chen case analysis

The combinatorial proof repeatedly subtracts cardinalities.  The lemmas in the large-`c`
part are therefore stated over `ℤ`; callers can cast natural cardinality identities before
applying them.  The final finite reductions are stated over `ℕ`.
-/

namespace Erdos518

/-! ## Basic consequences of the minimal-counterexample bounds -/

lemma cut_block_inequality {c w : ℤ} (hc : 0 ≤ c) (hcw : c ≤ w) :
    c ^ 2 + 2 * c - w ≤ c * (w + 1) := by
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hcw)]

lemma basic_complement_square_bound {c w : ℤ} (hw : w ≤ 2 * c - 2) :
    (c - 1) ^ 2 + 1 ≤ c ^ 2 - w := by
  nlinarith

lemma cover_failure_forces_a0_bound {c w a0 a1 : ℕ}
    (hw : w = a0 + a1) (hcover : c + 1 ≤ 1 + ceilHalf a1 + a0) :
    2 * c - 1 ≤ w + a0 := by
  have hceil := two_mul_ceilHalf_le_add_one a1
  omega

lemma cover_failure_forces_a0_sub_bound {c w a0 a1 : ℕ}
    (hw : w = a0 + a1) (hcover : c + 1 ≤ 1 + ceilHalf a1 + a0) :
    2 * c - 1 - w ≤ a0 := by
  have h := cover_failure_forces_a0_bound hw hcover
  omega

lemma basic_a0_positive {c r w a0 : ℕ} (hc : 1 ≤ c) (hw : w ≤ r - 2)
    (hr : r ≤ 2 * c) (ha0 : 2 * c - 1 - w ≤ a0) : 1 ≤ a0 := by
  omega

/-! ## Claim 1: the branch `t ≥ 2` -/

lemma claim1_a0_lower {c w a0 a1 : ℕ} (hw : w = a0 + a1)
    (ht : c + 1 ≤ a0 + ceilHalf a1) : 2 * c + 1 - w ≤ a0 := by
  have hceil := two_mul_ceilHalf_le_add_one a1
  omega

lemma claim1_a0_ge_three {c r w a0 : ℕ} (hc : 4 ≤ c) (hw : w ≤ r - 2)
    (hr : r ≤ 2 * c) (ha0 : 2 * c + 1 - w ≤ a0) : 3 ≤ a0 := by
  omega

lemma sq_sub_six_mul_add_eight_nonneg {c : ℤ} (hc : 4 ≤ c) :
    0 ≤ c ^ 2 - 6 * c + 8 := by
  have hprod : 0 ≤ (c - 2) * (c - 4) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

lemma claim1_dense_first_step {c r w μ : ℤ} (hw : w ≤ r - 2)
    (hμ : μ ≤ r - 2) :
    c ^ 2 - 3 * r + 8 ≤ c ^ 2 + r - 2 * w - 2 * μ := by
  omega

lemma claim1_dense_second_step {c r : ℤ} (hr : r ≤ 2 * c) :
    c ^ 2 - 6 * c + 8 ≤ c ^ 2 - 3 * r + 8 := by
  omega

lemma claim1_dense_nonneg {c r w μ : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hμ : μ ≤ r - 2) :
    0 ≤ c ^ 2 + r - 2 * w - 2 * μ := by
  exact (sq_sub_six_mul_add_eight_nonneg hc).trans
    ((claim1_dense_second_step hr).trans (claim1_dense_first_step hw hμ))

/-! Arithmetic for the covering-device parameters. -/

lemma device_small_p_nonneg {d μ p h : ℤ} (hp : p ≤ h)
    (hbase : 0 ≤ d - μ - 2 * h) : 0 ≤ d - μ - 2 * p := by
  omega

lemma claim1_small_p_base {c r w μ : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hμ : μ ≤ r - 2) :
    0 ≤ (c ^ 2 + r - 2 * w) - μ - 2 * (c - 1) := by
  have hsquare := sq_sub_six_mul_add_eight_nonneg hc
  nlinarith

lemma claim1_small_p_condition {c r w μ p : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hμ : μ ≤ r - 2)
    (hp : p ≤ c - 1) :
    2 * p ≤ (c ^ 2 + r - 2 * w) - μ := by
  have hbase := claim1_small_p_base hc hr hw hμ
  omega

lemma claim1_small_p_prose_lower {d h a0 r μ p : ℤ}
    (hpdef : p = d - h * (a0 + 1)) (hp : p ≤ h) (hμ : μ ≤ r - 2) :
    h * a0 - (r - 2) ≤ d - μ - 2 * p := by
  subst p
  nlinarith

lemma claim1_small_p_prose_positive {c r h a0 : ℤ} (hc : 4 ≤ c)
    (hh : h = c - 1) (hr : r ≤ 2 * c) (ha0 : 3 ≤ a0) :
    0 < h * a0 - (r - 2) := by
  subst h
  have hprod : 0 ≤ (c - 1) * (a0 - 3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

lemma claim1_w_ge_succ {c w a0 : ℤ} (ha0lo : 2 * c + 1 - w ≤ a0)
    (ha0hi : a0 ≤ w) : c + 1 ≤ w := by
  omega

lemma claim1_d_le_sq_sub_two {c r w : ℤ} (hr : r ≤ 2 * c)
    (hw : c + 1 ≤ w) : c ^ 2 + r - 2 * w ≤ c ^ 2 - 2 := by
  omega

lemma device_large_p_first_identity {d h p q a0 a1 w : ℤ}
    (hp : p = d - h * (a0 + 1)) (hq : q = h) (hw : w = a0 + a1) :
    q * a1 - p = h * (w + 1) - d := by
  subst p
  subst q
  subst w
  ring

lemma claim1_large_p_capacity {c d h w : ℤ} (hc : 0 < c)
    (hh : h = c - 1) (hw : c + 1 ≤ w) (hd : d ≤ c ^ 2 - 2) :
    0 < h * (w + 1) - d := by
  subst h
  nlinarith

lemma device_large_p_common_identity {d μ p q h a0 : ℤ}
    (hp : p = d - h * (a0 + 1)) (hq : q = h) :
    d - 2 * μ - (p - q) = h * (a0 + 2) - 2 * μ := by
  subst p
  subst q
  ring

lemma device_large_p_endpoint_identity {d μ p q h a0 : ℤ}
    (hp : p = d - h * (a0 + 1)) (hq : q = h) :
    d - μ - (p + q) = h * a0 - μ := by
  subst p
  subst q
  ring

lemma device_large_p_common_lower {h a0 μ : ℤ} (hμ : μ ≤ 2 * h) :
    h * (a0 - 2) ≤ h * (a0 + 2) - 2 * μ := by
  nlinarith

lemma device_large_p_endpoint_lower {h a0 μ : ℤ} (hμ : μ ≤ 2 * h) :
    h * (a0 - 2) ≤ h * a0 - μ := by
  nlinarith

lemma claim1_large_p_common_nonneg {h a0 μ : ℤ} (hh : 0 ≤ h)
    (ha0 : 2 ≤ a0) (hμ : μ ≤ 2 * h) : 0 ≤ h * (a0 + 2) - 2 * μ := by
  exact (mul_nonneg hh (sub_nonneg.mpr ha0)).trans (device_large_p_common_lower hμ)

lemma claim1_large_p_endpoint_nonneg {h a0 μ : ℤ} (hh : 0 ≤ h)
    (ha0 : 2 ≤ a0) (hμ : μ ≤ 2 * h) : 0 ≤ h * a0 - μ := by
  exact (mul_nonneg hh (sub_nonneg.mpr ha0)).trans (device_large_p_endpoint_lower hμ)

/-! ## The low-neighbourhood branch `2μ ≤ r` -/

lemma lowMu_le_c {c r μ : ℤ} (hr : r ≤ 2 * c) (hμ : 2 * μ ≤ r) : μ ≤ c := by
  omega

lemma sq_sub_three_mul_add_one_pos {c : ℤ} (hc : 4 ≤ c) :
    0 < c ^ 2 - 3 * c + 1 := by
  have hprod : 0 ≤ c * (c - 4) := mul_nonneg (by omega) (by omega)
  nlinarith

lemma lowMu_endpoint_first_step {c r w μ : ℤ} (hr : r ≤ 2 * c)
    (hw : w ≤ r - 2) (hμ : 2 * μ ≤ r) :
    c ^ 2 - 3 * c + 1 ≤ c ^ 2 - w - μ - 1 := by
  omega

lemma lowMu_endpoint_positive {c r w μ : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hμ : 2 * μ ≤ r) :
    0 < c ^ 2 - w - μ - 1 := by
  exact (sq_sub_three_mul_add_one_pos hc).trans_le
    (lowMu_endpoint_first_step hr hw hμ)

lemma sq_sub_four_mul_add_two_nonneg {c : ℤ} (hc : 4 ≤ c) :
    0 ≤ c ^ 2 - 4 * c + 2 := by
  have hprod : 0 ≤ c * (c - 4) := mul_nonneg (by omega) (by omega)
  nlinarith

lemma lowMu_common_first_step {c r w μ : ℤ} (hr : r ≤ 2 * c)
    (hw : w ≤ r - 2) (hμ : 2 * μ ≤ r) :
    c ^ 2 - 4 * c + 2 ≤ c ^ 2 - w - 2 * μ := by
  omega

lemma lowMu_common_nonneg {c r w μ : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hμ : 2 * μ ≤ r) :
    0 ≤ c ^ 2 - w - 2 * μ := by
  exact (sq_sub_four_mul_add_two_nonneg hc).trans (lowMu_common_first_step hr hw hμ)

lemma lowMu_after_extension {c r w a0 μ : ℤ}
    (ha : w + 1 ≤ r - μ) (ha0 : 2 * c - 1 - w ≤ a0) :
    2 * c - r ≤ a0 - μ := by
  omega

lemma lowMu_small_p_endpoint {d h a0 μ p : ℤ}
    (hpdef : p = d - h * (a0 + 1)) (hp : p ≤ h) :
    h * a0 - μ ≤ d - μ - 2 * p := by
  subst p
  nlinarith

lemma lowMu_ha0_nonneg {h a0 μ : ℤ} (hh : 1 ≤ h)
    (hμ0 : 0 ≤ μ) (ha0 : μ ≤ a0) : 0 ≤ h * a0 - μ := by
  have ha00 : 0 ≤ a0 := by omega
  have hprod : 0 ≤ (h - 1) * a0 := mul_nonneg (by omega) ha00
  nlinarith

lemma lowMu_large_p_capacity {c r d h w : ℤ} (hh : h = c - 1)
    (hc : 0 ≤ c) (hw : c ≤ w) (hr : r ≤ 2 * c)
    (hd : d = c ^ 2 + r - 2 * w - 1) :
    h * (w + 1) - d ≥ (c - 1) * (c + 1) - (c ^ 2 - 1) := by
  subst h
  subst d
  have hprod : 0 ≤ (c + 1) * (w - c) := mul_nonneg (by omega) (by omega)
  nlinarith

lemma lowMu_large_p_capacity_zero (c : ℤ) :
    (c - 1) * (c + 1) - (c ^ 2 - 1) = 0 := by ring

lemma lowMu_large_p_capacity_nonneg {c r d h w : ℤ} (hh : h = c - 1)
    (hc : 0 ≤ c) (hw : c ≤ w) (hr : r ≤ 2 * c)
    (hd : d = c ^ 2 + r - 2 * w - 1) : 0 ≤ h * (w + 1) - d := by
  rw [← lowMu_large_p_capacity_zero c]
  exact lowMu_large_p_capacity hh hc hw hr hd

lemma lowMu_common_nonneg_of_a0 {h a0 μ : ℤ} (hh : 1 ≤ h)
    (hμ0 : 0 ≤ μ) (ha0 : μ ≤ a0) (hμh : μ ≤ 2 * h) :
    0 ≤ h * (a0 + 2) - 2 * μ := by
  have ha00 : 0 ≤ a0 := by omega
  have hprod : 0 ≤ (h - 1) * a0 := mul_nonneg (by omega) ha00
  nlinarith

/-! ## The high-neighbourhood branch `r + 1 ≤ 2μ` -/

lemma highMu_deficit_le_pred {c r μ : ℕ} (hr : r ≤ 2 * c)
    (hhigh : r + 1 ≤ 2 * μ) : r - μ ≤ c - 1 := by
  omega

lemma odd_triple_free_lower {c a0 m : ℕ} (ha0 : a0 + (m + 1) = c) :
    c - 1 ≤ a0 + max ((2 * m + 1) - 2) 0 := by
  omega

lemma even_triple_free_lower {c a0 m : ℕ} (hm : 1 ≤ m) (ha0 : a0 + m = c) :
    c - 1 ≤ a0 + max (2 * m - 2) 0 := by
  omega

lemma large_even_triple_free_lower {c a0 lam : ℕ} (hlam : 4 ≤ lam)
    (ha0 : a0 + lam = c) : c - 1 ≤ a0 + ((2 * lam - 3) - 2) := by
  omega

lemma highMu_endpoint_chain {c r w η : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hη : 2 * η ≤ r) :
    0 ≤ c ^ 2 - r - η + 1 ∧
      c ^ 2 - r - η + 1 ≤ c ^ 2 - w - η - 1 := by
  have hprod : 0 ≤ c * (c - 4) := mul_nonneg (by omega) (by omega)
  constructor <;> nlinarith

lemma highMu_common_chain {c r w η : ℤ} (hc : 4 ≤ c)
    (hr : r ≤ 2 * c) (hw : w ≤ r - 2) (hη : 2 * η ≤ r) :
    0 ≤ c ^ 2 - r - 2 * η + 2 ∧
      c ^ 2 - r - 2 * η + 2 ≤ c ^ 2 - w - 2 * η := by
  have hsquare := sq_sub_four_mul_add_two_nonneg hc
  constructor <;> nlinarith

lemma even_between_four_and_seven {a1 : ℕ} (heven : Even a1)
    (hlo : 3 ≤ a1) (hhi : a1 < 8) :
    ∃ lam : ℕ, (lam = 2 ∨ lam = 3) ∧ a1 = 2 * lam := by
  rcases heven with ⟨lam, rfl⟩
  refine ⟨lam, ?_, by omega⟩
  omega

lemma even_parameter_cardinalities {c a0 a1 w lam : ℕ}
    (ha1 : a1 = 2 * lam) (ha0 : a0 + lam = c) (hw : w = a0 + a1) :
    w = c + lam := by
  omega

lemma highMu_shortfall {c r μ a0 lam b : ℕ} (hr : r ≤ 2 * c)
    (hhigh : r + 1 ≤ 2 * μ) (ha0 : a0 + lam = c) (hb : b = r - μ) :
    b - a0 ≤ lam - 1 := by
  have hbpred : b ≤ c - 1 := by simpa [hb] using highMu_deficit_le_pred hr hhigh
  omega

lemma lambda_pred_le_two {lam : ℕ} (hlam : lam = 2 ∨ lam = 3) : lam - 1 ≤ 2 := by
  omega

lemma highMu_final_first_step {c lam μ : ℤ} (hμ : μ ≤ 2 * c - 2) :
    c ^ 2 - 3 * c - lam + 1 ≤ c ^ 2 - c - lam - μ - 1 := by
  omega

lemma highMu_final_nonneg {c lam μ : ℤ} (hc : 4 ≤ c) (hlam : lam ≤ 3)
    (hμ : μ ≤ 2 * c - 2) : 0 ≤ c ^ 2 - c - lam - μ - 1 := by
  have hprod : 0 ≤ c * (c - 4) := mul_nonneg (by omega) (by omega)
  nlinarith

/-! ## The finite cases `c ≤ 3` -/

lemma small_r_ge_three {c r w : ℕ} (hc : 1 ≤ c) (hcw : c ≤ w)
    (hw : w ≤ r - 2) : 3 ≤ r := by
  omega

lemma c_one_impossible {r w : ℕ} (hwlo : 1 ≤ w) (hwhi : w ≤ r - 2)
    (hr : r ≤ 2) : False := by
  omega

lemma c_two_parameters {r w : ℕ} (hwlo : 2 ≤ w) (hwhi : w ≤ r - 2)
    (hr : r ≤ 4) : r = 4 ∧ w = 2 := by
  omega

lemma c_two_partition {a0 a1 w : ℕ} (hw : w = 2) (hsum : w = a0 + a1)
    (ha0 : 1 ≤ a0) (ha1 : 1 ≤ a1) : a0 = 1 ∧ a1 = 1 := by
  omega

lemma c_two_mu_cases {μ r : ℕ} (hr : r = 4) (hμlo : 1 ≤ μ) (hμhi : μ ≤ r - 2) :
    μ = 1 ∨ μ = 2 := by
  omega

lemma c_three_parameters {r w : ℕ} (hwlo : 3 ≤ w) (hwhi : w ≤ r - 2)
    (hr : r ≤ 6) : (w = 3 ∨ w = 4) ∧ (r = 5 ∨ r = 6) := by
  omega

lemma c_three_w_three_partition {a0 a1 w : ℕ} (hw : w = 3)
    (hsum : w = a0 + a1) (ha0 : 2 ≤ a0) (ha1 : 1 ≤ a1) :
    a0 = 2 ∧ a1 = 1 := by
  omega

lemma c_three_w_four_r {r w : ℕ} (hw : w = 4) (hwr : w ≤ r - 2)
    (hr : r ≤ 6) : r = 6 := by
  omega

lemma c_three_w_three_core_bound {r μ : ℕ} (hrlo : 5 ≤ r) (hrhi : r ≤ 6)
    (hμ : μ ≤ r - 2) : 2 * μ < 6 + r := by
  omega

lemma c_three_core_ceil_bound {r : ℕ} (hr : r ≤ 6) :
    (6 + r) ⌈/⌉ 4 ≤ 3 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

lemma c_three_w_four_x_card {r w : ℕ} (hr : r = 6) (hw : w = 4) :
    3 ^ 2 + r - w = 11 := by
  omega

lemma c_three_low_mu_red_degree {μ : ℕ} (hμ : μ ≤ 2) : 9 ≤ 11 - μ := by
  omega

lemma c_three_device_p_bound {a0 p : ℤ} (ha0 : 1 ≤ a0)
    (hp : p = 4 - 2 * a0) : p ≤ 2 := by
  nlinarith

lemma c_three_device_half_bound {μ : ℕ} (hμ : μ ≤ 2) :
    2 ≤ (6 - μ) / 2 := by
  omega

end Erdos518

import ErdosProblems.Erdos1038.Definitions


/-!
# Elementary analysis of the one-cut parameters

This file formalizes the elementary part of the one-cut analysis in Section 6
of the manuscript.  In particular, it proves the basic ranges of `qCeiling`,
`H`, `s`, and `A`, and studies the scalar soft-edge function from (6.4).
-/

open Set

namespace Erdos1038

noncomputable section

/-! ## The parameter interval -/

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

theorem sqrt_two_lt_ten_sevenths : Real.sqrt 2 < 10 / 7 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

theorem eleven_eighths_lt_sqrt_two : (11 / 8 : ℝ) < Real.sqrt 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

theorem qCeiling_eq_sq : qCeiling = (Real.sqrt 2 - 1) ^ 2 := by
  rw [qCeiling]
  nlinarith [sqrt_two_sq]

theorem qCeiling_pos : 0 < qCeiling := by
  rw [qCeiling_eq_sq]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr one_lt_sqrt_two.ne')

theorem qCeiling_lt_one : qCeiling < 1 := by
  rw [qCeiling]
  nlinarith [one_lt_sqrt_two]

theorem qCeiling_lt_one_fourth : qCeiling < 1 / 4 := by
  rw [qCeiling]
  nlinarith [eleven_eighths_lt_sqrt_two]

theorem qCeiling_mem_Ioo : qCeiling ∈ Ioo (0 : ℝ) 1 :=
  ⟨qCeiling_pos, qCeiling_lt_one⟩

theorem one_seventh_lt_qCeiling : (1 / 7 : ℝ) < qCeiling := by
  rw [qCeiling]
  nlinarith [sqrt_two_lt_ten_sevenths]

theorem one_ninth_lt_qCeiling : (1 / 9 : ℝ) < qCeiling := by
  exact (by norm_num : (1 / 9 : ℝ) < 1 / 7) |>.trans one_seventh_lt_qCeiling

theorem mem_Ioo_zero_qCeiling_imp_lt_one {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : q < 1 :=
  hq.2.trans qCeiling_lt_one

/-! ## Algebraic identities and ranges for `H` and `s` -/

theorem one_add_pos {q : ℝ} (hq : 0 < q) : 0 < 1 + q := by
  linarith

theorem H_eq_q_mul (q : ℝ) : H q = q * (2 / (1 + q) ^ 2) := by
  rw [H]
  ring

theorem one_sub_s (q : ℝ) (hq : q ≠ -1) : 1 - s q = 2 * q / (1 + q) := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  rw [s]
  field_simp [hden]
  ring

theorem one_add_s (q : ℝ) (hq : q ≠ -1) : 1 + s q = 2 / (1 + q) := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  rw [s]
  field_simp [hden]
  ring

theorem one_sub_s_sq (q : ℝ) (hq : q ≠ -1) : 1 - (s q) ^ 2 = 2 * H q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  rw [s, H]
  field_simp [hden]
  ring

theorem H_eq_half_one_sub_s_sq (q : ℝ) (hq : q ≠ -1) :
    H q = (1 - (s q) ^ 2) / 2 := by
  nlinarith [one_sub_s_sq q hq]

theorem H_pos {q : ℝ} (hq : 0 < q) : 0 < H q := by
  rw [H]
  positivity

theorem H_lt_one {q : ℝ} (hq : 0 < q) : H q < 1 := by
  rw [H]
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (one_add_pos hq)
  rw [div_lt_iff₀ hden]
  nlinarith [sq_nonneg (q - 1)]

theorem H_lt_one_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : H q < 1 :=
  H_lt_one hq.1

theorem H_mem_Ioo {q : ℝ} (hq : 0 < q) : H q ∈ Ioo (0 : ℝ) 1 :=
  ⟨H_pos hq, H_lt_one hq⟩

theorem H_mem_Ioo_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) :
    H q ∈ Ioo (0 : ℝ) 1 :=
  H_mem_Ioo hq.1

theorem H_lt_half {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : H q < 1 / 2 := by
  rw [H]
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (one_add_pos hq)
  rw [div_lt_iff₀ hden]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hq1.ne)]

theorem q_lt_H_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : q < H q := by
  rw [H]
  have hq_fourth : q < 1 / 4 := hq.2.trans qCeiling_lt_one_fourth
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (one_add_pos hq.1)
  rw [lt_div_iff₀ hden]
  have hprod : 0 < q * (1 / 4 - q) := mul_pos hq.1 (sub_pos.mpr hq_fourth)
  have hsquare : (1 + q) ^ 2 < 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left hsquare hq.1]

theorem s_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 < s q := by
  rw [s]
  exact div_pos (sub_pos.mpr hq1) (one_add_pos hq)

theorem s_lt_one {q : ℝ} (hq : 0 < q) : s q < 1 := by
  rw [s]
  have hden : 0 < 1 + q := one_add_pos hq
  rw [div_lt_iff₀ hden]
  linarith

theorem s_mem_Ioo {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : s q ∈ Ioo (0 : ℝ) 1 :=
  ⟨s_pos hq hq1, s_lt_one hq⟩

theorem s_mem_Ioo_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : s q ∈ Ioo (0 : ℝ) 1 :=
  s_mem_Ioo hq.1 (mem_Ioo_zero_qCeiling_imp_lt_one hq)

/-! ## Logarithmic facts and the range of `A` -/

theorem log_q_neg {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : Real.log q < 0 :=
  Real.log_neg hq hq1

theorem log_q_neg_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : Real.log q < 0 :=
  log_q_neg hq.1 (mem_Ioo_zero_qCeiling_imp_lt_one hq)

theorem log_q_ne_zero {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : Real.log q ≠ 0 :=
  (log_q_neg hq hq1).ne

theorem log_q_ne_zero_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) :
    Real.log q ≠ 0 :=
  (log_q_neg_of_mem_Ioo hq).ne

theorem log_H_neg {q : ℝ} (hq : 0 < q) : Real.log (H q) < 0 :=
  Real.log_neg (H_pos hq) (H_lt_one hq)

theorem log_H_neg_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) :
    Real.log (H q) < 0 :=
  log_H_neg hq.1

theorem log_q_lt_log_H_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) :
    Real.log q < Real.log (H q) :=
  Real.log_lt_log hq.1 (q_lt_H_of_mem_Ioo hq)

theorem A_pos_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : 0 < A q := by
  rw [A]
  exact div_pos_of_neg_of_neg (log_H_neg_of_mem_Ioo hq) (log_q_neg_of_mem_Ioo hq)

theorem A_lt_one_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) : A q < 1 := by
  rw [A, div_lt_one_of_neg (log_q_neg_of_mem_Ioo hq)]
  exact log_q_lt_log_H_of_mem_Ioo hq

theorem A_mem_Ioo_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 qCeiling) :
    A q ∈ Ioo (0 : ℝ) 1 :=
  ⟨A_pos_of_mem_Ioo hq, A_lt_one_of_mem_Ioo hq⟩

theorem log_H_decomposition {q : ℝ} (hq : 0 < q) :
    Real.log (H q) = Real.log q + Real.log (2 / (1 + q) ^ 2) := by
  rw [H_eq_q_mul, Real.log_mul hq.ne']
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (one_add_pos hq)
  exact (div_pos (by norm_num) hden).ne'

/-! ## The scalar soft-edge function -/

/-- The function `f` in equations (6.4)--(6.5) of the manuscript. -/
def softFunction (q : ℝ) : ℝ :=
  (1 + q) * Real.log (2 / (1 + q) ^ 2) + 2 * q * Real.log q

theorem hasDerivAt_log_two_div_one_add_sq {q : ℝ} (hq : q ≠ -1) :
    HasDerivAt (fun x : ℝ ↦ Real.log (2 / (1 + x) ^ 2)) (-2 / (1 + q)) q := by
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  have hadd : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 q := by
    convert! (hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q) using 1
    all_goals simp
  have hpow : HasDerivAt (fun x : ℝ ↦ (1 + x) ^ 2) (2 * (1 + q)) q := by
    convert! hadd.pow 2 using 1
    all_goals ring
  have hquot :
      HasDerivAt (fun x : ℝ ↦ 2 / (1 + x) ^ 2)
        (-4 * (1 + q) / ((1 + q) ^ 2) ^ 2) q := by
    convert! (hasDerivAt_const q (2 : ℝ)).div hpow (pow_ne_zero 2 hden) using 1
    all_goals ring
  have harg : 2 / (1 + q) ^ 2 ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 hden)
  convert! hquot.log harg using 1
  field_simp [hden]
  ring

theorem softFunction_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt softFunction
      (Real.log (2 / (1 + q) ^ 2) + 2 * Real.log q) q := by
  have hq_neg_one : q ≠ -1 := by linarith
  have hden : 1 + q ≠ 0 := by linarith
  have hadd : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 q := by
    convert! (hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q) using 1
    all_goals simp
  have hfirst := hadd.mul (hasDerivAt_log_two_div_one_add_sq hq_neg_one)
  have hsecond := (Real.hasDerivAt_mul_log hq.ne').const_mul 2
  convert! hfirst.add hsecond using 1
  · funext x
    rw [softFunction]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · field_simp [hden]
    ring

theorem softFunction_deriv {q : ℝ} (hq : 0 < q) :
    deriv softFunction q = Real.log (2 / (1 + q) ^ 2) + 2 * Real.log q :=
  (softFunction_hasDerivAt hq).deriv

theorem softFunction_deriv_eq_log {q : ℝ} (hq : 0 < q) :
    deriv softFunction q = Real.log (2 * q ^ 2 / (1 + q) ^ 2) := by
  rw [softFunction_deriv hq]
  have hden : (1 + q) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have hq_sq : q ^ 2 ≠ 0 := pow_ne_zero 2 hq.ne'
  calc
    Real.log (2 / (1 + q) ^ 2) + 2 * Real.log q =
        (Real.log 2 - Real.log ((1 + q) ^ 2)) + 2 * Real.log q := by
          rw [Real.log_div (by norm_num) hden]
    _ = (Real.log 2 + Real.log (q ^ 2)) - Real.log ((1 + q) ^ 2) := by
          rw [Real.log_pow]
          norm_num
          ring
    _ = Real.log (2 * q ^ 2) - Real.log ((1 + q) ^ 2) := by
          rw [Real.log_mul (by norm_num) hq_sq]
    _ = Real.log (2 * q ^ 2 / (1 + q) ^ 2) := by
          rw [Real.log_div (mul_ne_zero (by norm_num) hq_sq) hden]

theorem softFunction_deriv_neg {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    deriv softFunction q < 0 := by
  rw [softFunction_deriv_eq_log hq]
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (one_add_pos hq)
  have hprod : 0 < q * (1 - q) := mul_pos hq (sub_pos.mpr hq1)
  have hratio_lt : 2 * q ^ 2 / (1 + q) ^ 2 < 1 := by
    rw [div_lt_one hden]
    nlinarith
  exact Real.log_neg (by positivity) hratio_lt

theorem softFunction_continuousOn_Ioo_zero_one :
    ContinuousOn softFunction (Ioo (0 : ℝ) 1) := by
  intro q hq
  exact (softFunction_hasDerivAt hq.1).continuousAt.continuousWithinAt

theorem softFunction_strictAntiOn_Ioo_zero_one :
    StrictAntiOn softFunction (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1) softFunction_continuousOn_Ioo_zero_one
  rw [interior_Ioo]
  intro q hq
  exact softFunction_deriv_neg hq.1 hq.2

theorem softFunction_continuousOn_Ioo_zero_qCeiling :
    ContinuousOn softFunction (Ioo (0 : ℝ) qCeiling) :=
  softFunction_continuousOn_Ioo_zero_one.mono fun _ hq ↦
    ⟨hq.1, mem_Ioo_zero_qCeiling_imp_lt_one hq⟩

theorem softFunction_strictAntiOn_Ioo_zero_qCeiling :
    StrictAntiOn softFunction (Ioo (0 : ℝ) qCeiling) :=
  softFunction_strictAntiOn_Ioo_zero_one.mono fun _ hq ↦
    ⟨hq.1, mem_Ioo_zero_qCeiling_imp_lt_one hq⟩

theorem softFunction_one_ninth_pos : 0 < softFunction (1 / 9) := by
  have harg : (1 : ℝ) < (81 / 50 : ℝ) ^ 5 / 9 := by norm_num
  have hlog : 0 < Real.log ((81 / 50 : ℝ) ^ 5 / 9) := Real.log_pos harg
  have hid :
      Real.log ((81 / 50 : ℝ) ^ 5 / 9) =
        5 * Real.log (81 / 50) + Real.log (1 / 9) := by
    rw [Real.log_div (x := (81 / 50 : ℝ) ^ 5) (y := 9)
      (pow_ne_zero 5 (by norm_num)) (by norm_num), Real.log_pow,
      Real.log_div (x := (81 : ℝ)) (y := 50) (by norm_num) (by norm_num),
      Real.log_div (x := (1 : ℝ)) (y := 9) (by norm_num) (by norm_num), Real.log_one]
    norm_num
    ring
  rw [hid] at hlog
  norm_num [softFunction]
  nlinarith

theorem softFunction_one_seventh_neg : softFunction (1 / 7) < 0 := by
  have harg_pos : 0 < (49 / 32 : ℝ) ^ 4 / 7 := by positivity
  have harg_lt : (49 / 32 : ℝ) ^ 4 / 7 < 1 := by norm_num
  have hlog : Real.log ((49 / 32 : ℝ) ^ 4 / 7) < 0 :=
    Real.log_neg harg_pos harg_lt
  have hid :
      Real.log ((49 / 32 : ℝ) ^ 4 / 7) =
        4 * Real.log (49 / 32) + Real.log (1 / 7) := by
    rw [Real.log_div (x := (49 / 32 : ℝ) ^ 4) (y := 7)
      (pow_ne_zero 4 (by norm_num)) (by norm_num), Real.log_pow,
      Real.log_div (x := (49 : ℝ)) (y := 32) (by norm_num) (by norm_num),
      Real.log_div (x := (1 : ℝ)) (y := 7) (by norm_num) (by norm_num), Real.log_one]
    norm_num
    ring
  rw [hid] at hlog
  norm_num [softFunction]
  nlinarith

/-! ## Equivalence with the soft-edge equation and its unique root -/

theorem softFunction_eq_mul_A_sub_s {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    softFunction q = (1 + q) * Real.log q * (A q - s q) := by
  have hlog : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  have hden : 1 + q ≠ 0 := by linarith
  rw [softFunction, A, s, log_H_decomposition hq]
  field_simp [hlog, hden]
  ring

theorem A_eq_s_iff_softFunction_eq_zero {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    A q = s q ↔ softFunction q = 0 := by
  rw [softFunction_eq_mul_A_sub_s hq hq1]
  have hcoeff : (1 + q) * Real.log q ≠ 0 :=
    mul_ne_zero (by linarith) (log_q_ne_zero hq hq1)
  constructor
  · intro h
    rw [h, sub_self, mul_zero]
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hcoeff)

theorem A_le_s_iff_softFunction_nonneg {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    A q ≤ s q ↔ 0 ≤ softFunction q := by
  rw [softFunction_eq_mul_A_sub_s hq hq1]
  have hcoeff : (1 + q) * Real.log q < 0 :=
    mul_neg_of_pos_of_neg (one_add_pos hq) (log_q_neg hq hq1)
  constructor
  · intro h
    exact mul_nonneg_of_nonpos_of_nonpos hcoeff.le (sub_nonpos.mpr h)
  · intro h
    by_contra hle
    have hsub : 0 < A q - s q := sub_pos.mpr (lt_of_not_ge hle)
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos hcoeff hsub)

theorem A_lt_s_iff_softFunction_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    A q < s q ↔ 0 < softFunction q := by
  rw [softFunction_eq_mul_A_sub_s hq hq1]
  have hcoeff : (1 + q) * Real.log q < 0 :=
    mul_neg_of_pos_of_neg (one_add_pos hq) (log_q_neg hq hq1)
  constructor
  · intro h
    exact mul_pos_of_neg_of_neg hcoeff (sub_neg.mpr h)
  · intro h
    by_contra hlt
    have hsub : 0 ≤ A q - s q := sub_nonneg.mpr (not_lt.mp hlt)
    exact (not_le_of_gt h) (mul_nonpos_of_nonpos_of_nonneg hcoeff.le hsub)

theorem exists_softFunction_root_in_one_ninth_one_seventh :
    ∃ q ∈ Ioo (1 / 9 : ℝ) (1 / 7), softFunction q = 0 := by
  have hab : (1 / 9 : ℝ) ≤ 1 / 7 := by norm_num
  have hcont : ContinuousOn softFunction (Icc (1 / 9 : ℝ) (1 / 7)) :=
    softFunction_continuousOn_Ioo_zero_one.mono fun x hx ↦ by
      constructor <;> norm_num at hx ⊢ <;> linarith
  have hzero :
      (0 : ℝ) ∈ Icc (softFunction (1 / 7)) (softFunction (1 / 9)) :=
    ⟨softFunction_one_seventh_neg.le, softFunction_one_ninth_pos.le⟩
  obtain ⟨q, hq, hqzero⟩ := intermediate_value_Icc' hab hcont hzero
  have hq_ne_left : q ≠ (1 / 9 : ℝ) := by
    intro h
    subst q
    linarith [softFunction_one_ninth_pos]
  have hq_ne_right : q ≠ (1 / 7 : ℝ) := by
    intro h
    subst q
    linarith [softFunction_one_seventh_neg]
  exact ⟨q, ⟨lt_of_le_of_ne hq.1 hq_ne_left.symm, lt_of_le_of_ne hq.2 hq_ne_right⟩,
    hqzero⟩

theorem exists_softFunction_root :
    ∃ q ∈ Ioo (0 : ℝ) qCeiling, softFunction q = 0 := by
  obtain ⟨q, hq, hzero⟩ := exists_softFunction_root_in_one_ninth_one_seventh
  exact ⟨q, ⟨(by exact (by norm_num : (0 : ℝ) < 1 / 9) |>.trans hq.1),
    hq.2.trans one_seventh_lt_qCeiling⟩, hzero⟩

theorem existsUnique_softFunction_root :
    ∃! q : ℝ, q ∈ Ioo 0 qCeiling ∧ softFunction q = 0 := by
  obtain ⟨q, hq, hzero⟩ := exists_softFunction_root
  refine ⟨q, ⟨hq, hzero⟩, ?_⟩
  intro r hr
  exact (softFunction_strictAntiOn_Ioo_zero_qCeiling.injOn hq hr.1
    (hzero.trans hr.2.symm)).symm

theorem isSoftRoot_iff_softFunction_root {q : ℝ} :
    IsSoftRoot q ↔ q ∈ Ioo 0 qCeiling ∧ softFunction q = 0 := by
  constructor
  · intro h
    exact ⟨h.1,
      (A_eq_s_iff_softFunction_eq_zero h.1.1
        (mem_Ioo_zero_qCeiling_imp_lt_one h.1)).mp h.2⟩
  · intro h
    exact ⟨h.1,
      (A_eq_s_iff_softFunction_eq_zero h.1.1
        (mem_Ioo_zero_qCeiling_imp_lt_one h.1)).mpr h.2⟩

theorem existsUnique_isSoftRoot : ∃! q : ℝ, IsSoftRoot q := by
  obtain ⟨q, hq, huniq⟩ := existsUnique_softFunction_root
  refine ⟨q, isSoftRoot_iff_softFunction_root.mpr hq, ?_⟩
  intro r hr
  exact huniq r (isSoftRoot_iff_softFunction_root.mp hr)

theorem isSoftRoot_qSoft : IsSoftRoot qSoft := by
  obtain ⟨q, hq, huniq⟩ := existsUnique_isSoftRoot
  have hset : {r : ℝ | IsSoftRoot r} = {q} := by
    ext r
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact huniq r
    · rintro rfl
      exact hq
  have hqSoft : qSoft = q := by
    rw [qSoft, hset]
    exact csInf_singleton q
  rwa [hqSoft]

theorem qSoft_mem_Ioo : qSoft ∈ Ioo (0 : ℝ) qCeiling :=
  isSoftRoot_qSoft.1

theorem A_qSoft_eq_s_qSoft : A qSoft = s qSoft :=
  isSoftRoot_qSoft.2

theorem softFunction_qSoft_eq_zero : softFunction qSoft = 0 :=
  (isSoftRoot_iff_softFunction_root.mp isSoftRoot_qSoft).2

theorem isSoftRoot_eq_qSoft {q : ℝ} (hq : IsSoftRoot q) : q = qSoft := by
  have hq' := isSoftRoot_iff_softFunction_root.mp hq
  exact softFunction_strictAntiOn_Ioo_zero_qCeiling.injOn hq'.1 qSoft_mem_Ioo
    (hq'.2.trans softFunction_qSoft_eq_zero.symm)

theorem qSoft_mem_Ioo_one_ninth_one_seventh :
    qSoft ∈ Ioo (1 / 9 : ℝ) (1 / 7) := by
  obtain ⟨q, hq, hzero⟩ := exists_softFunction_root_in_one_ninth_one_seventh
  have hq_domain : q ∈ Ioo (0 : ℝ) qCeiling :=
    ⟨(by exact (by norm_num : (0 : ℝ) < 1 / 9) |>.trans hq.1),
      hq.2.trans one_seventh_lt_qCeiling⟩
  have heq : q = qSoft :=
    softFunction_strictAntiOn_Ioo_zero_qCeiling.injOn hq_domain qSoft_mem_Ioo
      (hzero.trans softFunction_qSoft_eq_zero.symm)
  rwa [← heq]

theorem A_qSoft_mem_Ioo : A qSoft ∈ Ioo (0 : ℝ) 1 :=
  A_mem_Ioo_of_mem_Ioo qSoft_mem_Ioo

theorem s_qSoft_mem_Ioo : s qSoft ∈ Ioo (0 : ℝ) 1 :=
  s_mem_Ioo_of_mem_Ioo qSoft_mem_Ioo

end

end Erdos1038

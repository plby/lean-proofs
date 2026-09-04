import ErdosProblems.Erdos490.Basic
import Util.MertensThird

noncomputable section

namespace Erdos490

open Finset BigOperators Nat Real Filter
open scoped Topology

set_option maxHeartbeats 800000

def factorialKernel (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

lemma factorialKernel_nonneg (n : ℕ) : 0 ≤ factorialKernel n := by
  unfold factorialKernel
  omega

lemma factorialKernel_eq_one {n : ℕ} (h₁ : 1 ≤ n) (h₆ : n < 6) :
    factorialKernel n = 1 := by
  interval_cases n <;> norm_num [factorialKernel]

def factorialCombination (n : ℕ) : ℝ :=
  Real.log (n.factorial) - Real.log ((n / 2).factorial) -
    Real.log ((n / 3).factorial) - Real.log ((n / 5).factorial) +
      Real.log ((n / 30).factorial)

lemma log_factorial_vonMangoldt (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (n / d : ℕ) =
      Real.log (n.factorial) := by
  have h_interchange :
      ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt d =
        ∑ d ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt d * (if d ∣ m then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Finset.mem_Icc.mp hm).1,
        (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hd).trans (Finset.mem_Icc.mp hm).2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by have := (Finset.mem_Icc.mp hm).1; omega⟩
  have h_inner (d : ℕ) (hd : d ∈ Finset.Icc 1 n) :
      ∑ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (if d ∣ m then 1 else 0) =
        ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hset : (Finset.Icc 1 n).filter (d ∣ ·) =
        (Finset.Icc 1 (n / d)).image (d * ·) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hm1, hmn⟩, hdm⟩
        exact ⟨m / d, ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdm) hd0,
          Nat.div_le_div_right hmn⟩, Nat.mul_div_cancel' hdm⟩
      · rintro ⟨j, ⟨hj1, hjn⟩, rfl⟩
        exact ⟨⟨by nlinarith, (Nat.mul_le_mul_left d hjn).trans (Nat.mul_div_le n d)⟩,
          dvd_mul_right d j⟩
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const]
    rw [hset, Finset.card_image_of_injective _ (fun a b h => mul_left_cancel₀ hd0.ne' h)]
    simp [nsmul_eq_mul, mul_comm]
  rw [← Finset.sum_congr rfl h_inner, ← h_interchange]
  simp only [ArithmeticFunction.vonMangoldt_sum]
  clear h_inner h_interchange
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring

lemma log_factorial_vonMangoldt_of_le {m n : ℕ} (hmn : m ≤ n) :
    Real.log (m.factorial) =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * (m / d : ℕ) := by
  rw [← log_factorial_vonMangoldt]
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hmn)
  intro d hd hdm
  have hmd : m < d := by
    simp only [Finset.mem_Icc] at hd hdm
    omega
  simp [Nat.div_eq_of_lt hmd]

lemma factorialCombination_eq_sum (n : ℕ) :
    factorialCombination n =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d * factorialKernel (n / d) := by
  unfold factorialCombination
  rw [log_factorial_vonMangoldt_of_le (le_refl n),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 2),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 3),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 5),
    log_factorial_vonMangoldt_of_le (Nat.div_le_self n 30)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [factorialKernel, Int.cast_add, Int.cast_sub, Int.cast_natCast,
    Nat.div_div_eq_div_mul]
  simp only [mul_comm d]
  ring

lemma chebyshevPsi_nat_eq_sum (n : ℕ) :
    chebyshevPsi n = ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d := by
  unfold chebyshevPsi
  erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num

lemma chebyshevPsi_factorial_step (n : ℕ) :
    chebyshevPsi n ≤ factorialCombination n + chebyshevPsi (n / 6 : ℕ) := by
  rw [chebyshevPsi_nat_eq_sum, factorialCombination_eq_sum, chebyshevPsi_nat_eq_sum]
  have hsmall : (∑ d ∈ Finset.Icc 1 (n / 6), ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ Finset.Icc 1 n, if d ≤ n / 6 then ArithmeticFunction.vonMangoldt d else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hle := Nat.div_le_self n 6
    omega
  rw [hsmall, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hkernel : (0 : ℝ) ≤ factorialKernel (n / d) := by
    exact_mod_cast factorialKernel_nonneg (n / d)
  split_ifs with hsmall
  · linarith [mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d)) hkernel]
  · have h₁ : 1 ≤ n / d := Nat.div_pos (Finset.mem_Icc.mp hd).2 hdpos
    have h₆ : n / d < 6 := (Nat.div_lt_iff_lt_mul hdpos).mpr (by omega)
    simp [factorialKernel_eq_one h₁ h₆]

lemma log_factorial_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n.factorial) := by
  induction hn
  · norm_num
  simp_all +decide only [succ_eq_add_one, cast_add, cast_one]
  rw [Nat.factorial_succ, Nat.cast_mul]
  rw [Real.log_mul (by positivity) (by positivity)]
  have h_log : ∀ m : ℕ, 1 ≤ m → Real.log (m + 1) ≤ Real.log m + 1 / m := by
    intro m hm
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, Real.exp_log (by positivity)]
    nlinarith [Real.add_one_le_exp (1 / (m : ℝ)),
      one_div_mul_cancel (by positivity : (m : ℝ) ≠ 0)]
  have := h_log _ ‹_›
  norm_num at *
  nlinarith [inv_mul_cancel₀ (by positivity : ((Nat.cast : ℕ → ℝ) ‹_›) ≠ 0)]

def factorialEntropy : ℝ :=
  (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5

lemma factorialEntropy_lt : factorialEntropy < 922 / 1000 := by
  unfold factorialEntropy
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

lemma factorialCombination_mul30_bound (m : ℕ) (hm : 0 < m) :
    factorialCombination (30 * m) ≤
      (922 / 1000 : ℝ) * (30 * m) + 2 * Real.log (30 * m) := by
  have h2 : 30 * m / 2 = 15 * m := by omega
  have h3 : 30 * m / 3 = 10 * m := by omega
  have h5 : 30 * m / 5 = 6 * m := by omega
  have h30 : 30 * m / 30 = m := by omega
  unfold factorialCombination
  rw [h2, h3, h5, h30]
  have hu := _root_.log_factorial_le (30 * m) (by omega)
  have hu' := _root_.log_factorial_le m hm
  have hl2 := log_factorial_lower (15 * m) (by omega)
  have hl3 := log_factorial_lower (10 * m) (by omega)
  have hl5 := log_factorial_lower (6 * m) (by omega)
  push_cast at hu hu' hl2 hl3 hl5 ⊢
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlogm : Real.log (m : ℝ) ≤ Real.log (30 * (m : ℝ)) :=
    Real.log_le_log hmR (by linarith)
  have hlog30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hlog15 : Real.log (15 : ℝ) = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hmain :
      (30 * (m : ℝ)) * Real.log (30 * m) - (15 * m) * Real.log (15 * m) -
        (10 * m) * Real.log (10 * m) - (6 * m) * Real.log (6 * m) +
          m * Real.log m = factorialEntropy * (30 * m) := by
    simp only [Real.log_mul (by norm_num : (30 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (15 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hmR.ne',
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hmR.ne',
      hlog30, hlog15, hlog10, hlog6, factorialEntropy]
    ring
  have hEntropy := mul_le_mul_of_nonneg_right factorialEntropy_lt.le (by positivity :
    (0 : ℝ) ≤ 30 * m)
  linarith

lemma chebyshevPsi_nat_le_two (n : ℕ) : chebyshevPsi n ≤ 2 * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [chebyshevPsi]
  have h := _root_.chebyshevPsi_le n hn
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound : (2 : ℝ) * n * Real.log 2 ≤ 2 * n := by nlinarith
  have h' : chebyshevPsi n ≤ 2 * n * Real.log 2 := by
    simpa [chebyshevPsi, _root_.chebyshevPsi] using h
  exact h'.trans hbound

lemma chebyshevPsi_multiple_bound (m : ℕ) (hm : 0 < m) :
    chebyshevPsi (6480 * m : ℕ) ≤
      (358697 / 324000 : ℝ) * (6480 * m) + 8 * Real.log (6480 * m) := by
  have h₀ := chebyshevPsi_factorial_step (6480 * m)
  have h₁ := chebyshevPsi_factorial_step (1080 * m)
  have h₂ := chebyshevPsi_factorial_step (180 * m)
  have h₃ := chebyshevPsi_factorial_step (30 * m)
  have hd₀ : 6480 * m / 6 = 1080 * m := by omega
  have hd₁ : 1080 * m / 6 = 180 * m := by omega
  have hd₂ : 180 * m / 6 = 30 * m := by omega
  have hd₃ : 30 * m / 6 = 5 * m := by omega
  rw [hd₀] at h₀
  rw [hd₁] at h₁
  rw [hd₂] at h₂
  rw [hd₃] at h₃
  have ht₀ := factorialCombination_mul30_bound (216 * m) (by omega)
  have ht₁ := factorialCombination_mul30_bound (36 * m) (by omega)
  have ht₂ := factorialCombination_mul30_bound (6 * m) (by omega)
  have ht₃ := factorialCombination_mul30_bound m hm
  norm_num [← mul_assoc] at ht₀ ht₁ ht₂
  have ht₄ := chebyshevPsi_nat_le_two (5 * m)
  have hl₁ : Real.log (1080 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hl₂ : Real.log (180 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hl₃ : Real.log (30 * (m : ℝ)) ≤ Real.log (6480 * m) :=
    Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  push_cast at h₀ h₁ h₂ h₃ ht₄ ⊢
  linarith

lemma chebyshevPsi_mono : Monotone chebyshevPsi := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hxy)))
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- An elementary eventual Chebyshev upper bound, obtained solely from
factorial inequalities and a nonnegative periodic floor kernel. -/
theorem elementary_chebyshev_bound :
    ∃ T : ℝ, ∀ x : ℝ, T ≤ x → chebyshevPsi x ≤ (111 / 100) * x := by
  let c : ℝ := 358697 / 324000
  let δ : ℝ := 111 / 100 - c
  let K : ℝ := c * 6481 + 8 * Real.log 2
  have hδ : 0 < δ := by norm_num [δ, c]
  have hc : 0 ≤ c := by norm_num [c]
  have hlog := Real.isLittleO_log_id_atTop.def (by positivity : 0 < δ / 16)
  apply Filter.eventually_atTop.mp
  filter_upwards [hlog, eventually_ge_atTop (6481 : ℝ),
    eventually_ge_atTop (2 * K / δ)] with x hlog hx hK
  have hxpos : 0 < x := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hxpos.le,
    abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ x))] at hlog
  have hK' : 2 * K ≤ x * δ := (div_le_iff₀ hδ).mp hK
  let m : ℕ := ⌈x⌉₊ / 6480 + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hceilLower : ⌈x⌉₊ ≤ 6480 * m := by
    dsimp [m]
    have hmod := Nat.mod_lt ⌈x⌉₊ (by norm_num : 0 < 6480)
    have hdiv := Nat.div_add_mod ⌈x⌉₊ 6480
    omega
  have hceilUpper : 6480 * m ≤ ⌈x⌉₊ + 6480 := by
    dsimp [m]
    have hdiv := Nat.div_mul_le_self ⌈x⌉₊ 6480
    omega
  have hYlower : x ≤ (6480 * m : ℕ) :=
    (Nat.le_ceil x).trans (by exact_mod_cast hceilLower)
  have hYupper : ((6480 * m : ℕ) : ℝ) ≤ x + 6481 := by
    have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    have h := Nat.cast_le (α := ℝ).mpr hceilUpper
    push_cast at h
    push_cast
    linarith
  have hYpos : (0 : ℝ) < (6480 * m : ℕ) := by positivity
  have hlogY : Real.log ((6480 * m : ℕ) : ℝ) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
    apply Real.log_le_log hYpos
    linarith
  have hpsi := chebyshevPsi_multiple_bound m hm
  have hmono := chebyshevPsi_mono hYlower
  have hmain : c * ((6480 * m : ℕ) : ℝ) ≤ c * (x + 6481) :=
    mul_le_mul_of_nonneg_left hYupper hc
  dsimp [c, δ, K] at *
  push_cast at hmain hlogY hmono hpsi
  linarith

#print axioms elementary_chebyshev_bound

end Erdos490

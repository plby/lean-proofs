/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Explicit elementary Chebyshev estimates for Erdős 175

This file develops the five-term Chebyshev weight

`⌊t⌋ - ⌊t/2⌋ - ⌊t/3⌋ - ⌊t/5⌋ + ⌊t/30⌋`.

The weight is nonnegative, is at least one on `[1,6)`, and is at most one.
Together with the exact von Mangoldt--factorial convolution and explicit
Stirling remainders, these facts give effective lower and upper estimates for
`Chebyshev.psi`.  The constants are intentionally coarser than the best known
ones; the cutoff in Erdős 175 is so large that these bounds are ample.
-/

namespace Erdos175.ExplicitChebyshev

open ArithmeticFunction Finset Real
open scoped Chebyshev

noncomputable section

/-- The floor-weight used in Chebyshev's five-term approximation. -/
def chi (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

lemma chi_add_thirty (n : ℕ) : chi (n + 30) = chi n := by
  unfold chi
  norm_num [Nat.add_div_of_dvd_left]
  omega

lemma chi_nonneg (n : ℕ) : 0 ≤ chi n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 30
      · interval_cases n <;> norm_num [chi]
      · have hsub : n - 30 < n := by omega
        have hadd : n - 30 + 30 = n := by omega
        rw [← hadd, chi_add_thirty]
        exact ih (n - 30) hsub

lemma chi_le_one (n : ℕ) : chi n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 30
      · interval_cases n <;> norm_num [chi]
      · have hsub : n - 30 < n := by omega
        have hadd : n - 30 + 30 = n := by omega
        rw [← hadd, chi_add_thirty]
        exact ih (n - 30) hsub

lemma one_le_chi_of_lt_six {n : ℕ} (hn1 : 1 ≤ n) (hn6 : n < 6) :
    1 ≤ chi n := by
  interval_cases n <;> norm_num [chi]

/-- The floor-weight evaluated on a nonnegative real number. -/
def chiReal (x : ℝ) : ℝ := (chi ⌊x⌋₊ : ℤ)

lemma chiReal_eq_cast (x : ℝ) : chiReal x = (chi ⌊x⌋₊ : ℤ) := by
  rfl

lemma chiReal_nonneg (x : ℝ) : 0 ≤ chiReal x := by
  rw [chiReal_eq_cast]
  exact_mod_cast chi_nonneg ⌊x⌋₊

lemma chiReal_le_one (x : ℝ) : chiReal x ≤ 1 := by
  rw [chiReal_eq_cast]
  exact_mod_cast chi_le_one ⌊x⌋₊

lemma one_le_chiReal {x : ℝ} (hx1 : 1 ≤ x) (hx6 : x < 6) :
    1 ≤ chiReal x := by
  have hfloor1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx1
  have hfloor6 : ⌊x⌋₊ < 6 := (Nat.floor_lt (by linarith : 0 ≤ x)).2 hx6
  rw [chiReal_eq_cast]
  exact_mod_cast one_le_chi_of_lt_six hfloor1 hfloor6

/-- The floor-weighted von Mangoldt convolution. -/
def mangoldtFloorConvolution (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ)

/-- Exact factorial convolution for von Mangoldt's function. -/
lemma mangoldtFloorConvolution_eq_log_factorial (n : ℕ) :
    mangoldtFloorConvolution n = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp [mangoldtFloorConvolution]
  | succ n ih =>
      have hdivisors :
          (n + 1).divisors =
            insert (n + 1) ((Icc 1 n).filter (· ∣ n + 1)) := by
        ext d
        simp only [Nat.mem_divisors, mem_insert, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hd, hn⟩
          by_cases heq : d = n + 1
          · exact Or.inl heq
          · right
            have hd0 : d ≠ 0 := by rintro rfl; simp at hd
            exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0,
              by have := Nat.le_of_dvd (by omega : 0 < n + 1) hd; omega⟩, hd⟩
        · rintro (rfl | ⟨hdI, hd⟩)
          · exact ⟨dvd_rfl, by omega⟩
          · exact ⟨hd, by omega⟩
      have hnot : n + 1 ∉ (Icc 1 n).filter (· ∣ n + 1) := by simp
      have hcorrection :
          (∑ d ∈ Icc 1 n, if d ∣ n + 1 then Λ d else 0) + Λ (n + 1) =
            Real.log (n + 1) := by
        rw [← sum_filter, add_comm, ← sum_insert hnot, ← hdivisors]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ArithmeticFunction.vonMangoldt_sum (n := n + 1))
      calc
        mangoldtFloorConvolution (n + 1) =
            (∑ d ∈ Icc 1 n,
              Λ d * ((n / d : ℕ) + if d ∣ n + 1 then 1 else 0)) + Λ (n + 1) := by
          rw [mangoldtFloorConvolution,
            sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
          simp only [Nat.succ_div, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
            Nat.cast_zero]
          congr 1
          simp [Nat.div_eq_of_lt (Nat.lt_succ_self n)]
        _ = mangoldtFloorConvolution n +
            ((∑ d ∈ Icc 1 n, if d ∣ n + 1 then Λ d else 0) + Λ (n + 1)) := by
          rw [mangoldtFloorConvolution]
          simp_rw [mul_add]
          rw [sum_add_distrib]
          simp only [mul_ite, mul_one, mul_zero]
          ring_nf
        _ = Real.log (n.factorial : ℝ) + Real.log (n + 1) := by rw [ih, hcorrection]
        _ = Real.log ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
          · norm_num [add_comm]
          · positivity
          · positivity

/-- A convenient elementary upper half of Stirling's estimate. -/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [Nat.factorial_succ]
  rw [Real.log_mul (by positivity) (by positivity), add_comm]
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < (↑‹ℕ› : ℝ) / (↑‹ℕ› + 1))
  rw [Real.log_div] at h <;>
    first | positivity |
      nlinarith [mul_div_cancel₀ ((↑‹ℕ› : ℝ) : ℝ)
        (by positivity : (↑‹ℕ› + 1 : ℝ) ≠ 0)]

/-- The continuous main term in Stirling's formula. -/
def stirlingMain (x : ℝ) : ℝ := x * Real.log x - x

/-- Error made when `log (⌊x⌋₊!)` is compared with its continuous main term. -/
def factorialRemainder (x : ℝ) : ℝ :=
  Real.log (⌊x⌋₊.factorial : ℝ) - stirlingMain x

lemma stirlingMain_floor_le {x : ℝ} (hx : 3 ≤ x) :
    stirlingMain ⌊x⌋₊ ≤ stirlingMain x := by
  have hx0 : 0 ≤ x := by linarith
  have hn3 : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 hx
  have hnle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hn0 : (0 : ℝ) ≤ ⌊x⌋₊ := by positivity
  have hlogmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
    exact hnle
  have hlogone : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans hx
  unfold stirlingMain
  calc
    (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊ ≤
        (⌊x⌋₊ : ℝ) * Real.log x - ⌊x⌋₊ := by gcongr
    _ ≤ x * Real.log x - x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnle) (sub_nonneg.mpr hlogone)]

lemma stirlingMain_sub_floor_le_log {x : ℝ} (hx : 3 ≤ x) :
    stirlingMain x - stirlingMain ⌊x⌋₊ ≤ Real.log x := by
  have hnpos : (0 : ℝ) < ⌊x⌋₊ := by
    exact_mod_cast (show 0 < ⌊x⌋₊ from by
      have : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 hx
      omega)
  have hxpos : 0 < x := by positivity
  have hnle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hgap : x - (⌊x⌋₊ : ℝ) ≤ 1 := (Nat.self_sub_floor_lt_one x).le
  have hratio := Real.log_le_sub_one_of_pos (div_pos hxpos hnpos)
  rw [Real.log_div hxpos.ne' hnpos.ne'] at hratio
  have hmul := mul_le_mul_of_nonneg_left hratio hnpos.le
  have hquot : (⌊x⌋₊ : ℝ) * (x / ⌊x⌋₊ - 1) = x - ⌊x⌋₊ := by
    field_simp
  rw [hquot] at hmul
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  unfold stirlingMain
  calc
    x * Real.log x - x -
        ((⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊) =
        (x - ⌊x⌋₊) * Real.log x +
          (⌊x⌋₊ : ℝ) * (Real.log x - Real.log ⌊x⌋₊) -
            (x - ⌊x⌋₊) := by ring
    _ ≤ (x - ⌊x⌋₊) * Real.log x := by linarith
    _ ≤ 1 * Real.log x := by gcongr
    _ = Real.log x := one_mul _

lemma factorialRemainder_abs_le {x : ℝ} (hx : 3 ≤ x) :
    |factorialRemainder x| ≤ Real.log x + 1 := by
  have hn : 1 ≤ ⌊x⌋₊ := by
    have : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 hx
    omega
  have hupper := log_factorial_le ⌊x⌋₊ hn
  have hlower := Stirling.le_log_factorial_stirling (n := ⌊x⌋₊) (by omega)
  have hlogfloor_nonneg : 0 ≤ Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have := Real.pi_gt_three
    nlinarith)
  have hnatlower : stirlingMain ⌊x⌋₊ ≤ Real.log (⌊x⌋₊.factorial : ℝ) := by
    unfold stirlingMain
    linarith
  have hremLower : -(Real.log x) ≤ factorialRemainder x := by
    unfold factorialRemainder
    linarith [stirlingMain_sub_floor_le_log hx]
  have hremUpper : factorialRemainder x ≤ Real.log x + 1 := by
    have hlogmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
      apply Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
      exact Nat.floor_le (by linarith)
    have hupper' : Real.log (⌊x⌋₊.factorial : ℝ) ≤
        stirlingMain ⌊x⌋₊ + 1 + Real.log ⌊x⌋₊ := by
      simpa [stirlingMain] using hupper
    unfold factorialRemainder
    linarith [stirlingMain_floor_le hx]
  rw [abs_le]
  constructor
  · have hlog0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
    linarith
  · exact hremUpper

/-- Chebyshev's five-term constant, written using only `log 2`, `log 3`,
and `log 5`.  It is approximately `0.92129`. -/
def alpha : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 +
    (1 / 6 : ℝ) * Real.log 5

lemma nine_tenths_le_alpha : (9 / 10 : ℝ) ≤ alpha := by
  unfold alpha
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
    Real.log_five_gt_d9]

lemma alpha_le_fourteen_fifteenths : alpha ≤ (14 / 15 : ℝ) := by
  unfold alpha
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9]

/-- The five-term logarithmic factorial combination. -/
def weightedFactorial (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ) -
    Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ) +
      Real.log ((n / 30).factorial : ℝ)

lemma mangoldtFloorConvolution_div (n k : ℕ) (hk : 0 < k) :
    Real.log ((n / k).factorial : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * ((n / k) / d : ℕ) := by
  rw [← mangoldtFloorConvolution_eq_log_factorial, mangoldtFloorConvolution]
  apply sum_subset
  · intro d hd
    simp only [mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.div_le_self n k)⟩
  · intro d hd hdnot
    simp only [mem_Icc] at hd hdnot
    have hlt : n / k < d := by
      by_contra h
      apply hdnot
      exact ⟨hd.1, by omega⟩
    rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]

lemma weightedFactorial_eq_sum_chi (n : ℕ) :
    weightedFactorial n =
      ∑ d ∈ Icc 1 n, Λ d * (chi (n / d) : ℤ) := by
  have h1 : Real.log (n.factorial : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ) := by
    simpa using mangoldtFloorConvolution_div n 1 (by norm_num)
  rw [weightedFactorial,
    h1,
    mangoldtFloorConvolution_div n 2 (by norm_num),
    mangoldtFloorConvolution_div n 3 (by norm_num),
    mangoldtFloorConvolution_div n 5 (by norm_num),
    mangoldtFloorConvolution_div n 30 (by norm_num)]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (mem_Icc.mp hd).1
  simp only [chi]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  simp only [Nat.div_div_eq_div_mul]
  rw [mul_comm 2 d, mul_comm 3 d, mul_comm 5 d, mul_comm 30 d]
  ring

lemma sum_vonMangoldt_Icc_eq_psi (n : ℕ) :
    (∑ d ∈ Icc 1 n, Λ d) = Chebyshev.psi n := by
  symm
  simp [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]

/-- The weighted factorial is bounded above by `psi`. -/
lemma weightedFactorial_le_psi (n : ℕ) :
    weightedFactorial n ≤ Chebyshev.psi n := by
  rw [weightedFactorial_eq_sum_chi, ← sum_vonMangoldt_Icc_eq_psi]
  apply sum_le_sum
  intro d hd
  have hchi : ((chi (n / d) : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast chi_le_one (n / d)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hchi (ArithmeticFunction.vonMangoldt_nonneg)

/-- The weighted factorial dominates the von Mangoldt mass in `(n/6,n]`. -/
lemma interval_mangoldt_le_weightedFactorial (n : ℕ) :
    (∑ d ∈ Ioc (n / 6) n, Λ d) ≤ weightedFactorial n := by
  rw [weightedFactorial_eq_sum_chi]
  calc
    (∑ d ∈ Ioc (n / 6) n, Λ d) ≤
        ∑ d ∈ Ioc (n / 6) n, Λ d * (chi (n / d) : ℤ) := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Ioc.mp hd
      have hdpos : 0 < d := by
        have : n / 6 < d := hd'.1
        omega
      have hone : 1 ≤ n / d := (Nat.one_le_div_iff hdpos).2 hd'.2
      have hsix : n / d < 6 := by
        rw [Nat.div_lt_iff_lt_mul hdpos]
        omega
      have hchi : (1 : ℝ) ≤ (chi (n / d) : ℤ) := by
        exact_mod_cast one_le_chi_of_lt_six hone hsix
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ d ∈ Icc 1 n, Λ d * (chi (n / d) : ℤ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [mem_Ioc] at hd
        exact mem_Icc.mpr ⟨by omega, hd.2⟩
      · intro d hd _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by
          exact_mod_cast chi_nonneg (n / d))

lemma stirlingMain_five_term {n : ℕ} (hn : 0 < n) :
    stirlingMain n - stirlingMain ((n : ℝ) / 2) -
        stirlingMain ((n : ℝ) / 3) - stirlingMain ((n : ℝ) / 5) +
          stirlingMain ((n : ℝ) / 30) = alpha * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog30 : Real.log (30 : ℝ) =
      Real.log 2 + Real.log 3 + Real.log 5 := by
    calc
      Real.log (30 : ℝ) = Real.log ((2 : ℝ) * (3 * 5)) := by norm_num
      _ = Real.log 2 + Real.log (3 * 5) := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 2 + (Real.log 3 + Real.log 5) := by
        rw [Real.log_mul] <;> norm_num
      _ = _ := by ring
  unfold stirlingMain alpha
  rw [Real.log_div hnR.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (30 : ℝ) ≠ 0), hlog30]
  ring

lemma weightedFactorial_eq_alpha_add_remainders {n : ℕ} (hn : 0 < n) :
    weightedFactorial n = alpha * n + factorialRemainder n -
        factorialRemainder ((n : ℝ) / 2) -
        factorialRemainder ((n : ℝ) / 3) -
        factorialRemainder ((n : ℝ) / 5) +
        factorialRemainder ((n : ℝ) / 30) := by
  have hmain := stirlingMain_five_term hn
  unfold weightedFactorial factorialRemainder
  simp only [Nat.floor_natCast, Nat.floor_div_ofNat]
  linarith

lemma log_div_le_log {x c : ℝ} (hx : 1 ≤ x) (hc : 1 ≤ c) :
    Real.log (x / c) ≤ Real.log x := by
  apply Real.log_le_log (by positivity)
  exact div_le_self (by positivity) hc

/-- Effective lower bound needed for the square-root interval in the
Granville--Ramaré argument. -/
lemma psi_lower_nat (n : ℕ) (hn : 90 ≤ n) :
    (9 / 10 : ℝ) * n - (5 * Real.log n + 5) ≤ Chebyshev.psi n := by
  have hnpos : 0 < n := by omega
  have hnR : (90 : ℝ) ≤ n := by exact_mod_cast hn
  have hargs :
      (3 : ℝ) ≤ n ∧ (3 : ℝ) ≤ n / 2 ∧ (3 : ℝ) ≤ n / 3 ∧
        (3 : ℝ) ≤ n / 5 ∧ (3 : ℝ) ≤ n / 30 := by
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  rcases hargs with ⟨hn3, hn2, hn3', hn5, hn30⟩
  have hrn := factorialRemainder_abs_le hn3
  have hr2 := factorialRemainder_abs_le hn2
  have hr3 := factorialRemainder_abs_le hn3'
  have hr5 := factorialRemainder_abs_le hn5
  have hr30 := factorialRemainder_abs_le hn30
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by nlinarith [hnR])
  have hl2 : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl3 : Real.log ((n : ℝ) / 3) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl5 : Real.log ((n : ℝ) / 5) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl30 : Real.log ((n : ℝ) / 30) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hw : alpha * n - (5 * Real.log n + 5) ≤ weightedFactorial n := by
    rw [weightedFactorial_eq_alpha_add_remainders hnpos]
    rw [abs_le] at hrn hr2 hr3 hr5 hr30
    linarith
  exact (by
    calc
      (9 / 10 : ℝ) * n - (5 * Real.log n + 5) ≤
          alpha * n - (5 * Real.log n + 5) := by
        gcongr
        exact nine_tenths_le_alpha
      _ ≤ weightedFactorial n := hw
      _ ≤ Chebyshev.psi n := weightedFactorial_le_psi n)

lemma weightedFactorial_upper (n : ℕ) (hn : 90 ≤ n) :
    weightedFactorial n ≤ alpha * n + (5 * Real.log n + 5) := by
  have hnpos : 0 < n := by omega
  have hnR : (90 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (3 : ℝ) ≤ n := by nlinarith
  have hn2 : (3 : ℝ) ≤ n / 2 := by nlinarith
  have hn3' : (3 : ℝ) ≤ n / 3 := by nlinarith
  have hn5 : (3 : ℝ) ≤ n / 5 := by nlinarith
  have hn30 : (3 : ℝ) ≤ n / 30 := by nlinarith
  have hrn := factorialRemainder_abs_le hn3
  have hr2 := factorialRemainder_abs_le hn2
  have hr3 := factorialRemainder_abs_le hn3'
  have hr5 := factorialRemainder_abs_le hn5
  have hr30 := factorialRemainder_abs_le hn30
  have hl2 : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl3 : Real.log ((n : ℝ) / 3) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl5 : Real.log ((n : ℝ) / 5) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl30 : Real.log ((n : ℝ) / 30) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  rw [weightedFactorial_eq_alpha_add_remainders hnpos]
  rw [abs_le] at hrn hr2 hr3 hr5 hr30
  linarith

lemma psi_eq_psi_div_six_add_interval (n : ℕ) :
    Chebyshev.psi n = Chebyshev.psi ((n / 6 : ℕ) : ℝ) +
      ∑ d ∈ Ioc (n / 6) n, Λ d := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  have hsets : Ioc 0 n = Ioc 0 (n / 6) ∪ Ioc (n / 6) n := by
    ext d
    simp only [mem_Ioc, mem_union]
    omega
  rw [hsets, sum_union]
  apply Finset.disjoint_left.mpr
  intro d hd1 hd2
  simp only [mem_Ioc] at hd1 hd2
  omega

lemma psi_rec (n : ℕ) (hn : 90 ≤ n) :
    Chebyshev.psi n ≤
      Chebyshev.psi ((n / 6 : ℕ) : ℝ) + alpha * n +
        (5 * Real.log n + 5) := by
  rw [psi_eq_psi_div_six_add_interval]
  have hi := (interval_mangoldt_le_weightedFactorial n).trans
    (weightedFactorial_upper n hn)
  linarith

/-- A global effective upper bound.  Its leading coefficient `28/25 = 1.12`
is small enough, together with `psi_lower_nat`, to leave a positive amount of
von Mangoldt mass in a square-root interval. -/
lemma psi_upper_nat (n : ℕ) :
    Chebyshev.psi n ≤
      (28 / 25 : ℝ) * n + 20 * Real.log n ^ 2 + 20000 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 1980
      · have hpsi := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
        have hlog4 : Real.log 4 ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
          norm_num at this ⊢
          exact this
        have hnR : (n : ℝ) ≤ 1980 := by exact_mod_cast hn.le
        have hlogsq : 0 ≤ Real.log (n : ℝ) ^ 2 := sq_nonneg _
        nlinarith
      · have hn1980 : 1980 ≤ n := by omega
        have hn90 : 90 ≤ n := by omega
        let m := n / 6
        have hm_lt : m < n := by
          dsimp [m]
          omega
        have hm330 : 330 ≤ m := by
          dsimp [m]
          omega
        have hih := ih m hm_lt
        have hrec := psi_rec n hn90
        have hnR : (1980 : ℝ) ≤ n := by exact_mod_cast hn1980
        have hmR : (330 : ℝ) ≤ m := by exact_mod_cast hm330
        have hm_le : (m : ℝ) ≤ (n : ℝ) / 6 := by
          dsimp [m]
          exact Nat.cast_div_le
        have hlogn1 : 1 ≤ Real.log (n : ℝ) := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          exact Real.exp_one_lt_three.le.trans (by nlinarith [hnR])
        have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
          Real.log_nonneg (by nlinarith [hmR])
        have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          exact Real.exp_one_lt_three.le
        have hm_le_third : (m : ℝ) ≤ (n : ℝ) / 3 := by nlinarith [hm_le]
        have hlogm_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - 1 := by
          have h := Real.log_le_log (by nlinarith [hmR]) hm_le_third
          rw [Real.log_div (by positivity : (n : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
          linarith
        have hsq : Real.log (m : ℝ) ^ 2 ≤
            (Real.log (n : ℝ) - 1) ^ 2 := by
          exact (sq_le_sq₀ hlogm0 (by linarith)).2 hlogm_le
        have herror :
            20 * Real.log (m : ℝ) ^ 2 + (5 * Real.log n + 5) ≤
              20 * Real.log n ^ 2 := by
          nlinarith
        have hlin :
            (28 / 25 : ℝ) * m + alpha * n ≤ (28 / 25 : ℝ) * n := by
          have ha := alpha_le_fourteen_fifteenths
          nlinarith
        calc
          Chebyshev.psi n ≤ Chebyshev.psi m + alpha * n +
              (5 * Real.log n + 5) := by simpa [m] using hrec
          _ ≤ ((28 / 25 : ℝ) * m + 20 * Real.log m ^ 2 + 20000) +
              alpha * n + (5 * Real.log n + 5) := by gcongr
          _ ≤ (28 / 25 : ℝ) * n + 20 * Real.log n ^ 2 + 20000 := by
            nlinarith

lemma psi_eq_psi_add_interval {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.psi b = Chebyshev.psi a + ∑ d ∈ Ioc a b, Λ d := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  have hsets : Ioc 0 b = Ioc 0 a ∪ Ioc a b := by
    ext d
    simp only [mem_Ioc, mem_union]
    omega
  rw [hsets, sum_union]
  apply Finset.disjoint_left.mpr
  intro d hd1 hd2
  simp only [mem_Ioc] at hd1 hd2
  omega

/-- The fully explicit form of the square-root interval estimate.  Unlike the
very sharp estimate of Dusart used in the printed proof, this only uses the
elementary five-term Chebyshev weight above.  The leading constant is still
large enough for the later Fourier argument; the logarithmic error is made
negligible by the (very large) cutoff in that argument. -/
lemma sqrtInterval_mangoldt_lower_with_error (n : ℕ) (hn : 4050 ≤ n) :
    (763 / 5000 : ℝ) * Real.sqrt n -
          (20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006) ≤
      ∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d := by
  let a := Nat.sqrt n
  let b := Nat.sqrt (2 * n)
  have hnpos : 0 < n := by omega
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Nat.sqrt_le_sqrt (by omega)
  have hb90 : 90 ≤ b := by
    dsimp [b]
    rw [Nat.le_sqrt]
    omega
  have hlower := psi_lower_nat b hb90
  have hupper := psi_upper_nat a
  have hpsi := psi_eq_psi_add_interval hab
  have ha_sqrt : (a : ℝ) ≤ Real.sqrt n := by
    dsimp [a]
    exact Real.nat_sqrt_le_real_sqrt
  have hb_sqrt : Real.sqrt (2 * (n : ℝ)) - 1 ≤ (b : ℝ) := by
    dsimp [b]
    have h := Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * n)
    norm_num [Nat.cast_mul] at h ⊢
    linarith
  have hsqrt2 : (707 / 500 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hsqrt_mul : Real.sqrt (2 * (n : ℝ)) =
      Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hsqrtn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have ha_le_n : a ≤ n := by
    dsimp [a]
    exact Nat.sqrt_le_self n
  have hb_le_two_n : b ≤ 2 * n := by
    dsimp [b]
    exact Nat.sqrt_le_self (2 * n)
  have hloga : Real.log (a : ℝ) ≤ Real.log n := by
    by_cases ha0 : a = 0
    · simp [ha0, Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hnpos)]
    · apply Real.log_le_log
      · exact_mod_cast (Nat.pos_of_ne_zero ha0)
      · exact_mod_cast ha_le_n
  have hlogb : Real.log (b : ℝ) ≤ Real.log (2 * n) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < b by omega)
    · exact_mod_cast hb_le_two_n
  have hloga0 : 0 ≤ Real.log (a : ℝ) := by
    have ha90 : 1 ≤ a := by
      dsimp [a]
      rw [Nat.le_sqrt]
      omega
    exact Real.log_nonneg (by exact_mod_cast ha90)
  have hlogsq : Real.log (a : ℝ) ^ 2 ≤ Real.log n ^ 2 := by
    exact (sq_le_sq₀ hloga0 (Real.log_nonneg (by exact_mod_cast hnpos))).2 hloga
  rw [hsqrt_mul] at hb_sqrt
  rw [hpsi] at hlower
  nlinarith

private lemma log_sq_le_quarter_power (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 64 * Real.sqrt (Real.sqrt x) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hlog := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 8 by norm_num)
  have hu : 0 ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx0 _
  have hu2 : (x ^ (1 / 8 : ℝ)) ^ 2 = Real.sqrt (Real.sqrt x) := by
    calc
      (x ^ (1 / 8 : ℝ)) ^ 2 = (x ^ (1 / 8 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 2).symm
      _ = x ^ ((1 / 8 : ℝ) * 2) := (Real.rpow_mul hx0 _ _).symm
      _ = x ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
        norm_num
      _ = (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_mul hx0 _ _
      _ = Real.sqrt (Real.sqrt x) := by simp [Real.sqrt_eq_rpow]
  have hlog' : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    convert hlog using 1 <;> ring
  have hsq := (sq_le_sq₀ (Real.log_nonneg hx) (by positivity : 0 ≤ 8 * x ^ (1 / 8 : ℝ))).2 hlog'
  nlinarith [hu2]

private lemma explicit_error_le_margin (n : ℕ) (hn : 2 ^ 1728 ≤ n) :
    20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006 ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hlargeCutoff : 10 ^ 24 ≤ 2 ^ 1728 := by
    calc
      10 ^ 24 ≤ 16 ^ 24 := Nat.pow_le_pow_left (by norm_num) 24
      _ = 2 ^ 96 := by norm_num [← pow_mul]
      _ ≤ 2 ^ 1728 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hnlargeNat : 10 ^ 24 ≤ n := hlargeCutoff.trans hn
  have hnlarge : (10 : ℝ) ^ 24 ≤ n := by exact_mod_cast hnlargeNat
  have hsqrt1 := Real.sqrt_le_sqrt hnlarge
  have hsqrt2 := Real.sqrt_le_sqrt hsqrt1
  have hbase : Real.sqrt (Real.sqrt ((10 : ℝ) ^ 24)) = 10 ^ 6 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
    rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
  rw [hbase] at hsqrt2
  have hq : (1000000 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    norm_num at hsqrt2 ⊢
    exact hsqrt2
  clear hn hlargeCutoff hnlargeNat hnlarge hsqrt1 hsqrt2 hbase
  have hq0 : 0 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_nonneg _
  have hq_sq : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt n :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlogsq := log_sq_le_quarter_power (n : ℝ) hnone
  have hlogn_linear : Real.log (n : ℝ) ≤ Real.log n ^ 2 + 1 := by
    nlinarith [sq_nonneg (Real.log (n : ℝ) - 1 / 2)]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogmul : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hnpos.ne')]
  have herr : 20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006 ≤
      1600 * Real.sqrt (Real.sqrt n) + 20016 := by
    rw [hlogmul]
    nlinarith
  have hqmul : 1000000 * Real.sqrt (Real.sqrt (n : ℝ)) ≤
      Real.sqrt (Real.sqrt n) ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  rw [hq_sq] at hqmul
  nlinarith

/-- A clean square-root interval lower bound at the cutoff used by the coarse
Granville--Ramaré assembly. -/
theorem sqrtInterval_mangoldt_lower (n : ℕ) (hn : 2 ^ 1728 ≤ n) :
    (3 / 20 : ℝ) * Real.sqrt n ≤
      ∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d := by
  have hsmallCutoff : 4050 ≤ 2 ^ 1728 := by
    calc
      4050 ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ 1728 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hn4050 : 4050 ≤ n := hsmallCutoff.trans hn
  have hmain := sqrtInterval_mangoldt_lower_with_error n hn4050
  have herr := explicit_error_le_margin n hn
  linarith

/-- The interval bound in the exact normalization needed after the
`6 / 43` Fourier-coefficient loss.  The `11 / 8 * log n` term is the
endpoint error in the trigonometric minorant. -/
theorem sqrtInterval_mangoldt_lower_after_fourier (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 50 : ℝ) * Real.sqrt n ≤
      (6 / 43 : ℝ) *
        ((∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
          (11 / 8 : ℝ) * Real.log n) := by
  have hsum := sqrtInterval_mangoldt_lower n hn
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hlog2n0 : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (2 * n) := by
    exact Real.log_le_log (by exact_mod_cast hnpos)
      (by exact_mod_cast (show n ≤ 2 * n by omega))
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsmallLog : 5 * Real.log (n : ℝ) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- A slightly stronger, sometimes more convenient, arrangement of the same
numerical loss, with the logarithmic term outside the factor `6 / 43`. -/
theorem sqrtInterval_mangoldt_lower_after_strong_loss (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 50 : ℝ) * Real.sqrt n ≤
      (6 / 43 : ℝ) *
          (∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
        (11 / 8 : ℝ) * Real.log n := by
  have hsum := sqrtInterval_mangoldt_lower n hn
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (2 * n) := by
    exact Real.log_le_log (by exact_mod_cast hnpos)
      (by exact_mod_cast (show n ≤ 2 * n by omega))
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsmallLog : 5 * Real.log (n : ℝ) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- The purely numerical arrangement used when the unconditional bad-prime
contribution is bounded by `log (2*n)`. -/
theorem sqrtInterval_numeric_after_log_two_mul_loss (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 50 : ℝ) * Real.sqrt n ≤
      (6 / 43 : ℝ) *
        ((3 / 20 : ℝ) * Real.sqrt n -
          (11 / 8 : ℝ) * Real.log (2 * n)) := by
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsmallLog : 5 * Real.log (2 * (n : ℝ)) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- Direct interval-sum version of
`sqrtInterval_numeric_after_log_two_mul_loss`. -/
theorem sqrtInterval_mangoldt_lower_after_log_two_mul_loss (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 50 : ℝ) * Real.sqrt n ≤
      (6 / 43 : ℝ) *
        ((∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
          (11 / 8 : ℝ) * Real.log (2 * n)) := by
  have hnum := sqrtInterval_numeric_after_log_two_mul_loss n hn
  have hsum := sqrtInterval_mangoldt_lower n hn
  nlinarith

/-- Numerical bridge for the degree-three Fourier minorant.  The strict
inequality is useful for extracting a nonzero term from the resulting finite
sum. -/
theorem sqrtInterval_numeric_degree_three (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt n <
      (1 / 180 : ℝ) *
        ((3 / 20 : ℝ) * Real.sqrt n - 40 * Real.log (2 * n)) := by
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hsmallLog : 5 * Real.log (2 * (n : ℝ)) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- Direct interval-sum form of `sqrtInterval_numeric_degree_three`. -/
theorem sqrtInterval_mangoldt_degree_three (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt n <
      (1 / 180 : ℝ) *
        ((∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
          40 * Real.log (2 * n)) := by
  have hnum := sqrtInterval_numeric_degree_three n hn
  have hsum := sqrtInterval_mangoldt_lower n hn
  nlinarith

/-- Numerical bridge for the final degree-three constants
`c = 33 / 200`, `A = 3 / 4`.  In the normalization used by Section 7 these
constants give the loss `S ≤ 450 M + 100 log (2n)`. -/
theorem sqrtInterval_numeric_degree_three_450 (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 5000 : ℝ) * Real.sqrt n <
      (1 / 450 : ℝ) *
        ((3 / 20 : ℝ) * Real.sqrt n - 100 * Real.log (2 * n)) := by
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hsmallLog : 5 * Real.log (2 * (n : ℝ)) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- Direct Mangoldt interval-sum version of
`sqrtInterval_numeric_degree_three_450`. -/
theorem sqrtInterval_mangoldt_degree_three_450 (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 5000 : ℝ) * Real.sqrt n <
      (1 / 450 : ℝ) *
        ((∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
          100 * Real.log (2 * n)) := by
  have hnum := sqrtInterval_numeric_degree_three_450 n hn
  have hsum := sqrtInterval_mangoldt_lower n hn
  nlinarith


end

end Erdos175.ExplicitChebyshev

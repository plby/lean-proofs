import ErdosProblems.Erdos421.DirichletGram
import Mathlib.NumberTheory.LSeries.Convolution

/-! # Finite support, convolution, and powers of Dirichlet polynomials -/

namespace Erdos421

def SupportedThrough {R : Type*} [Zero R] (f : ArithmeticFunction R) (A : ℕ) : Prop :=
  ∀ n, A < n → f n = 0

theorem SupportedThrough.mul {R : Type*} [Semiring R] {f g : ArithmeticFunction R}
    {A B : ℕ} (hf : SupportedThrough f A) (hg : SupportedThrough g B) :
    SupportedThrough (f * g) (A * B) := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
  change a * b = n at hprod
  by_cases ha : A < a
  · rw [hf a ha, zero_mul]
  · have hb : B < b := by
      by_contra hnot
      have hbound := Nat.mul_le_mul (le_of_not_gt ha) (le_of_not_gt hnot)
      omega
    rw [hg b hb, mul_zero]

theorem supportedThrough_one {R : Type*} [Semiring R] :
    SupportedThrough (1 : ArithmeticFunction R) 1 := by
  intro n hn
  exact ArithmeticFunction.one_apply_ne (by omega)

theorem SupportedThrough.pow {R : Type*} [Semiring R] {f : ArithmeticFunction R}
    {A : ℕ} (hf : SupportedThrough f A) (k : ℕ) : SupportedThrough (f ^ k) (A ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (supportedThrough_one (R := R))
  | succ k ih =>
    simpa only [pow_succ] using ih.mul hf

theorem SupportedThrough.LSeriesHasSum {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (s : ℂ) :
    LSeriesHasSum f s (∑ n ∈ Finset.Icc 1 A, LSeries.term f s n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  by_cases hn0 : n = 0
  · simp only [hn0, LSeries.term_zero]
  · have hAn : A < n := by
      have hnot : ¬ (1 ≤ n ∧ n ≤ A) := by simpa only [Finset.mem_Icc] using hn
      omega
    rw [LSeries.term_of_ne_zero hn0, hf n hAn, zero_div]

theorem SupportedThrough.LSeriesSummable {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (s : ℂ) : LSeriesSummable f s :=
  (hf.LSeriesHasSum s).LSeriesSummable

theorem SupportedThrough.LSeries_eq_sum {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (s : ℂ) :
    LSeries f s = ∑ n ∈ Finset.Icc 1 A, f n / (n : ℂ) ^ s := by
  rw [(hf.LSeriesHasSum s).LSeries_eq]
  apply Finset.sum_congr rfl
  intro n hn
  exact LSeries.term_of_ne_zero (by have := (Finset.mem_Icc.mp hn).1; omega) f s

theorem finite_LSeries_one (s : ℂ) : LSeries (1 : ArithmeticFunction ℂ) s = 1 := by
  rw [supportedThrough_one.LSeries_eq_sum]
  simp

theorem SupportedThrough.LSeries_pow {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (k : ℕ) (s : ℂ) :
    LSeries (f ^ k : ArithmeticFunction ℂ) s = (LSeries f s) ^ k := by
  induction k with
  | zero => simp only [pow_zero, finite_LSeries_one]
  | succ k ih =>
    calc
      _ = LSeries (f ^ k * f : ArithmeticFunction ℂ) s := by rw [pow_succ]
      _ = LSeries (f ^ k : ArithmeticFunction ℂ) s * LSeries f s :=
        ArithmeticFunction.LSeries_mul' ((hf.pow k).LSeriesSummable s) (hf.LSeriesSummable s)
      _ = _ := by rw [ih, pow_succ]

theorem nat_cpow_imaginary {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (Complex.I * (t : ℂ)) = oscillatoryPhase (Real.log n) t := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  unfold oscillatoryPhase
  congr 1
  ring

theorem SupportedThrough.LSeries_eq_exponentialSum {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (t : ℝ) :
    LSeries f (-(Complex.I * (t : ℂ))) =
      exponentialSum (Finset.Icc 1 A) f (fun n ↦ Real.log n) t := by
  rw [hf.LSeries_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [Complex.cpow_neg, div_inv_eq_mul, nat_cpow_imaginary hn0]

/-- The actual finite exponential sum of convolution powers is the power of
the original finite exponential sum. -/
theorem SupportedThrough.exponentialSum_pow {f : ArithmeticFunction ℂ} {A : ℕ}
    (hf : SupportedThrough f A) (k : ℕ) (t : ℝ) :
    exponentialSum (Finset.Icc 1 (A ^ k)) (f ^ k : ArithmeticFunction ℂ) (fun n ↦ Real.log n) t =
      (exponentialSum (Finset.Icc 1 A) f (fun n ↦ Real.log n) t) ^ k := by
  rw [← (hf.pow k).LSeries_eq_exponentialSum, ← hf.LSeries_eq_exponentialSum]
  exact hf.LSeries_pow k _

end Erdos421

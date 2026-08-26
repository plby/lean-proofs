import ErdosProblems.Erdos421.FiniteDirichlet

/-! # Truncating arithmetic functions and summing their coefficients -/

namespace Erdos421

theorem sum_Ico_eq_sum_Icc_of_support {R : Type*} [AddCommMonoid R]
    (g : ℕ → R) {N B : ℕ} (hg : ∀ n, N < n → g n = 0) (hNB : N < B) :
    (∑ n ∈ Finset.Ico 1 B, g n) = ∑ n ∈ Finset.Icc 1 N, g n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn₁, hnN⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨hn₁, lt_of_le_of_lt hnN hNB⟩
  · intro n hn hnot
    have hn₁ := (Finset.mem_Ico.mp hn).1
    have hNn : N < n := by
      simp only [Finset.mem_Icc, hn₁, true_and] at hnot
      omega
    exact hg n hNn

def arithmeticTruncate {R : Type*} [Zero R] (f : ArithmeticFunction R) (A : ℕ) :
    ArithmeticFunction R :=
  ⟨fun n ↦ if n ≤ A then f n else 0, by simp⟩

theorem arithmeticTruncate_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (A n : ℕ) :
    arithmeticTruncate f A n = if n ≤ A then f n else 0 := rfl

theorem arithmeticTruncate_supported {R : Type*} [Zero R] (f : ArithmeticFunction R) (A : ℕ) :
    SupportedThrough (arithmeticTruncate f A) A := by
  intro n hn
  simp only [arithmeticTruncate_apply, if_neg (not_le_of_gt hn)]

theorem convolution_pow_eq_of_agree {R : Type*} [Semiring R]
    {f g : ArithmeticFunction R} {A : ℕ} (hfg : ∀ n ≤ A, f n = g n)
    (k : ℕ) {n : ℕ} (hn : n ≤ A) :
    (f ^ k : ArithmeticFunction R) n = (g ^ k : ArithmeticFunction R) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro p hp
    have hp₁ := Nat.fst_mem_divisors_of_mem_antidiagonal hp
    have hp₂ := Nat.snd_mem_divisors_of_mem_antidiagonal hp
    have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hp).2
    rw [ih (le_trans (Nat.le_of_dvd hnpos (Nat.mem_divisors.mp hp₁).1) hn),
      hfg p.2 (le_trans (Nat.le_of_dvd hnpos (Nat.mem_divisors.mp hp₂).1) hn)]

theorem arithmeticTruncate_pow_apply {R : Type*} [Semiring R] (f : ArithmeticFunction R)
    (A k : ℕ) {n : ℕ} (hn : n ≤ A) :
    (arithmeticTruncate f A ^ k : ArithmeticFunction R) n = (f ^ k : ArithmeticFunction R) n := by
  apply convolution_pow_eq_of_agree (k := k) (n := n) _ hn
  intro m hm
  simp only [arithmeticTruncate_apply, if_pos hm]

theorem natCast_convolution_pow {R : Type*} [Semiring R] (f : ArithmeticFunction ℕ) (k : ℕ) :
    ((f ^ k : ArithmeticFunction ℕ) : ArithmeticFunction R) = (f : ArithmeticFunction R) ^ k := by
  induction k with
  | zero => simp only [pow_zero, ArithmeticFunction.natCoe_one]
  | succ k ih => simp only [pow_succ, ArithmeticFunction.natCoe_mul, ih]

theorem SupportedThrough.natCast {R : Type*} [AddMonoidWithOne R]
    {f : ArithmeticFunction ℕ} {A : ℕ} (hf : SupportedThrough f A) :
    SupportedThrough (f : ArithmeticFunction R) A := by
  intro n hn
  simp only [ArithmeticFunction.natCoe_apply, hf n hn, Nat.cast_zero]

theorem SupportedThrough.weighted_sum_pow {f : ArithmeticFunction ℕ} {A : ℕ}
    (hf : SupportedThrough f A) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 (A ^ k), ((f ^ k : ArithmeticFunction ℕ) n : ℝ) / n) =
      (∑ n ∈ Finset.Icc 1 A, (f n : ℝ) / n) ^ k := by
  have h := (hf.natCast (R := ℂ)).LSeries_pow k 1
  rw [((hf.natCast (R := ℂ)).pow k).LSeries_eq_sum,
    (hf.natCast (R := ℂ)).LSeries_eq_sum] at h
  simp only [Complex.cpow_one, ← natCast_convolution_pow, ArithmeticFunction.natCoe_apply] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

end Erdos421

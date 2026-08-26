import ErdosProblems.Erdos67b.MRPrimeLogWide
import ErdosProblems.Erdos67b.MRSmoothPrimeAbel
import ErdosProblems.Erdos67b.MRSmoothPrimeProgressions

/-! # Actual smooth progression sums at nonzero polynomial heights -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

theorem mrExists_smoothPrime_progression_oscillation (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {P : ℝ}, 0 < P →
      ∀ {q : ℕ}, 0 < q → 2 * (q : ℝ) ≤ P →
        A₀ ≤ ⌈(P / 2) / (q : ℝ)⌉₊ →
      ∀ {t : ℝ}, t ≠ 0 → positiveLogCoefficient t <
        ((⌈(P / 2) / (q : ℝ)⌉₊ : ℕ) : ℝ) ^ (R + 1) →
      ‖∑ n ∈ Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊ with q ∣ n,
        mrSmoothPrimeKernelIntegrand P t n‖ ≤
        1400 * (3 * ((⌈(P / 2) / (q : ℝ)⌉₊ : ℕ) : ℝ) / positiveLogCoefficient t +
          (mrPrimeWeylConstant R + 20) *
            ((⌈(P / 2) / (q : ℝ)⌉₊ : ℕ) : ℝ) ^ (1 - savingExponent R)) := by
  obtain ⟨A₀, hA₀one, hA₀⟩ := mrExists_primeMellin_wide_bound R hR
  refine ⟨A₀, hA₀one, ?_⟩
  intro P hP q hq hqP hA t ht hu
  let a : ℝ := (P / 2) / (q : ℝ)
  let b : ℝ := (3 * P) / (q : ℝ)
  let A : ℕ := ⌈a⌉₊
  let B : ℕ := ⌊b⌋₊
  let E : ℝ := 3 * (A : ℝ) / positiveLogCoefficient t +
    (mrPrimeWeylConstant R + 20) * (A : ℝ) ^ (1 - savingExponent R)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha : 1 ≤ a := (le_div_iff₀ hqR).2 (by linarith)
  have hb : b = 6 * a := by dsimp [a, b]; ring
  have hbpos : 0 ≤ b := by rw [hb]; linarith
  have hAlower : a ≤ A := Nat.le_ceil a
  have hAupper : (A : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hBlower : (B : ℝ) ≤ b := Nat.floor_le hbpos
  have hAB : A ≤ B := by
    apply Nat.le_floor
    rw [hb]
    linarith
  have hAone : 1 ≤ A := by exact_mod_cast ha.trans hAlower
  have hBwide : B ≤ 8 * A := by
    have hh : (B : ℝ) ≤ 8 * (A : ℝ) := by rw [hb] at hBlower; linarith
    exact_mod_cast hh
  have hlo : P / 2 ≤ (q : ℝ) * A := by
    have hh := (div_le_iff₀ hqR).1 hAlower
    simpa only [mul_comm] using hh
  have hhi : (q : ℝ) * B ≤ 3 * P := by
    have hh := (le_div_iff₀ hqR).1 hBlower
    simpa only [mul_comm] using hh
  have hE : 0 ≤ E := by
    have := positiveLogCoefficient_pos ht
    have := mrPrimeWeylConstant_pos R
    dsimp [E]
    positivity
  have hprefix (m : ℕ) (hm : m ∈ Finset.Icc A B) :
      ‖∑ n ∈ Finset.Icc A m, mrPrimeMellinMonomial 0 t n‖ ≤ 7 * E :=
    hA₀ hA ((Finset.mem_Icc.1 hm).2.trans hBwide) ht hu
  have hweighted := mrNorm_smoothPrime_weighted_sum_le hP hqR hAB hlo hhi
    (fun n ↦ mrPrimeMellinMonomial 0 t n) (mul_nonneg (by norm_num) hE) hprefix
  have hsum : (∑ n ∈ Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊ with q ∣ n,
      mrSmoothPrimeKernelIntegrand P t n) =
      mrPrimeMellinMonomial 0 t q *
        ∑ m ∈ Finset.Icc A B, mrPrimeMellinMonomial 0 t m *
          (mrPrimeWeightPolynomial ((q : ℝ) * m / P) : ℂ) := by
    rw [mrSum_multiples_rounded_interval (fun n ↦ mrSmoothPrimeKernelIntegrand P t n)
      (by positivity : (0 : ℝ) ≤ P / 2) (by linarith : P / 2 ≤ 3 * P) hq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : (0 : ℝ) < m := by
      have hmA : A ≤ m := (Finset.mem_Icc.1 hm).1
      exact_mod_cast (show 0 < m by omega)
    rw [mrSmoothPrimeKernelIntegrand, Nat.cast_mul,
      mrPrimeMellinMonomial_mul 0 t hqR hmpos]
    ring
  rw [hsum, norm_mul, norm_mrPrimeMellinMonomial 0 t hqR, pow_zero, one_mul]
  change _ ≤ 1400 * E
  exact hweighted.trans (by ring_nf; exact le_rfl)

end

end Erdos67b

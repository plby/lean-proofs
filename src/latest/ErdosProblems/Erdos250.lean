/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 250: irrationality of the sum-of-divisors Lambert series.

The mathematical proof and the implementation plan are documented in
`tex/250.tex` at the repository root.
-/

import ErdosProblems.Erdos250.Erdos250Assemble

open Filter
open scoped ArithmeticFunction.sigma BigOperators Topology

namespace Erdos250

/-- The `q = 1/2` value of the Lambert series usually denoted `ζ_q(2)`. -/
noncomputable def zetaQ2 : ℝ :=
  ∑' n : ℕ+, (n : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) /
    (1 - ((1 : ℝ) / 2) ^ (n : ℕ))

/-- The series in the problem is the Lambert-series value `zetaQ2`. -/
lemma hasSum_eq_zetaQ2 (x : ℝ)
    (h : HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x) :
    x = zetaQ2 := by
  calc
    x = ∑' n : ℕ, (σ 1 n : ℝ) / (2 : ℝ) ^ n := h.tsum_eq.symm
    _ = ∑' n : ℕ+, (σ 1 (n : ℕ) : ℝ) / (2 : ℝ) ^ (n : ℕ) := by
      simpa using (tsum_zero_pnat_eq_tsum_nat h.summable).symm
    _ = ∑' n : ℕ+, (σ 1 (n : ℕ) : ℝ) *
          ((1 : ℝ) / 2) ^ (n : ℕ) := by
      congr 1
      ext n
      rw [one_div_pow]
      ring
    _ = zetaQ2 := by
      rw [zetaQ2]
      symm
      simpa using
        (tsum_pow_div_one_sub_eq_tsum_sigma
          (r := (1 : ℝ) / 2) (by norm_num) 1)

/-- An integer-valued sequence converging to zero is eventually zero. -/
lemma int_tendsto_zero_eventually_zero (f : ℕ → ℤ)
    (htend : Tendsto (fun n => (f n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, f n = 0 := by
  norm_num [Metric.tendsto_nhds] at htend
  exact eventually_atTop.mpr (by
    rcases htend 1 zero_lt_one with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      norm_cast at hN
      simpa [sub_eq_iff_eq_add] using hN n hn⟩)

/-- Nonzero integer linear forms tending to zero certify irrationality. -/
lemma irrational_of_integer_linear_forms (x : ℝ) (a b : ℕ → ℤ)
    (hne : ∀ n, (b n : ℝ) * x - a n ≠ 0)
    (htend : Tendsto (fun n => (b n : ℝ) * x - a n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  let F : ℕ → ℤ := fun n => b n * r.num - a n * r.den
  have hcast : ∀ n, (F n : ℝ) = (r.den : ℝ) *
      ((b n : ℝ) * (r : ℝ) - a n) := by
    intro n
    change (((b n * r.num - a n * (r.den : ℤ) : ℤ) : ℤ) : ℝ) = _
    push_cast
    rw [Rat.cast_def]
    field_simp [Rat.den_ne_zero]
  have hFtend : Tendsto (fun n => (F n : ℝ)) atTop (𝓝 0) := by
    simpa only [hcast, mul_zero] using htend.const_mul (r.den : ℝ)
  rcases eventually_atTop.mp (int_tendsto_zero_eventually_zero F hFtend) with ⟨N, hN⟩
  apply hne N
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hmul : (r.den : ℝ) * ((b N : ℝ) * (r : ℝ) - a N) = 0 := by
    simpa [hN N le_rfl] using (hcast N).symm
  exact (mul_eq_zero.mp hmul).resolve_left hden

/-- Erdős Problem 250: the sum of the divisors series at `1 / 2` is
irrational.  The term at `n = 0` vanishes, so this is the stated sum over
positive integers. -/
theorem erdos_250 :
    ∀ x : ℝ, HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x → Irrational x := by
  intro x hx
  rw [hasSum_eq_zetaQ2 x hx]
  have hzeta : zetaQ2 = ShiftedSums.zetaQ2 := by
    simp only [zetaQ2, ShiftedSums.zetaQ2, ShiftedSums.q]
  rw [hzeta]
  exact irrational_zetaQ2

end Erdos250

#print axioms Erdos250.erdos_250

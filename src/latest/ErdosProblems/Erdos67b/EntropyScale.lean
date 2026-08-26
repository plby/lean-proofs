import ErdosProblems.Erdos67b.ConditionalEntropy
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Finite scale selection for the entropy decrement

The finite telescoping argument is kept separate from the logarithmic
probability law. No analytic input is assumed as an axiom.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.FiniteEntropy

/-- Telescoping a finite family of entropy-rate inequalities. -/
theorem finite_entropy_decrement_sum
    (R D E : ℕ → ℝ) (J : ℕ)
    (hstep : ∀ j < J, R (j + 1) ≤ R j - D j + E j) :
    R J ≤ R 0 - (∑ j ∈ range J, D j) + ∑ j ∈ range J, E j := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprev := ih (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj))
    have hlast := hstep J (Nat.lt_succ_self J)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- If candidate decrements exceed all available initial entropy and
errors, at least one actual information decrement is no larger than its
candidate. This is a finite statement with an explicit terminal scale. -/
theorem exists_small_information_of_decrement
    (R D E b : ℕ → ℝ) (J : ℕ) (hR : 0 ≤ R J)
    (hstep : ∀ j < J, R (j + 1) ≤ R j - D j + E j)
    (hbudget : R 0 + (∑ j ∈ range J, E j) < ∑ j ∈ range J, b j) :
    ∃ j < J, D j ≤ b j := by
  by_contra h
  push Not at h
  have hsum : (∑ j ∈ range J, b j) ≤ ∑ j ∈ range J, D j :=
    Finset.sum_le_sum fun j hj ↦ (h j (Finset.mem_range.mp hj)).le
  have htel := finite_entropy_decrement_sum R D E J hstep
  linarith

/-- The reciprocal `n log n` series diverges. The exceptional values at
zero and one are zero under Lean's total inverse convention. -/
theorem not_summable_inv_nat_mul_log :
    ¬ Summable (fun n : ℕ ↦ 1 / ((n : ℝ) * Real.log n)) := by
  let f : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) * Real.log n)
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    rcases n with _ | n
    · simp [f]
    · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))))
  have hmono : ∀ᶠ n in Filter.atTop, f (n + 1) ≤ f n := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
    have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    exact one_div_le_one_div_of_le (mul_pos hnpos hnlog)
      (mul_le_mul hcast (Real.log_le_log hnpos hcast) hnlog.le (by positivity))
  intro hs
  have hc := (summable_condensed_iff_of_eventually_nonneg
    (Filter.Eventually.of_forall hnonneg) hmono).mpr hs
  have heq : (fun k : ℕ ↦ Real.log 2 * ((2 : ℝ) ^ k * f (2 ^ k))) =
      (fun k : ℕ ↦ 1 / (k : ℝ)) := by
    funext k
    simp only [f, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    by_cases hk : k = 0
    · simp [hk]
    · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      field_simp
  have hh := hc.mul_left (Real.log 2)
  rw [heq] at hh
  exact Real.not_summable_one_div_natCast hh

/-- The factorial scale schedule has summable reciprocal enlargement
factors while its reciprocal logarithms have divergent sum. -/
def entropyScale (H₀ j : ℕ) : ℕ := H₀ * (Nat.factorial (j + 1)) ^ 2

@[simp]
theorem entropyScale_zero (H₀ : ℕ) : entropyScale H₀ 0 = H₀ := by
  simp [entropyScale]

theorem entropyScale_succ (H₀ j : ℕ) :
    entropyScale H₀ (j + 1) = (j + 2) ^ 2 * entropyScale H₀ j := by
  simp only [entropyScale, Nat.factorial_succ, mul_pow]
  ring

theorem le_entropyScale (H₀ j : ℕ) : H₀ ≤ entropyScale H₀ j := by
  have h : 1 ≤ (Nat.factorial (j + 1)) ^ 2 :=
    Nat.one_le_pow _ _ (Nat.factorial_pos _)
  exact Nat.le_mul_of_pos_right H₀ (lt_of_lt_of_le Nat.zero_lt_one h)

theorem dvd_entropyScale (H₀ j : ℕ) : H₀ ∣ entropyScale H₀ j :=
  dvd_mul_right _ _

theorem log_entropyScale_pos {H₀ : ℕ} (hH₀ : 2 ≤ H₀) (j : ℕ) :
    0 < Real.log (entropyScale H₀ j) := by
  apply Real.log_pos
  exact_mod_cast lt_of_lt_of_le (by omega : 1 < H₀) (le_entropyScale H₀ j)

/-- A uniform upper bound for logarithms of the factorial schedule. -/
theorem exists_log_entropyScale_le {H₀ : ℕ} (hH₀ : 2 ≤ H₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ j,
      Real.log (entropyScale H₀ j) ≤ B * ((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hHpos : 0 < (H₀ : ℝ) := by exact_mod_cast (show 0 < H₀ by omega)
  have hHlog : 0 ≤ Real.log (H₀ : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ H₀ by omega))
  refine ⟨Real.log H₀ / Real.log 2 + 2, by positivity, ?_⟩
  intro j
  have hn : (2 : ℝ) ≤ (j + 2 : ℕ) := by exact_mod_cast (show 2 ≤ j + 2 by omega)
  have hnpos : 0 < ((j + 2 : ℕ) : ℝ) := by linarith
  have hnlog : 0 ≤ Real.log (j + 2 : ℕ) := Real.log_nonneg (by linarith)
  have hden : Real.log 2 ≤ ((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ) := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn
    nlinarith
  have hbase : Real.log (H₀ : ℝ) ≤
      (Real.log H₀ / Real.log 2) * (((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ)) := by
    have h := mul_le_mul_of_nonneg_left hden (div_nonneg hHlog htwo.le)
    rwa [div_mul_cancel₀ _ htwo.ne'] at h
  have hfac : (Nat.factorial (j + 1) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) ^ (j + 2) := by
    exact_mod_cast (Nat.factorial_le (show j + 1 ≤ j + 2 by omega)).trans
      (Nat.factorial_le_pow (j + 2))
  have hfacpos : 0 < (Nat.factorial (j + 1) : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfaclog := Real.log_le_log hfacpos hfac
  rw [Real.log_pow] at hfaclog
  have hscale : Real.log (entropyScale H₀ j) =
      Real.log H₀ + 2 * Real.log (Nat.factorial (j + 1)) := by
    simp only [entropyScale, Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul hHpos.ne' (pow_ne_zero _ hfacpos.ne'), Real.log_pow]
    norm_num
  rw [hscale]
  nlinarith

/-- Reciprocal logarithms of the chosen finite scales are not summable. -/
theorem not_summable_inv_log_entropyScale {H₀ : ℕ} (hH₀ : 2 ≤ H₀) :
    ¬ Summable (fun j ↦ 1 / Real.log (entropyScale H₀ j)) := by
  obtain ⟨B, hB, hbound⟩ := exists_log_entropyScale_le hH₀
  intro hs
  have hsmall : Summable (fun j : ℕ ↦
      1 / (((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ))) := by
    apply (hs.mul_left B).of_nonneg_of_le
    · intro j
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ j + 2 by omega))))
    · intro j
      have h := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (log_entropyScale_pos hH₀ j) (hbound j)) hB.le
      have heq : B * (1 / (B * ((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ))) =
          1 / (((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ)) := by
        field_simp
      rwa [heq] at h
  exact not_summable_inv_nat_mul_log ((summable_nat_add_iff 2).mp hsmall)

/-- The total reciprocal-square cost of the enlargements is at most one. -/
theorem sum_inverse_square_enlargement_le (J : ℕ) :
    (∑ j ∈ range J, 1 / (((j + 2 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  have hstrong : ∀ J : ℕ,
      (∑ j ∈ range J, 1 / (((j + 2 : ℕ) : ℝ) ^ 2)) ≤
        1 - 1 / ((J + 1 : ℕ) : ℝ) := by
    intro J
    induction J with
    | zero => norm_num
    | succ J ih =>
      have hJ1 : (0 : ℝ) < (J + 1 : ℕ) := by positivity
      have hJ2 : (0 : ℝ) < (J + 2 : ℕ) := by positivity
      have hterm : 1 / (((J + 2 : ℕ) : ℝ) ^ 2) ≤
          1 / ((J + 1 : ℕ) : ℝ) - 1 / ((J + 2 : ℕ) : ℝ) := by
        field_simp
        norm_num
      rw [Finset.sum_range_succ]
      exact le_trans (add_le_add ih hterm) (by ring_nf; rfl)
  exact (hstrong J).trans (sub_le_self _ (by positivity))

/-- A finite scale range can absorb any fixed entropy budget. -/
theorem exists_sum_inv_log_entropyScale_gt {H₀ : ℕ} (hH₀ : 2 ≤ H₀) (A : ℝ) :
    ∃ J : ℕ, A < ∑ j ∈ range J, 1 / Real.log (entropyScale H₀ j) := by
  by_contra h
  push Not at h
  exact not_summable_inv_log_entropyScale hH₀
    (summable_of_sum_range_le (fun j ↦ (one_div_pos.mpr (log_entropyScale_pos hH₀ j)).le) h)

/-- Quantified finite entropy decrement. The scale range is chosen before
the law and its common error `e`; the latter need only obey `J * e ≤ 1`.
No rate of convergence of that error is required. -/
theorem exists_finite_entropy_scale
    {H₀ : ℕ} (hH₀ : 2 ≤ H₀) {τ : ℝ} (hτ : 0 < τ)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ J : ℕ, 0 < J ∧ ∀ (R I : ℕ → ℝ) (e : ℝ),
      0 ≤ R J → R 0 ≤ K → (J : ℝ) * e ≤ 1 →
      (∀ j < J, R (j + 1) ≤ R j - I j / entropyScale H₀ j +
        C / (((j + 2 : ℕ) : ℝ) ^ 2) + e) →
      ∃ j < J, I j ≤ τ * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  obtain ⟨J, hJ⟩ := exists_sum_inv_log_entropyScale_gt hH₀ ((K + C + 1) / τ)
  have hbudget : K + C + 1 < τ *
      (∑ j ∈ range J, 1 / Real.log (entropyScale H₀ j)) := by
    have h := (div_lt_iff₀ hτ).mp hJ
    simpa only [mul_comm] using h
  have hJpos : 0 < J := by
    by_contra h
    have hzero : J = 0 := by omega
    simp only [hzero, Finset.range_zero, Finset.sum_empty, mul_zero] at hbudget
    linarith
  refine ⟨J, hJpos, ?_⟩
  intro R I e hR hR0 he hstep
  let E : ℕ → ℝ := fun j ↦ C / (((j + 2 : ℕ) : ℝ) ^ 2) + e
  let b : ℕ → ℝ := fun j ↦ τ / Real.log (entropyScale H₀ j)
  have herror : (∑ j ∈ range J, E j) ≤ C + 1 := by
    have hsum := mul_le_mul_of_nonneg_left (sum_inverse_square_enlargement_le J) hC
    have hrewrite : (∑ j ∈ range J, E j) =
        C * (∑ j ∈ range J, 1 / (((j + 2 : ℕ) : ℝ) ^ 2)) + J * e := by
      simp only [E, div_eq_mul_inv, one_mul, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    rw [hrewrite]
    linarith
  have hcandidate : (∑ j ∈ range J, b j) =
      τ * (∑ j ∈ range J, 1 / Real.log (entropyScale H₀ j)) := by
    simp only [b, div_eq_mul_inv, one_mul, Finset.mul_sum]
  obtain ⟨j, hj, hi⟩ := exists_small_information_of_decrement R
    (fun j ↦ I j / entropyScale H₀ j) E b J hR
    (fun j hj ↦ by simpa only [E, add_assoc] using hstep j hj)
    (by rw [hcandidate]; linarith)
  refine ⟨j, hj, ?_⟩
  have hscale : (0 : ℝ) < entropyScale H₀ j := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < H₀) (le_entropyScale H₀ j)
  have h := (div_le_iff₀ hscale).mp hi
  change I j ≤ τ / Real.log (entropyScale H₀ j) * entropyScale H₀ j at h
  simpa only [div_mul_eq_mul_div] using h

end Erdos67b.FiniteEntropy

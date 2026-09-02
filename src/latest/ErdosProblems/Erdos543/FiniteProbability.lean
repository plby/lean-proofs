import Mathlib

/-!
# Elementary probability on a finite uniform sample space

This file supplies the finite probability estimates used in the formalization
of Erdős Problem 543.  Everything is defined directly as a finite sum divided
by the (real) cardinality of the sample space, so no measure-theoretic
probability infrastructure is required.
-/

open scoped BigOperators

namespace Erdos543.FiniteProbability

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- Uniform probability of an event on a finite sample space. -/
noncomputable def prob (E : Set Ω) : ℝ :=
  by
    classical
    exact ((Finset.univ.filter fun ω => ω ∈ E).card : ℝ) / Fintype.card Ω

/-- Uniform expectation of a real-valued random variable. -/
noncomputable def expect (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- The real indicator of an event. -/
noncomputable def indicator (E : Set Ω) (ω : Ω) : ℝ :=
  by
    classical
    exact if ω ∈ E then 1 else 0

/-- Variance with respect to the finite uniform distribution. -/
noncomputable def variance (X : Ω → ℝ) : ℝ :=
  expect fun ω => (X ω - expect X) ^ 2

theorem card_pos [Nonempty Ω] : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

theorem card_ne_zero [Nonempty Ω] : (Fintype.card Ω : ℝ) ≠ 0 :=
  ne_of_gt card_pos

@[simp] theorem prob_empty : prob (∅ : Set Ω) = 0 := by
  simp [prob]

@[simp] theorem prob_univ [Nonempty Ω] : prob (Set.univ : Set Ω) = 1 := by
  simp [prob]

theorem prob_nonneg (E : Set Ω) : 0 ≤ prob E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prob_le_one [Nonempty Ω] (E : Set Ω) : prob E ≤ 1 := by
  classical
  rw [prob, div_le_one card_pos]
  exact_mod_cast Finset.card_filter_le (Finset.univ : Finset Ω) _

theorem prob_mono {E F : Set Ω} (hEF : E ⊆ F) : prob E ≤ prob F := by
  classical
  rw [prob, prob]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub :
      Finset.univ.filter (fun ω => ω ∈ E) ⊆
        Finset.univ.filter (fun ω => ω ∈ F) := by
    intro ω hω
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, hEF hω.2⟩
  exact_mod_cast Finset.card_le_card hsub

omit [Fintype Ω] in
@[simp] theorem indicator_of_mem {E : Set Ω} {ω : Ω} (hω : ω ∈ E) :
    indicator E ω = 1 := by
  simp [indicator, hω]

omit [Fintype Ω] in
@[simp] theorem indicator_of_not_mem {E : Set Ω} {ω : Ω} (hω : ω ∉ E) :
    indicator E ω = 0 := by
  simp [indicator, hω]

omit [Fintype Ω] in
theorem indicator_nonneg (E : Set Ω) (ω : Ω) : 0 ≤ indicator E ω := by
  by_cases hω : ω ∈ E <;> simp [indicator, hω]

omit [Fintype Ω] in
theorem indicator_le_one (E : Set Ω) (ω : Ω) : indicator E ω ≤ 1 := by
  by_cases hω : ω ∈ E <;> simp [indicator, hω]

omit [Fintype Ω] in
@[simp] theorem indicator_inter (E F : Set Ω) (ω : Ω) :
    indicator (E ∩ F) ω = indicator E ω * indicator F ω := by
  by_cases hE : ω ∈ E <;> by_cases hF : ω ∈ F <;>
    simp [indicator, hE, hF]

omit [Fintype Ω] in
@[simp] theorem indicator_compl (E : Set Ω) (ω : Ω) :
    indicator Eᶜ ω = 1 - indicator E ω := by
  by_cases hE : ω ∈ E <;> simp [indicator, hE]

@[simp] theorem expect_zero : expect (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [expect]

@[simp] theorem expect_const [Nonempty Ω] (c : ℝ) :
    expect (fun _ : Ω => c) = c := by
  simp [expect]

theorem expect_add (X Y : Ω → ℝ) :
    expect (fun ω => X ω + Y ω) = expect X + expect Y := by
  simp [expect, Finset.sum_add_distrib, add_div]

theorem expect_sub (X Y : Ω → ℝ) :
    expect (fun ω => X ω - Y ω) = expect X - expect Y := by
  simp [expect, Finset.sum_sub_distrib, sub_div]

theorem expect_smul (c : ℝ) (X : Ω → ℝ) :
    expect (fun ω => c * X ω) = c * expect X := by
  rw [expect, expect, ← Finset.mul_sum]
  ring

theorem expect_finset_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, expect (X i) := by
  simp only [expect]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

theorem expect_nonneg {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ expect X := by
  exact div_nonneg (Finset.sum_nonneg fun ω _ => hX ω) (Nat.cast_nonneg _)

theorem expect_mono {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    expect X ≤ expect Y := by
  rw [expect, expect]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun ω _ => hXY ω) (Nat.cast_nonneg _)

@[simp] theorem expect_indicator (E : Set Ω) : expect (indicator E) = prob E := by
  classical
  rw [expect, prob]
  congr 1
  simp [indicator]

theorem prob_compl [Nonempty Ω] (E : Set Ω) : prob Eᶜ = 1 - prob E := by
  calc
    prob Eᶜ = expect (indicator Eᶜ) := (expect_indicator Eᶜ).symm
    _ = expect (fun ω => 1 - indicator E ω) := by
      congr 1
      funext ω
      exact indicator_compl E ω
    _ = 1 - expect (indicator E) := by
      rw [expect_sub, expect_const]
    _ = 1 - prob E := by rw [expect_indicator]

theorem variance_nonneg (X : Ω → ℝ) : 0 ≤ variance X := by
  exact expect_nonneg fun _ => sq_nonneg _

/-- The raw-second-moment formula for variance. -/
theorem variance_eq_secondMoment_sub_sq [Nonempty Ω] (X : Ω → ℝ) :
    variance X = expect (fun ω => (X ω) ^ 2) - (expect X) ^ 2 := by
  calc
    variance X = expect (fun ω =>
        (X ω) ^ 2 - (2 * expect X) * X ω + (expect X) ^ 2) := by
      rw [variance]
      congr 1
      funext ω
      ring
    _ = expect (fun ω => (X ω) ^ 2) -
          expect (fun ω => (2 * expect X) * X ω) +
          expect (fun _ : Ω => (expect X) ^ 2) := by
      rw [expect_add, expect_sub]
    _ = expect (fun ω => (X ω) ^ 2) - (expect X) ^ 2 := by
      rw [expect_smul, expect_const]
      ring

/-- Markov's inequality on a finite uniform sample space. -/
theorem prob_le_expect_div {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    prob {ω | t ≤ X ω} ≤ expect X / t := by
  rw [prob, expect]
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  have hsum :
      ((Finset.univ.filter fun ω => t ≤ X ω).card : ℝ) * t ≤ ∑ ω, X ω := by
    calc
      ((Finset.univ.filter fun ω => t ≤ X ω).card : ℝ) * t =
          ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), t := by simp
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), X ω := by
        exact Finset.sum_le_sum fun ω hω => (Finset.mem_filter.mp hω).2
      _ ≤ ∑ ω, X ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro ω _ _
          exact hX ω
  calc
    ((Finset.univ.filter fun ω => t ≤ X ω).card : ℝ) / Fintype.card Ω
        ≤ ((∑ ω, X ω) / t) / Fintype.card Ω := by
          apply div_le_div_of_nonneg_right _ hcard
          exact (le_div_iff₀ ht).2 (by simpa [mul_comm] using hsum)
    _ = ((∑ ω, X ω) / Fintype.card Ω) / t := by ring

/-- Chebyshev's inequality on a finite uniform sample space. -/
theorem prob_abs_sub_expect_ge_le (X : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    prob {ω | t ≤ |X ω - expect X|} ≤ variance X / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hmarkov := prob_le_expect_div
    (X := fun ω => (X ω - expect X) ^ 2) (fun ω => sq_nonneg _) ht2
  have hevents : {ω | t ^ 2 ≤ (X ω - expect X) ^ 2} =
      {ω | t ≤ |X ω - expect X|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← sq_abs (X ω - expect X)]
    constructor <;> intro h <;> nlinarith [abs_nonneg (X ω - expect X)]
  simpa [variance, hevents] using hmarkov

/-- A finite second-moment inequality for a natural-valued random variable.
If its expectation is positive, the probability of being zero is at most its
variance divided by the square of its expectation. -/
theorem prob_eq_zero_le_variance_div_expect_sq (U : Ω → ℕ)
    (hU : 0 < expect fun ω => (U ω : ℝ)) :
    prob {ω | U ω = 0} ≤
      variance (fun ω => (U ω : ℝ)) /
        (expect fun ω => (U ω : ℝ)) ^ 2 := by
  let μ : ℝ := expect fun ω => (U ω : ℝ)
  have hcheb := prob_abs_sub_expect_ge_le (fun ω => (U ω : ℝ)) hU
  apply le_trans (prob_mono (E := {ω | U ω = 0})
    (F := {ω | μ ≤ |(U ω : ℝ) - μ|}) ?_) hcheb
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  simp [hω, μ, abs_of_nonneg hU.le]

/-! ## Bonferroni bounds from factorial moments -/

/-- The `j`-th descending-factorial moment of a natural-valued random
variable. -/
noncomputable def factorialMoment (Z : Ω → ℕ) (j : ℕ) : ℝ :=
  expect fun ω => (Z ω).descFactorial j

/-- The Bonferroni sum through order `m`, expressed using descending-factorial
moments.  Its `j`-th term is `(-1)^j E[(Z)_j]/j!`. -/
noncomputable def bonferroniSum (Z : Ω → ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ j * factorialMoment Z j / (j.factorial : ℝ)

theorem cast_choose_eq_descFactorial_div (n j : ℕ) :
    (n.choose j : ℝ) = (n.descFactorial j : ℝ) / (j.factorial : ℝ) := by
  apply (eq_div_iff (by positivity : (j.factorial : ℝ) ≠ 0)).2
  norm_cast
  simpa [Nat.mul_comm] using (Nat.descFactorial_eq_factorial_mul_choose n j).symm

/-- A factorial-moment Bonferroni sum is the expectation of the corresponding
pointwise alternating binomial sum. -/
theorem bonferroniSum_eq_expect_choose (Z : Ω → ℕ) (m : ℕ) :
    bonferroniSum Z m =
      expect (fun ω => ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ j * ((Z ω).choose j : ℝ)) := by
  calc
    bonferroniSum Z m =
        ∑ j ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ j / (j.factorial : ℝ)) * factorialMoment Z j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ Finset.range (m + 1),
          expect (fun ω =>
            ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
              ((Z ω).descFactorial j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [factorialMoment, expect_smul]
    _ = expect (fun ω => ∑ j ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
            ((Z ω).descFactorial j : ℝ)) := by
      exact (expect_finset_sum (Finset.range (m + 1)) fun j ω =>
        ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
          ((Z ω).descFactorial j : ℝ)).symm
    _ = expect (fun ω => ∑ j ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ j * ((Z ω).choose j : ℝ)) := by
      congr 1
      funext ω
      apply Finset.sum_congr rfl
      intro j hj
      rw [cast_choose_eq_descFactorial_div]
      ring

private theorem alternating_choose_sum_of_pos (n m : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ j * (n.choose j : ℝ)) =
        (-1 : ℝ) ^ m * ((n - 1).choose m : ℝ) := by
  have h := Int.alternating_sum_range_choose_eq_choose
    (n := n - 1) (m := m)
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hn'] at h
  exact_mod_cast h

private theorem indicator_zero_le_alternating_choose_even (n r : ℕ) :
    (if n = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ Finset.range (2 * r + 1),
        (-1 : ℝ) ^ j * (n.choose j : ℝ) := by
  by_cases hn : n = 0
  · subst n
    rw [Finset.sum_range_succ']
    simp [Nat.choose_zero_succ]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show 2 * r + 1 = 2 * r + 1 by rfl,
      alternating_choose_sum_of_pos n (2 * r) hnpos]
    simp [hn, pow_mul]

private theorem alternating_choose_odd_le_indicator_zero (n r : ℕ) :
    (∑ j ∈ Finset.range (2 * r + 2),
      (-1 : ℝ) ^ j * (n.choose j : ℝ)) ≤
        if n = 0 then (1 : ℝ) else 0 := by
  by_cases hn : n = 0
  · subst n
    rw [Finset.sum_range_succ']
    simp [Nat.choose_zero_succ]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega,
      alternating_choose_sum_of_pos n (2 * r + 1) hnpos]
    simp [hn, pow_succ, pow_mul]

/-- Even Bonferroni truncations are upper bounds for the zero event. -/
theorem prob_eq_zero_le_bonferroni_even (Z : Ω → ℕ) (r : ℕ) :
    prob {ω | Z ω = 0} ≤ bonferroniSum Z (2 * r) := by
  rw [bonferroniSum_eq_expect_choose]
  calc
    prob {ω | Z ω = 0} = expect (indicator {ω | Z ω = 0}) :=
      (expect_indicator _).symm
    _ ≤ expect (fun ω => ∑ j ∈ Finset.range (2 * r + 1),
          (-1 : ℝ) ^ j * ((Z ω).choose j : ℝ)) := by
      apply expect_mono
      intro ω
      by_cases hω : Z ω = 0
      · rw [indicator_of_mem (by simpa)]
        simpa [hω] using indicator_zero_le_alternating_choose_even (Z ω) r
      · rw [indicator_of_not_mem (by simpa)]
        simpa [hω] using indicator_zero_le_alternating_choose_even (Z ω) r

/-- Odd Bonferroni truncations are lower bounds for the zero event. -/
theorem bonferroni_odd_le_prob_eq_zero (Z : Ω → ℕ) (r : ℕ) :
    bonferroniSum Z (2 * r + 1) ≤ prob {ω | Z ω = 0} := by
  rw [bonferroniSum_eq_expect_choose]
  calc
    expect (fun ω => ∑ j ∈ Finset.range (2 * r + 1 + 1),
        (-1 : ℝ) ^ j * ((Z ω).choose j : ℝ)) ≤
        expect (indicator {ω | Z ω = 0}) := by
      apply expect_mono
      intro ω
      by_cases hω : Z ω = 0
      · rw [indicator_of_mem (by simpa)]
        simpa [hω, Nat.add_assoc] using
          alternating_choose_odd_le_indicator_zero (Z ω) r
      · rw [indicator_of_not_mem (by simpa)]
        simpa [hω, Nat.add_assoc] using
          alternating_choose_odd_le_indicator_zero (Z ω) r
    _ = prob {ω | Z ω = 0} := expect_indicator _

end

end Erdos543.FiniteProbability

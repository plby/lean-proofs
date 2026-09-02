import ErdosProblems.Erdos543.FiniteProbability

/-!
# First and second moments of a finite family of missed events

For a finite family `E i` of events, `missedCount E ω` counts how many of them
occur at the outcome `ω`.  This file gives exact first- and second-moment
formulas, followed by quantitative variance and zero-count bounds from
uniform estimates for singleton and distinct-pair probabilities.
-/

open scoped BigOperators

namespace Erdos543.MissedEvents

open FiniteProbability

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- Number of events in the family which occur at `ω`. -/
noncomputable def missedCount (E : ι → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ω ∈ E i).card

omit [Fintype Ω] [DecidableEq ι] in
/-- The missed count, cast to `ℝ`, is the sum of the event indicators. -/
theorem cast_missedCount_eq_sum_indicator (E : ι → Set Ω) (ω : Ω) :
    (missedCount E ω : ℝ) = ∑ i, indicator (E i) ω := by
  classical
  simp [missedCount, indicator]

omit [DecidableEq ι] in
/-- Exact first-moment formula for the missed count. -/
theorem expect_missedCount (E : ι → Set Ω) :
    expect (fun ω => (missedCount E ω : ℝ)) = ∑ i, prob (E i) := by
  calc
    expect (fun ω => (missedCount E ω : ℝ)) =
        expect (fun ω => ∑ i, indicator (E i) ω) := by
      congr 1
      funext ω
      exact cast_missedCount_eq_sum_indicator E ω
    _ = ∑ i, expect (indicator (E i)) :=
      expect_finset_sum Finset.univ (fun i => indicator (E i))
    _ = ∑ i, prob (E i) := by simp

private theorem sq_sum_eq_sum_add_offDiagonal
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, x i * x i = x i) :
    (∑ i ∈ s, x i) ^ 2 =
      (∑ i ∈ s, x i) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, x i * x j := by
  rw [pow_two, Finset.sum_mul]
  calc
    (∑ i ∈ s, x i * ∑ j ∈ s, x j) =
        ∑ i ∈ s, (x i * x i + ∑ j ∈ s.erase i, x i * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.add_sum_erase s x hi, mul_add, Finset.mul_sum]
    _ = (∑ i ∈ s, x i) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, x i * x j := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl hx

/-- Exact raw second-moment formula.  The off-diagonal sum is over ordered
pairs of distinct event indices. -/
theorem expect_missedCount_sq (E : ι → Set Ω) :
    expect (fun ω => (missedCount E ω : ℝ) ^ 2) =
      (∑ i, prob (E i)) +
        ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j) := by
  classical
  calc
    expect (fun ω => (missedCount E ω : ℝ) ^ 2) =
        expect (fun ω => (∑ i, indicator (E i) ω) ^ 2) := by
      congr 1
      funext ω
      rw [cast_missedCount_eq_sum_indicator]
    _ = expect (fun ω =>
          (∑ i, indicator (E i) ω) +
            ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i,
              indicator (E i) ω * indicator (E j) ω) := by
      congr 1
      funext ω
      apply sq_sum_eq_sum_add_offDiagonal
      intro i hi
      by_cases hω : ω ∈ E i <;> simp [indicator, hω]
    _ = expect (fun ω => ∑ i, indicator (E i) ω) +
          expect (fun ω => ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i,
            indicator (E i) ω * indicator (E j) ω) := by
      rw [expect_add]
    _ = (∑ i, expect (indicator (E i))) +
          ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i,
            expect (fun ω => indicator (E i) ω * indicator (E j) ω) := by
      rw [expect_finset_sum]
      congr 1
      rw [expect_finset_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [expect_finset_sum]
    _ = (∑ i, prob (E i)) +
          ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j) := by
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        calc
          expect (fun ω => indicator (E i) ω * indicator (E j) ω) =
              expect (indicator (E i ∩ E j)) := by
            congr 1
            funext ω
            exact (indicator_inter (E i) (E j) ω).symm
          _ = prob (E i ∩ E j) := expect_indicator _

/-- Exact variance formula for a missed-event count. -/
theorem variance_missedCount [Nonempty Ω] (E : ι → Set Ω) :
    variance (fun ω => (missedCount E ω : ℝ)) =
      (∑ i, prob (E i)) +
        ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j) -
          (∑ i, prob (E i)) ^ 2 := by
  rw [variance_eq_secondMoment_sub_sq, expect_missedCount, expect_missedCount_sq]

/-- Exact second descending-factorial moment.  It is the sum of the
probabilities of all ordered intersections with distinct indices. -/
theorem factorialMoment_missedCount_two (E : ι → Set Ω) :
    factorialMoment (missedCount E) 2 =
      ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j) := by
  calc
    factorialMoment (missedCount E) 2 =
        expect (fun ω => (missedCount E ω : ℝ) ^ 2 - missedCount E ω) := by
      rw [factorialMoment]
      congr 1
      funext ω
      rw [Nat.cast_descFactorial_two]
      ring
    _ = expect (fun ω => (missedCount E ω : ℝ) ^ 2) -
          expect (fun ω => (missedCount E ω : ℝ)) := by
      rw [expect_sub]
    _ = ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j) := by
      rw [expect_missedCount_sq, expect_missedCount]
      ring

/-- The number of ordered pairs of distinct indices, as a real number. -/
noncomputable def orderedPairCount (ι : Type*) [Fintype ι] : ℝ :=
  (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)

theorem sum_orderedPairs_const [Nonempty ι] (c : ℝ) :
    (∑ i : ι, ∑ _j ∈ (Finset.univ : Finset ι).erase i, c) =
      orderedPairCount ι * c := by
  simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
    nsmul_eq_mul, Finset.card_univ]
  rw [orderedPairCount]
  push_cast [Nat.cast_sub Fintype.card_pos]
  ring

omit [DecidableEq ι] in
/-- Variance upper bound obtained from uniform absolute errors for singleton
and distinct-pair probabilities. -/
theorem variance_missedCount_le_of_errors [Nonempty Ω] [Nonempty ι]
    (E : ι → Set Ω) (q ε₁ ε₂ : ℝ)
    (hεq : ε₁ ≤ q)
    (hsingle : ∀ i, |prob (E i) - q| ≤ ε₁)
    (hpair : ∀ i j, i ≠ j → |prob (E i ∩ E j) - q ^ 2| ≤ ε₂) :
    variance (fun ω => (missedCount E ω : ℝ)) ≤
      (Fintype.card ι : ℝ) * (q + ε₁) +
        orderedPairCount ι * (q ^ 2 + ε₂) -
          ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2 := by
  classical
  let S : ℝ := ∑ i, prob (E i)
  let P : ℝ :=
    ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, prob (E i ∩ E j)
  have hsingle_lower (i : ι) : q - ε₁ ≤ prob (E i) := by
    have h := (abs_le.mp (hsingle i)).1
    linarith
  have hsingle_upper (i : ι) : prob (E i) ≤ q + ε₁ := by
    have h := (abs_le.mp (hsingle i)).2
    linarith
  have hS_lower : (Fintype.card ι : ℝ) * (q - ε₁) ≤ S := by
    calc
      (Fintype.card ι : ℝ) * (q - ε₁) = ∑ _i : ι, (q - ε₁) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, prob (E i) := Finset.sum_le_sum fun i _ => hsingle_lower i
      _ = S := rfl
  have hS_upper : S ≤ (Fintype.card ι : ℝ) * (q + ε₁) := by
    calc
      S = ∑ i, prob (E i) := rfl
      _ ≤ ∑ _i : ι, (q + ε₁) := Finset.sum_le_sum fun i _ => hsingle_upper i
      _ = (Fintype.card ι : ℝ) * (q + ε₁) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpair_upper (i j : ι) (hij : i ≠ j) :
      prob (E i ∩ E j) ≤ q ^ 2 + ε₂ := by
    have h := (abs_le.mp (hpair i j hij)).2
    linarith
  have hP_upper : P ≤ orderedPairCount ι * (q ^ 2 + ε₂) := by
    calc
      P = ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i,
          prob (E i ∩ E j) := rfl
      _ ≤ ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i,
          (q ^ 2 + ε₂) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hpair_upper i j (Finset.ne_of_mem_erase hj).symm
      _ = orderedPairCount ι * (q ^ 2 + ε₂) :=
        sum_orderedPairs_const (q ^ 2 + ε₂)
  have hbase_nonneg : 0 ≤ (Fintype.card ι : ℝ) * (q - ε₁) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hεq)
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _ => prob_nonneg (E i)
  have hsq : ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2 ≤ S ^ 2 := by
    nlinarith
  rw [variance_missedCount]
  change S + P - S ^ 2 ≤ _
  linarith

omit [DecidableEq ι] in
/-- Quantitative second-moment bound for the event that none of the missed
events occurs.  The denominator is the square of the guaranteed first
moment. -/
theorem prob_no_missed_le_of_errors [Nonempty Ω] [Nonempty ι]
    (E : ι → Set Ω) (q ε₁ ε₂ : ℝ)
    (hεq : ε₁ < q)
    (hsingle : ∀ i, |prob (E i) - q| ≤ ε₁)
    (hpair : ∀ i j, i ≠ j → |prob (E i ∩ E j) - q ^ 2| ≤ ε₂) :
    prob {ω | missedCount E ω = 0} ≤
      ((Fintype.card ι : ℝ) * (q + ε₁) +
          orderedPairCount ι * (q ^ 2 + ε₂) -
            ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2) /
        ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2 := by
  classical
  let μ : ℝ := expect fun ω => (missedCount E ω : ℝ)
  let L : ℝ := (Fintype.card ι : ℝ) * (q - ε₁)
  let B : ℝ := (Fintype.card ι : ℝ) * (q + ε₁) +
    orderedPairCount ι * (q ^ 2 + ε₂) - L ^ 2
  have hsingle_lower (i : ι) : q - ε₁ ≤ prob (E i) := by
    have h := (abs_le.mp (hsingle i)).1
    linarith
  have hμ_lower : L ≤ μ := by
    dsimp [μ]
    rw [expect_missedCount]
    change (Fintype.card ι : ℝ) * (q - ε₁) ≤ ∑ i, prob (E i)
    calc
      (Fintype.card ι : ℝ) * (q - ε₁) = ∑ _i : ι, (q - ε₁) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, prob (E i) := Finset.sum_le_sum fun i _ => hsingle_lower i
  have hL : 0 < L := by
    exact mul_pos (by exact_mod_cast Fintype.card_pos) (sub_pos.mpr hεq)
  have hμ : 0 < μ := lt_of_lt_of_le hL hμ_lower
  have hvar : variance (fun ω => (missedCount E ω : ℝ)) ≤ B := by
    simpa [B, L] using
      variance_missedCount_le_of_errors E q ε₁ ε₂ hεq.le hsingle hpair
  have hvar_nonneg : 0 ≤ variance (fun ω => (missedCount E ω : ℝ)) :=
    variance_nonneg _
  have hB : 0 ≤ B := le_trans hvar_nonneg hvar
  have hsq : L ^ 2 ≤ μ ^ 2 := by nlinarith
  calc
    prob {ω | missedCount E ω = 0} ≤
        variance (fun ω => (missedCount E ω : ℝ)) / μ ^ 2 := by
      exact prob_eq_zero_le_variance_div_expect_sq (missedCount E) hμ
    _ ≤ B / L ^ 2 := by
      exact div_le_div₀ hB hvar (sq_pos_of_pos hL) hsq
    _ = ((Fintype.card ι : ℝ) * (q + ε₁) +
          orderedPairCount ι * (q ^ 2 + ε₂) -
            ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2) /
        ((Fintype.card ι : ℝ) * (q - ε₁)) ^ 2 := by
      rfl

end

end Erdos543.MissedEvents

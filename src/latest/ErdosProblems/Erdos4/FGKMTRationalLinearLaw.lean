import ErdosProblems.Erdos4.FGKMTDivisorProbability
import ErdosProblems.Erdos4.FGKMTSupport

/-! The unsquared divisor law used for the two independent face completions. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem logarithmicReciprocal_nat_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ logarithmicReciprocal b n := by
  have hlog := Real.log_natCast_nonneg n
  unfold logarithmicReciprocal
  positivity

theorem rationalLinear_divisor_pointwise (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ∣ n) :
    logarithmicReciprocal b n * squarefreeHarmonicWeight W n ≤
      (logarithmicReciprocal b ((n / d : ℕ) : ℝ) * squarefreeHarmonicWeight W (n / d)) /
        (d.totient : ℝ) := by
  by_cases hqual : Squarefree n ∧ n.Coprime W
  · have hquot : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq1 : (1 : ℝ) ≤ (n / d : ℕ) := by exact_mod_cast hquot
    have hrecip := logarithmicReciprocal_antitone hb hq1 hn1
      (by exact_mod_cast Nat.div_le_self n d)
    rw [squarefreeHarmonicWeight_divisor hdn hqual.1 hqual.2]
    exact (mul_le_mul_of_nonneg_right hrecip
      (div_nonneg (squarefreeHarmonicWeight_nonneg W (n / d)) (Nat.cast_nonneg d.totient))).trans_eq
        (by ring)
  · rw [squarefreeHarmonicWeight, if_neg hqual, mul_zero]
    exact div_nonneg (mul_nonneg (logarithmicReciprocal_nat_nonneg hb (n / d))
      (squarefreeHarmonicWeight_nonneg W (n / d))) (Nat.cast_nonneg _)

theorem rationalLinear_divisor_mass_le (W R : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n),
      logarithmicReciprocal b n * squarefreeHarmonicWeight W n) ≤
      rationalMass W b R / (d.totient : ℝ) := by
  let S := (Finset.Icc 1 R).filter (fun n => d ∣ n)
  let f : ℕ → ℝ := fun n => logarithmicReciprocal b n * squarefreeHarmonicWeight W n
  change (∑ n ∈ S, f n) ≤ (∑ n ∈ Finset.Icc 1 R, f n) / (d.totient : ℝ)
  calc
    _ ≤ ∑ n ∈ S, f (n / d) / (d.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS := Finset.mem_filter.mp hn
      exact rationalLinear_divisor_pointwise W hb (Finset.mem_Icc.mp hnS.1).1 hd hnS.2
    _ = (∑ n ∈ S.image (fun n => n / d), f n) / (d.totient : ℝ) := by
      rw [Finset.sum_image (divisor_quotient_injective_on d R), Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg (divisor_quotient_image_subset hd R)
        (fun n _ _ => mul_nonneg (logarithmicReciprocal_nat_nonneg hb n)
          (squarefreeHarmonicWeight_nonneg W n))

noncomputable def rationalLinearLaw (W : ℕ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (hR : 1 ≤ R) :
    FiniteLaw (Fin (R + 1)) where
  weight n := (logarithmicReciprocal b n * squarefreeHarmonicWeight W n) / rationalMass W b R
  nonneg n := div_nonneg (mul_nonneg (logarithmicReciprocal_nat_nonneg hb n)
    (squarefreeHarmonicWeight_nonneg W n)) (rationalMass_nonneg hb W R)
  total := by
    rw [← Finset.sum_div, sum_fin_succ_eq_Icc
      (f := fun n : ℕ => logarithmicReciprocal b n * squarefreeHarmonicWeight W n)
      (by rw [squarefreeHarmonicWeight_zero, mul_zero])]
    change rationalMass W b R / rationalMass W b R = 1
    exact div_self (ne_of_gt (zero_lt_one.trans_le (one_le_rationalMass hb W hR)))

theorem rationalLinearLaw_prob_divisor_eq (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R : ℕ} (hR : 1 ≤ R) (d : ℕ) :
    (rationalLinearLaw W hb R hR).prob (fun n => d ∣ (n : ℕ)) =
      (∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n),
        logarithmicReciprocal b n * squarefreeHarmonicWeight W n) / rationalMass W b R := by
  classical
  unfold FiniteLaw.prob rationalLinearLaw
  simp only
  have hpoint (n : Fin (R + 1)) :
      (if d ∣ (n : ℕ) then (logarithmicReciprocal b n * squarefreeHarmonicWeight W n) /
        rationalMass W b R else 0) =
      (if d ∣ (n : ℕ) then logarithmicReciprocal b n * squarefreeHarmonicWeight W n else 0) /
        rationalMass W b R := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_div, sum_fin_succ_eq_Icc
    (f := fun n : ℕ => if d ∣ n then logarithmicReciprocal b n * squarefreeHarmonicWeight W n else 0)
    (by simp [squarefreeHarmonicWeight_zero]), ← Finset.sum_filter]

theorem rationalLinearLaw_prob_divisor_le (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R : ℕ} (hR : 1 ≤ R) {d : ℕ} (hd : 0 < d) :
    (rationalLinearLaw W hb R hR).prob (fun n => d ∣ (n : ℕ)) ≤ (d.totient : ℝ)⁻¹ := by
  rw [rationalLinearLaw_prob_divisor_eq]
  have hM : 0 < rationalMass W b R := zero_lt_one.trans_le (one_le_rationalMass hb W hR)
  have hh := div_le_div_of_nonneg_right (rationalLinear_divisor_mass_le W R hb hd) hM.le
  apply hh.trans_eq
  field_simp

theorem rationalLinearLaw_support (W : ℕ) {b : ℝ} (hb : 0 ≤ b) {R : ℕ} (hR : 1 ≤ R)
    (n : Fin (R + 1)) (hn : 0 < (rationalLinearLaw W hb R hR).weight n) :
    Squarefree (n : ℕ) ∧ (n : ℕ).Coprime W := by
  by_contra hbad
  have hz : squarefreeHarmonicWeight W n = 0 := by
    rw [squarefreeHarmonicWeight, if_neg hbad]
  simp only [rationalLinearLaw, hz, mul_zero, zero_div, lt_self_iff_false] at hn

/-- Extend the smaller face law to the common finite outcome space. -/
noncomputable def rationalFaceLaw (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {T R : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R) : FiniteLaw (Fin (R + 1)) :=
  (rationalLinearLaw W hb T hT).map (Fin.castLE (Nat.succ_le_succ hTR))

theorem rationalFaceLaw_prob_divisor_le (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {T R : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R) {d : ℕ} (hd : 0 < d) :
    (rationalFaceLaw W hb hT hTR).prob (fun n => d ∣ (n : ℕ)) ≤ (d.totient : ℝ)⁻¹ := by
  rw [rationalFaceLaw, FiniteLaw.prob_map]
  exact rationalLinearLaw_prob_divisor_le W hb hT hd

theorem rationalFaceLaw_support (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {T R : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R) (n : Fin (R + 1))
    (hn : 0 < (rationalFaceLaw W hb hT hTR).weight n) :
    Squarefree (n : ℕ) ∧ (n : ℕ).Coprime W ∧ (n : ℕ) ≤ T := by
  obtain ⟨m, hm, rfl⟩ := FiniteLaw.map_support (rationalLinearLaw W hb T hT)
    (Fin.castLE (Nat.succ_le_succ hTR)) n hn
  have hs := rationalLinearLaw_support W hb hT m hm
  exact ⟨hs.1, hs.2, Nat.le_of_lt_succ m.isLt⟩

end Erdos4.FGKMT

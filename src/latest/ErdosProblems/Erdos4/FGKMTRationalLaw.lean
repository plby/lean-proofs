import ErdosProblems.Erdos4.FGKMTRationalMoments
import ErdosProblems.Erdos4.FGKMTProductMoments

/-! The actual finite divisor law underlying the product sieve coefficients. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem sum_fin_succ_eq_Icc {f : ℕ → ℝ} (hf : f 0 = 0) (R : ℕ) :
    (∑ n : Fin (R + 1), f n) = ∑ n ∈ Finset.Icc 1 R, f n := by
  rw [Fin.sum_univ_eq_sum_range, Nat.range_succ_eq_Icc_zero]
  exact sum_start_one_eq hf R

noncomputable def rationalSquareLaw (W : ℕ) (b : ℝ) (R : ℕ) (hR : 1 ≤ R) :
    FiniteLaw (Fin (R + 1)) where
  weight n := (logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) / rationalSquareMass W b R
  nonneg n := div_nonneg
    (mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W n))
    (rationalSquareMass_nonneg W b R)
  total := by
    rw [← Finset.sum_div, sum_fin_succ_eq_Icc
      (f := fun n : ℕ => logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n)
      (by rw [squarefreeHarmonicWeight_zero, mul_zero])]
    change rationalSquareMass W b R / rationalSquareMass W b R = 1
    exact div_self (ne_of_gt (zero_lt_one.trans_le (one_le_rationalSquareMass W b hR)))

theorem rationalSquareLaw_mean_log (W : ℕ) (b : ℝ) {R : ℕ} (hR : 1 ≤ R) :
    (rationalSquareLaw W b R hR).mean (fun n => Real.log (n : ℕ)) =
      rationalLogMoment W b R / rationalSquareMass W b R := by
  unfold FiniteLaw.mean rationalSquareLaw
  simp only
  calc
    _ = (∑ n : Fin (R + 1), Real.log (n : ℕ) *
        logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) / rationalSquareMass W b R := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [sum_fin_succ_eq_Icc (f := fun n : ℕ => Real.log (n : ℝ) *
        logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) (by simp)]
      rfl

theorem rationalSquareLaw_mean_log_le (W : ℕ) {b : ℝ} (hb : 0 < b) {R : ℕ} (hR : 1 ≤ R) :
    (rationalSquareLaw W b R hR).mean (fun n => Real.log (n : ℕ)) ≤
      rationalMass W b R / (b * rationalSquareMass W b R) := by
  rw [rationalSquareLaw_mean_log]
  exact (div_le_div_of_nonneg_right (rationalLogMoment_le hb W R)
    (rationalSquareMass_nonneg W b R)).trans_eq (by ring)

theorem rationalProduct_small_log_probability (I : Type*) [Fintype I] [DecidableEq I]
    (W : ℕ) {b : ℝ} (hb : 0 < b) {R : ℕ} (hR : 1 ≤ R) {L : ℝ} (hL : 0 < L) :
    1 - (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) ≤
      (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
        (fun a => (∑ i, Real.log (a i : ℕ)) ≤ L) := by
  have hh := FiniteLaw.independent_sum_good (fun _ : I => rationalSquareLaw W b R hR)
    (fun _ n => Real.log (n : ℕ)) (fun _ n => Real.log_natCast_nonneg n) hL
  have hmean : (∑ _i : I, (rationalSquareLaw W b R hR).mean (fun n => Real.log (n : ℕ))) ≤
      (Fintype.card I : ℝ) * (rationalMass W b R / (b * rationalSquareMass W b R)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset I))
        (fun _ _ => rationalSquareLaw_mean_log_le W hb hR)
  have hdiv := div_le_div_of_nonneg_right hmean hL.le
  have heq : (Fintype.card I : ℝ) * (rationalMass W b R / (b * rationalSquareMass W b R)) / L =
      (Fintype.card I : ℝ) * rationalMass W b R / (b * rationalSquareMass W b R * L) := by ring
  rw [heq] at hdiv
  linarith

end Erdos4.FGKMT

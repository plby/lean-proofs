import ErdosProblems.Erdos4.FGKMTRationalLaw
import ErdosProblems.Erdos4.FGKMTRationalDivisibility

/-! Actual divisor probabilities and exact pair independence for the sieve law. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem rationalSquareLaw_prob_divisor_eq (W : ℕ) (b : ℝ) {R : ℕ} (hR : 1 ≤ R) (d : ℕ) :
    (rationalSquareLaw W b R hR).prob (fun n => d ∣ (n : ℕ)) =
      (∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n),
        logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) / rationalSquareMass W b R := by
  classical
  unfold FiniteLaw.prob rationalSquareLaw
  simp only
  have hpoint (n : Fin (R + 1)) :
      (if d ∣ (n : ℕ) then (logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) /
        rationalSquareMass W b R else 0) =
      (if d ∣ (n : ℕ) then logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n else 0) /
        rationalSquareMass W b R := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_div, sum_fin_succ_eq_Icc
    (f := fun n : ℕ => if d ∣ n then logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n else 0)
    (by simp [squarefreeHarmonicWeight_zero]), ← Finset.sum_filter]

theorem rationalSquareLaw_prob_divisor_le (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {R : ℕ} (hR : 1 ≤ R) {d : ℕ} (hd : 0 < d) :
    (rationalSquareLaw W b R hR).prob (fun n => d ∣ (n : ℕ)) ≤ (d.totient : ℝ)⁻¹ := by
  rw [rationalSquareLaw_prob_divisor_eq]
  have hM : 0 < rationalSquareMass W b R := zero_lt_one.trans_le (one_le_rationalSquareMass W b hR)
  have hh := div_le_div_of_nonneg_right (rationalSquare_divisor_mass_le W R hb hd) hM.le
  apply hh.trans_eq
  field_simp

theorem rationalSquareLaw_support (W : ℕ) (b : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (n : Fin (R + 1)) (hn : 0 < (rationalSquareLaw W b R hR).weight n) :
    Squarefree (n : ℕ) ∧ (n : ℕ).Coprime W := by
  by_contra hbad
  have hz : squarefreeHarmonicWeight W n = 0 := by
    rw [squarefreeHarmonicWeight, if_neg hbad]
  simp only [rationalSquareLaw, hz, mul_zero, zero_div, lt_self_iff_false] at hn

theorem rationalSquareLaw_prob_excluded_prime (W : ℕ) (b : ℝ) {R : ℕ} (hR : 1 ≤ R)
    {p : ℕ} (hp : p.Prime) (hpW : p ∣ W) :
    (rationalSquareLaw W b R hR).prob (fun n => p ∣ (n : ℕ)) = 0 := by
  classical
  unfold FiniteLaw.prob
  apply Finset.sum_eq_zero
  intro n _hn
  by_cases hpn : p ∣ (n : ℕ)
  · rw [if_pos hpn]
    apply le_antisymm _ ((rationalSquareLaw W b R hR).nonneg n)
    by_contra hpos
    have hsupport := rationalSquareLaw_support W b hR n (lt_of_not_ge hpos)
    have hpcop := hsupport.2.of_dvd hpn hpW
    exact hp.ne_one (by simpa using hpcop)
  · rw [if_neg hpn]

theorem rationalProduct_pair_divisor_probability (I : Type*) [Fintype I] [DecidableEq I]
    (W : ℕ) {b : ℝ} (hb : 0 ≤ b) {R : ℕ} (hR : 1 ≤ R)
    {i j : I} (hij : i ≠ j) {d : ℕ} (hd : 0 < d) :
    (FiniteLaw.independent (fun _ : I => rationalSquareLaw W b R hR)).prob
      (fun a => d ∣ (a i : ℕ) ∧ d ∣ (a j : ℕ)) ≤ ((d.totient : ℝ)⁻¹) ^ 2 := by
  rw [FiniteLaw.independent_prob_pair (fun _ : I => rationalSquareLaw W b R hR) hij
    (fun n : Fin (R + 1) => d ∣ (n : ℕ)) (fun n : Fin (R + 1) => d ∣ (n : ℕ))]
  have hh := rationalSquareLaw_prob_divisor_le W hb hR hd
  have h0 := (rationalSquareLaw W b R hR).prob_nonneg (fun n => d ∣ (n : ℕ))
  simpa only [sq] using mul_le_mul hh hh h0 (inv_nonneg.mpr (Nat.cast_nonneg d.totient))

end Erdos4.FGKMT

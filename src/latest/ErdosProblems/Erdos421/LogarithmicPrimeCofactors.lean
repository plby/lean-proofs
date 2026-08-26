import ErdosProblems.Erdos421.LogarithmicBuchstab
import ErdosProblems.Erdos421.LargePrimeCofactors

/-! # Merging large-prime cofactor windows into bounded arithmetic weights -/

namespace Erdos421

noncomputable def logarithmicPrimeCofactorWindow (P : Finset ℕ) (B z : ℕ) (δ y : ℝ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹ * logarithmicRoughWindow (B / p) z δ (y - Real.log p)

theorem logarithmicRoughWindow_real_sum (B z : ℕ) (δ y : ℝ) :
    logarithmicRoughWindow B z δ y =
      ∑ n ∈ Finset.Icc 1 B, roughIndicator n z * (logarithmicIntegerWeight δ y n).re := by
  rw [logarithmicRoughWindow, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem logarithmic_cofactor_window_sum {p : ℕ} (hp : 0 < p) (B z : ℕ) (δ y : ℝ) :
    (p : ℝ)⁻¹ * logarithmicRoughWindow (B / p) z δ (y - Real.log p) =
      ∑ n ∈ Finset.Icc 1 B, if p ∣ n then
        roughIndicator (n / p) z * (logarithmicIntegerWeight δ y n).re else 0 := by
  rw [logarithmicRoughWindow_real_sum, Finset.mul_sum]
  calc
    _ = ∑ d ∈ Finset.Icc 1 (B / p),
        roughIndicator (p * d / p) z * (logarithmicIntegerWeight δ y (p * d)).re := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_right d hp, logarithmicIntegerWeight_mul_re hp (Finset.mem_Icc.mp hd).1]
      ring
    _ = _ := sum_positive_multiples
      (fun n ↦ roughIndicator (n / p) z * (logarithmicIntegerWeight δ y n).re) hp B

theorem logarithmicPrimeCofactorWindow_merge (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (B z : ℕ) (δ y : ℝ) :
    logarithmicPrimeCofactorWindow P B z δ y =
      ∑ n ∈ Finset.Icc 1 B, primeCofactorWeight P z n * (logarithmicIntegerWeight δ y n).re := by
  unfold logarithmicPrimeCofactorWindow
  calc
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Icc 1 B, if p ∣ n then
        roughIndicator (n / p) z * (logarithmicIntegerWeight δ y n).re else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact logarithmic_cofactor_window_sum (hP p hp) B z δ y
    _ = ∑ n ∈ Finset.Icc 1 B, ∑ p ∈ P, if p ∣ n then
        roughIndicator (n / p) z * (logarithmicIntegerWeight δ y n).re else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primeCofactorWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp

theorem logarithmicPrimeCofactorWindow_buchstab (P : Finset ℕ) (B : ℕ) {w z : ℕ}
    (hwz : w ≤ z) (δ y : ℝ) :
    logarithmicPrimeCofactorWindow P B w δ y = logarithmicPrimeCofactorWindow P B z δ y +
      ∑ q ∈ sievePrimes w z, (q : ℝ)⁻¹ *
        logarithmicPrimeCofactorWindow P (B / q) q δ (y - Real.log q) := by
  have hfirst : logarithmicPrimeCofactorWindow P B w δ y =
      logarithmicPrimeCofactorWindow P B z δ y +
        ∑ p ∈ P, ∑ q ∈ sievePrimes w z, (p : ℝ)⁻¹ * ((q : ℝ)⁻¹ *
          logarithmicRoughWindow (B / p / q) q δ (y - Real.log p - Real.log q)) := by
    unfold logarithmicPrimeCofactorWindow
    simp_rw [logarithmicRoughWindow_buchstab _ hwz, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hfirst, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [logarithmicPrimeCofactorWindow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdiv : B / p / q = B / q / p := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm p q]
  have hshift : y - Real.log p - Real.log q = y - Real.log q - Real.log p := by ring
  rw [hdiv, hshift]
  ring

end Erdos421

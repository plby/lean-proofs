import ErdosProblems.Erdos421.LogarithmicRoughWindows
import ErdosProblems.Erdos421.WeightedBuchstab

/-! # Exact Buchstab identities for the actual logarithmic windows -/

namespace Erdos421

theorem logarithmicIntegerWeight_real_nonneg {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (n : ℕ) :
    0 ≤ (logarithmicIntegerWeight δ y n).re := by
  have h := (oneSidedSchwartzWindow_real_nonneg ((y - Real.log n) / δ)).2
  simp only [logarithmicIntegerWeight, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (mul_nonneg (inv_nonneg.mpr hδ.le) h)

theorem logarithmicRoughWindow_eq_sifted (B z : ℕ) (δ y : ℝ) :
    logarithmicRoughWindow B z δ y =
      ∑ n ∈ sifted (Finset.Icc 1 B) z, (logarithmicIntegerWeight δ y n).re := by
  classical
  rw [logarithmicRoughWindow, Complex.re_sum, sifted, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold roughIndicator
  split_ifs <;> simp

theorem sieveCofactors_Icc {p : ℕ} (hp : 0 < p) (B : ℕ) :
    sieveCofactors (Finset.Icc 1 B) p = Finset.Icc 1 (B / p) := by
  ext d
  rw [mem_sieveCofactors hp, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨hdpos, hdB⟩
    refine ⟨by nlinarith, ?_⟩
    exact (Nat.le_div_iff_mul_le hp).mpr (by simpa only [mul_comm] using hdB)
  · rintro ⟨hdpos, hdB⟩
    refine ⟨Nat.mul_pos hp hdpos, ?_⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hdB

theorem logarithmicIntegerWeight_mul {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (δ y : ℝ) :
    logarithmicIntegerWeight δ y (p * d) =
      ((p : ℝ)⁻¹ : ℝ) • logarithmicIntegerWeight δ (y - Real.log p) d := by
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [logarithmicIntegerWeight, Nat.cast_mul, mul_inv, Real.log_mul hpp.ne' hdp.ne',
    sub_add_eq_sub_sub, smul_smul, mul_assoc]

theorem logarithmicIntegerWeight_mul_re {p d : ℕ} (hp : 0 < p) (hd : 0 < d) (δ y : ℝ) :
    (logarithmicIntegerWeight δ y (p * d)).re =
      (p : ℝ)⁻¹ * (logarithmicIntegerWeight δ (y - Real.log p) d).re := by
  rw [logarithmicIntegerWeight_mul hp hd]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem logarithmicRoughWindow_buchstab (B : ℕ) {w z : ℕ} (hwz : w ≤ z) (δ y : ℝ) :
    logarithmicRoughWindow B w δ y = logarithmicRoughWindow B z δ y +
      ∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹ *
        logarithmicRoughWindow (B / p) p δ (y - Real.log p) := by
  classical
  rw [logarithmicRoughWindow_eq_sifted,
    weighted_buchstab_identity (Finset.Icc 1 B) (fun n ↦ (logarithmicIntegerWeight δ y n).re) hwz,
    ← logarithmicRoughWindow_eq_sifted]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.pos
  rw [sieveCofactors_Icc hpp, logarithmicRoughWindow_eq_sifted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact logarithmicIntegerWeight_mul_re hpp (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 δ y

theorem logarithmicRoughWindow_nonneg (B z : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ logarithmicRoughWindow B z δ y := by
  rw [logarithmicRoughWindow_eq_sifted]
  exact Finset.sum_nonneg (fun n _ ↦ logarithmicIntegerWeight_real_nonneg hδ y n)

theorem logarithmicRoughWindow_antitone (B : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Antitone (fun z ↦ logarithmicRoughWindow B z δ y) := by
  intro w z hwz
  change logarithmicRoughWindow B z δ y ≤ logarithmicRoughWindow B w δ y
  rw [logarithmicRoughWindow_buchstab B hwz]
  have hs : 0 ≤ ∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹ *
      logarithmicRoughWindow (B / p) p δ (y - Real.log p) :=
    Finset.sum_nonneg (fun p _ ↦ mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
      (logarithmicRoughWindow_nonneg _ _ hδ _))
  linarith

end Erdos421

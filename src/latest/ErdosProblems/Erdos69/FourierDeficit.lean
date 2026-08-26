import ErdosProblems.Erdos69.FourierPhase

/-!
# A quantitative deficit for the independent characteristic function
-/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem complexMean_re (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    (μ.complexMean f).re = μ.mean (fun x ↦ (f x).re) := by
  simp [complexMean, mean, Complex.mul_re]

theorem complexMean_im (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    (μ.complexMean f).im = μ.mean (fun x ↦ (f x).im) := by
  simp [complexMean, mean, Complex.mul_im]

theorem complexMean_norm_sq (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    ‖μ.complexMean f‖ ^ 2 =
      μ.mean (fun x ↦ (f x).re) ^ 2 + μ.mean (fun x ↦ (f x).im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, complexMean_re, complexMean_im]
  ring

theorem mean_pair_phaseDeficit (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.mean (fun x ↦ μ.mean (fun y ↦ phaseDeficit (X x) (X y))) =
      1 - ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ^ 2 := by
  rw [complexMean_norm_sq]
  simp only [phaseDeficit, fourierPhase_sub_realPart, mean_sub, mean_add,
    mean_const, mean_const_mul, mean_mul_const]
  ring

theorem two_point_deficit_le (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (a b : Ω) (hab : a ≠ b) :
    2 * μ.mass a * μ.mass b * phaseDeficit (X a) (X b) ≤
      1 - ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ^ 2 := by
  classical
  let F : Ω × Ω → ℝ := fun z ↦ μ.mass z.1 * μ.mass z.2 * phaseDeficit (X z.1) (X z.2)
  have hnonneg (z : Ω × Ω) : 0 ≤ F z :=
    mul_nonneg (mul_nonneg (μ.nonneg _) (μ.nonneg _)) (phaseDeficit_nonneg _ _)
  have hpairs : (a, b) ≠ (b, a) := fun h ↦ hab (congrArg Prod.fst h)
  have hsum : (∑ z ∈ ({(a, b), (b, a)} : Finset (Ω × Ω)), F z) ≤ ∑ z, F z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun z _ _ ↦ hnonneg z)
  have hleft : (∑ z ∈ ({(a, b), (b, a)} : Finset (Ω × Ω)), F z) =
      2 * μ.mass a * μ.mass b * phaseDeficit (X a) (X b) := by
    simp only [Finset.sum_pair hpairs, F, phaseDeficit_symm (X b) (X a)]
    ring
  have hright : (∑ z, F z) =
      μ.mean (fun x ↦ μ.mean (fun y ↦ phaseDeficit (X x) (X y))) := by
    simp [F, Fintype.sum_prod_type, mean, Finset.mul_sum, mul_assoc]
  rw [hleft, hright, mean_pair_phaseDeficit] at hsum
  exact hsum

theorem categorical_fourier_deficit {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : 2 * Fintype.card ι ≤ p) (c : ι → ℝ)
    (i : ι) (hi : |c i| ≤ 1 / 2) :
    8 * c i ^ 2 / p ≤
      1 - ‖(categorical ι p hp (by omega)).complexMean
        (fun x ↦ fourierPhase (optionalValue c x))‖ ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcR : 2 * (Fintype.card ι : ℝ) ≤ p := by exact_mod_cast hcard
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (Fintype.card ι : ℝ) / p := by
    have h := (div_le_iff₀ hpR).mpr (show (Fintype.card ι : ℝ) ≤ (1 / 2 : ℝ) * p by linarith)
    linarith
  have hdef := two_point_deficit_le (categorical ι p hp (by omega))
    (optionalValue c) none (some i) (by simp)
  simp only [categorical, optionalValue] at hdef
  rw [phaseDeficit_symm 0 (c i), phaseDeficit, sub_zero] at hdef
  have hlow := fourierPhase_deficit_lower hi
  have hnonneg := sub_nonneg.mpr (fourierPhase_realPart_le_one (c i))
  have hweight : (1 : ℝ) / p ≤ 2 * (1 - (Fintype.card ι : ℝ) / p) * (1 / p) := by
    calc
      (1 : ℝ) / p = (2 * (1 / 2)) * (1 / p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith :
        2 * (1 / 2 : ℝ) ≤ 2 * (1 - (Fintype.card ι : ℝ) / p)) (by positivity)
  calc
    8 * c i ^ 2 / p ≤ (1 / p) * (1 - (fourierPhase (c i)).re) := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        mul_le_mul_of_nonneg_right hlow (inv_nonneg.mpr hpR.le)
    _ ≤ 2 * (1 - (Fintype.card ι : ℝ) / p) * (1 / p) *
        (1 - (fourierPhase (c i)).re) := mul_le_mul_of_nonneg_right hweight hnonneg
    _ ≤ _ := hdef

theorem categorical_fourier_norm_le {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : 2 * Fintype.card ι ≤ p) (c : ι → ℝ)
    (i : ι) (hi : |c i| ≤ 1 / 2) :
    ‖(categorical ι p hp (by omega)).complexMean
      (fun x ↦ fourierPhase (optionalValue c x))‖ ≤ Real.exp (-4 * c i ^ 2 / p) := by
  have hdef := categorical_fourier_deficit p hp hcard c i hi
  have hexp := Real.one_sub_le_exp_neg (8 * c i ^ 2 / p)
  have heq : Real.exp (-(8 * c i ^ 2 / p)) = (Real.exp (-4 * c i ^ 2 / p)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [heq] at hexp
  have hnonneg := norm_nonneg ((categorical ι p hp (by omega)).complexMean
    (fun x ↦ fourierPhase (optionalValue c x)))
  have hpos := Real.exp_pos (-4 * c i ^ 2 / p)
  nlinarith

end Erdos69.Elementary.FiniteLaw

import ErdosProblems.Erdos4.FGKMTRationalMass

/-! Actual nonnegative finite masses and their logarithmic first moment. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

noncomputable def rationalMass (W : ℕ) (b : ℝ) (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 R, logarithmicReciprocal b n * squarefreeHarmonicWeight W n

noncomputable def rationalSquareMass (W : ℕ) (b : ℝ) (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 R, logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n

noncomputable def rationalLogMoment (W : ℕ) (b : ℝ) (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 R, Real.log (n : ℝ) *
    logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n

theorem squarefreeHarmonicWeight_nonneg (W n : ℕ) : 0 ≤ squarefreeHarmonicWeight W n := by
  unfold squarefreeHarmonicWeight
  split_ifs <;> positivity

theorem squarefreeHarmonicWeight_one (W : ℕ) : squarefreeHarmonicWeight W 1 = 1 := by
  simp [squarefreeHarmonicWeight]

theorem rationalMass_nonneg {b : ℝ} (hb : 0 ≤ b) (W R : ℕ) : 0 ≤ rationalMass W b R := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (logarithmicReciprocal_nonneg hb (by exact_mod_cast (Finset.mem_Icc.mp hn).1))
    (squarefreeHarmonicWeight_nonneg W n)

theorem rationalSquareMass_nonneg (W : ℕ) (b : ℝ) (R : ℕ) : 0 ≤ rationalSquareMass W b R := by
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W n))

theorem rationalLogMoment_nonneg (W : ℕ) (b : ℝ) (R : ℕ) : 0 ≤ rationalLogMoment W b R := by
  exact Finset.sum_nonneg (fun n _ => mul_nonneg
    (mul_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)) (squarefreeHarmonicWeight_nonneg W n))

theorem one_le_rationalMass {b : ℝ} (hb : 0 ≤ b) (W : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ rationalMass W b R := by
  unfold rationalMass
  have hh := Finset.single_le_sum (s := Finset.Icc 1 R)
    (f := fun n : ℕ => logarithmicReciprocal b n * squarefreeHarmonicWeight W n)
    (fun n hn => mul_nonneg (logarithmicReciprocal_nonneg hb (by exact_mod_cast (Finset.mem_Icc.mp hn).1))
      (squarefreeHarmonicWeight_nonneg W n)) (Finset.mem_Icc.mpr ⟨le_rfl, hR⟩)
  simpa only [Nat.cast_one, logarithmicReciprocal, Real.log_one, mul_zero, add_zero, inv_one,
    squarefreeHarmonicWeight_one, mul_one] using hh

theorem one_le_rationalSquareMass (W : ℕ) (b : ℝ) {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ rationalSquareMass W b R := by
  unfold rationalSquareMass
  have hh := Finset.single_le_sum (s := Finset.Icc 1 R)
    (f := fun n : ℕ => logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n)
    (fun n _ => mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W n))
    (Finset.mem_Icc.mpr ⟨le_rfl, hR⟩)
  simpa only [Nat.cast_one, logarithmicReciprocal, Real.log_one, mul_zero, add_zero, inv_one,
    one_pow, squarefreeHarmonicWeight_one, mul_one] using hh

theorem logarithmicReciprocal_moment_pointwise {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    b * Real.log x * logarithmicReciprocal b x ^ 2 ≤ logarithmicReciprocal b x := by
  have hbase := logarithmicReciprocal_base_pos hb hx
  have hid : (1 + b * Real.log x) * logarithmicReciprocal b x ^ 2 = logarithmicReciprocal b x := by
    unfold logarithmicReciprocal
    field_simp
  exact (mul_le_mul_of_nonneg_right (by linarith : b * Real.log x ≤ 1 + b * Real.log x)
    (sq_nonneg (logarithmicReciprocal b x))).trans_eq hid

theorem rationalLogMoment_mul_le {b : ℝ} (hb : 0 ≤ b) (W R : ℕ) :
    b * rationalLogMoment W b R ≤ rationalMass W b R := by
  unfold rationalLogMoment rationalMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hh := mul_le_mul_of_nonneg_right
    (logarithmicReciprocal_moment_pointwise (x := (n : ℝ)) hb (by exact_mod_cast (Finset.mem_Icc.mp hn).1))
    (squarefreeHarmonicWeight_nonneg W n)
  simpa only [mul_assoc] using hh

theorem rationalLogMoment_le {b : ℝ} (hb : 0 < b) (W R : ℕ) :
    rationalLogMoment W b R ≤ rationalMass W b R / b := by
  apply (le_div_iff₀ hb).mpr
  simpa only [mul_comm] using rationalLogMoment_mul_le hb.le W R

theorem rationalMass_upper {W R : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hR : 1 ≤ R)
    {b : ℝ} (hb : 0 < b) :
    rationalMass W b R ≤ coprimeHarmonicDensity W *
      (Real.log (1 + b * Real.log (R : ℝ)) / b) + harmonicTransferError W := by
  have hh := (abs_le.mp (reciprocal_harmonic_mass_error hW hSq hR hb)).2
  change rationalMass W b R - _ ≤ _ at hh
  linarith

theorem rationalSquareMass_lower {W R : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hR : 1 ≤ R)
    {b : ℝ} (hb : 0 ≤ b) :
    coprimeHarmonicDensity W * (Real.log (R : ℝ) / (1 + b * Real.log (R : ℝ))) -
      harmonicTransferError W ≤ rationalSquareMass W b R := by
  have hh := (abs_le.mp (reciprocal_sq_harmonic_mass_error hW hSq hR hb)).1
  change _ ≤ rationalSquareMass W b R - _ at hh
  linarith

end Erdos4.FGKMT

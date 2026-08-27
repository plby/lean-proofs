import ErdosProblems.Erdos4.FGKMTTranslatedWeights
import ErdosProblems.Erdos4.DivisibilityExpansion

/-! Exact divisor-indicator expansion and pointwise bounds for the growing rational weights. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical DivisorCoefficients LocalOrthogonality LocalIndicatorExpansion DivisibilityExpansion

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def rationalCutoffProfile (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : ℝ :=
  if totalDivisor ell a ≤ R then rationalProfileProduct b ell a else 0

noncomputable def rationalDivisorCoefficient (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (c : P → Option (Fin k)) : ℝ :=
  ∑ a : P → Option (Fin k), rationalCutoffProfile b R ell a *
    ∏ p, transition (ell p) (a p) (c p)

theorem rationalCutoffProfile_nonneg {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : 0 ≤ rationalCutoffProfile b R ell a := by
  unfold rationalCutoffProfile
  split_ifs
  · exact rationalProfileProduct_nonneg hb ell a
  · exact le_rfl

theorem rationalProfileProduct_le_one {b : ℝ} (hb : 0 ≤ b)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (a : P → Option (Fin k)) :
    rationalProfileProduct b ell a ≤ 1 := by
  unfold rationalProfileProduct
  apply Finset.prod_le_one (fun i _ => logarithmicReciprocal_nat_nonneg hb _)
  intro i _
  apply logarithmicReciprocal_le_one hb
  exact_mod_cast (show 1 ≤ coordinateDivisor ell a i from coordinateDivisor_pos ell hell a i)

theorem rationalCoefficient_factor (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) :
    rationalCoefficient b R ell a = rationalCutoffProfile b R ell a * normalization ell a := by
  unfold rationalCoefficient rationalCutoffProfile
  split_ifs <;> simp

theorem rational_expansion_eq (b : ℝ) (R : ℕ) (ell : P → ℕ) (s : P → Option (Fin k)) :
    (∑ c, rationalDivisorCoefficient b R ell c * evaluation s c) =
      ∑ a, rationalCoefficient b R ell a * ∏ p, extendedBasis (ell p : ℝ) (a p) (s p) := by
  unfold rationalDivisorCoefficient evaluation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = rationalCutoffProfile b R ell a * ∑ c : P → Option (Fin k),
        ∏ p, transition (ell p) (a p) (c p) * indicator (s p) (c p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.prod_mul_distrib]
      ring
    _ = rationalCutoffProfile b R ell a * ∏ p, localWeight (ell p) (a p) *
        extendedBasis (ell p : ℝ) (a p) (s p) := by
      rw [← Fintype.prod_sum (fun p (c : Option (Fin k)) =>
        transition (ell p) (a p) c * indicator (s p) c)]
      simp only [local_expansion]
    _ = _ := by
      rw [Finset.prod_mul_distrib, rationalCoefficient_factor]
      unfold normalization
      ring

theorem rational_sum_abs_coefficient_le_mass {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) :
    (∑ c : P → Option (Fin k), |rationalDivisorCoefficient b R ell c|) ≤
      CutoffMass.mass (k := k) R ell (rowCost k) := by
  have hq := rationalCutoffProfile_nonneg (k := k) hb R ell
  have hpoint : ∀ a : P → Option (Fin k),
      rationalCutoffProfile b R ell a * (∏ p, ∑ c : Option (Fin k), |transition (ell p) (a p) c|) ≤
        if totalDivisor ell a ≤ R then CutoffMass.labelCost (rowCost k) a else 0 := by
    intro a
    have hprod : (∏ p, ∑ c : Option (Fin k), |transition (ell p) (a p) c|) ≤
        CutoffMass.labelCost (rowCost k) a := by
      apply Finset.prod_le_prod
      · intro p _
        exact Finset.sum_nonneg (fun c _ => abs_nonneg _)
      · intro p _
        exact row_bound (hell p) (a p)
    by_cases ha : totalDivisor ell a ≤ R
    · rw [rationalCutoffProfile, if_pos ha, if_pos ha]
      have hh := mul_le_mul (rationalProfileProduct_le_one hb ell
        (fun p => by have := hell p; omega) a) hprod
        (Finset.prod_nonneg (fun p _ => Finset.sum_nonneg (fun c _ => abs_nonneg _))) zero_le_one
      simpa only [one_mul] using hh
    · simp [rationalCutoffProfile, ha]
  calc
    _ ≤ ∑ c : P → Option (Fin k), ∑ a : P → Option (Fin k),
        rationalCutoffProfile b R ell a * ∏ p, |transition (ell p) (a p) (c p)| := by
      apply Finset.sum_le_sum
      intro c _
      have hh := Finset.abs_sum_le_sum_abs
        (fun a : P → Option (Fin k) => rationalCutoffProfile b R ell a *
          ∏ p, transition (ell p) (a p) (c p)) Finset.univ
      simpa only [rationalDivisorCoefficient, abs_mul, abs_of_nonneg (hq _), Finset.abs_prod] using hh
    _ = ∑ a : P → Option (Fin k), rationalCutoffProfile b R ell a *
        ∏ p, ∑ c : Option (Fin k), |transition (ell p) (a p) c| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun p (c : Option (Fin k)) => |transition (ell p) (a p) c|)]
    _ ≤ _ := Finset.sum_le_sum (fun a _ => hpoint a)

theorem rational_sum_abs_coefficient_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) :
    (∑ c : P → Option (Fin k), |rationalDivisorCoefficient b R ell c|) ≤
      (R : ℝ) ^ 2 * Real.exp ((k : ℝ) * rowCost k * ∑ p, 1 / (ell p : ℝ) ^ 2) :=
  (rational_sum_abs_coefficient_le_mass hb R ell hell).trans
    (CutoffMass.mass_le R ell (fun p => by have := hell p; omega) (rowCost_nonneg k))

theorem rational_amplitude_abs_le_mass {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (s : P → Option (Fin k)) :
    |∑ a, rationalCoefficient b R ell a * ∏ p, extendedBasis (ell p : ℝ) (a p) (s p)| ≤
      CutoffMass.mass (k := k) R ell (rowCost k) := by
  rw [← rational_expansion_eq]
  calc
    _ ≤ ∑ c : P → Option (Fin k), |rationalDivisorCoefficient b R ell c * evaluation s c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : P → Option (Fin k), |rationalDivisorCoefficient b R ell c| := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul, abs_of_nonneg (evaluation_nonneg s c)]
      exact mul_le_of_le_one_right (abs_nonneg _) (evaluation_le_one s c)
    _ ≤ _ := rational_sum_abs_coefficient_le_mass hb R ell hell

variable (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

theorem translatedSmallMask_le_one (h : Fin k → ℕ) (Y p n : ℕ) :
    translatedSmallMask ell h Y p n ≤ 1 := by
  apply Finset.prod_le_one
  · intro l _
    split_ifs <;> norm_num
  · intro l _
    split_ifs <;> norm_num

theorem rationalTranslatedAmplitude_abs_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ l, k + 2 ≤ ell l)
    (htail : (k : ℝ) * rowCost k * ∑ l, 1 / (ell l : ℝ) ^ 2 ≤ 1)
    (h : Fin k → ℕ) (Y p n : ℕ) :
    |rationalTranslatedAmplitude ell b R h Y p n| ≤ Real.exp 1 * (R : ℝ) ^ 2 :=
  (rational_amplitude_abs_le_mass hb R ell hell (translatedResidueState ell h Y n p)).trans
    (CutoffMass.mass_le_of_small_tail R ell (fun l => by have := hell l; omega)
      (rowCost_nonneg k) htail)

theorem maskedTranslatedWeight_le {Q : Type*} [Fintype Q] [DecidableEq Q]
    (ell₀ : Q → ℕ) [∀ q, Fact (ell₀ q).Prime]
    {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (hell : ∀ l, k + 2 ≤ ell l)
    (htail : (k : ℝ) * rowCost k * ∑ l, 1 / (ell l : ℝ) ^ 2 ≤ 1)
    (h : Fin k → ℕ) (Y p n : ℕ) :
    maskedTranslatedWeight ell₀ ell b R h Y p n ≤ Real.exp 1 ^ 2 * (R : ℝ) ^ 4 := by
  have habs := rationalTranslatedAmplitude_abs_le ell hb R hell htail h Y p n
  have hsq := (sq_le_sq₀ (abs_nonneg (rationalTranslatedAmplitude ell b R h Y p n))
    (mul_nonneg (Real.exp_pos 1).le (sq_nonneg (R : ℝ)))).mpr habs
  rw [sq_abs, mul_pow, ← pow_mul] at hsq
  exact (mul_le_of_le_one_left (sq_nonneg (rationalTranslatedAmplitude ell b R h Y p n))
    (translatedSmallMask_le_one ell₀ h Y p n)).trans hsq

end Erdos4.FGKMT

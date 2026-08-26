import ErdosProblems.Erdos421.SelbergSupport

/-! # Uniform bounds for the optimized Selberg coefficients -/

namespace Erdos421

open scoped ArithmeticFunction.Moebius

theorem upperMobiusTransform_cofactors (y : ℕ → ℝ) {P d : ℕ}
    (hP : P ≠ 0) (hd : d ∣ P) :
    upperMobiusTransform P y d =
      ∑ e ∈ (P / d).divisors, (μ e : ℝ) * y (d * e) := by
  rw [upperMobiusTransform, lowerMobiusTransform,
    Nat.sum_divisorsAntidiagonal (fun a b : ℕ ↦ (μ a : ℝ) * y (P / b))]
  apply Finset.sum_congr rfl
  intro e he
  have hde : d * e ∣ P :=
    (Nat.dvd_div_iff_mul_dvd hd).mp (Nat.dvd_of_mem_divisors he)
  rw [Nat.div_div_eq_div_mul, Nat.div_div_self hde hP]

theorem selbergOptimizedWeight_abs_le (s : BoundingSieve) {D d : ℕ}
    (hD : 1 ≤ D) (hd : d ∣ s.prodPrimes) :
    |selbergOptimizedWeight s D d| ≤ (s.nu d)⁻¹ * s.selbergTerms d := by
  classical
  have hP := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hP)
  have hν : 0 < s.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hd
  have hg : 0 < s.selbergTerms d := BoundingSieve.selbergTerms_pos hd
  have hG := selbergNormalizer_pos s hD
  have hterm (e : ℕ) (he : e ∈ (s.prodPrimes / d).divisors) :
      |(μ e : ℝ) * selbergTarget s D (d * e)| ≤
        s.selbergTerms d / selbergNormalizer s D *
          (if e ≤ D then s.selbergTerms e else 0) := by
    have heP : e ∣ s.prodPrimes :=
      (Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd)
    have hde : d * e ∣ s.prodPrimes :=
      (Nat.dvd_div_iff_mul_dvd hd).mp (Nat.dvd_of_mem_divisors he)
    have hcop : Nat.Coprime d e := Nat.coprime_of_squarefree_mul
      (BoundingSieve.squarefree_of_dvd_prodPrimes hde)
    have hge : 0 < s.selbergTerms e := BoundingSieve.selbergTerms_pos heP
    have hgde : 0 < s.selbergTerms (d * e) := BoundingSieve.selbergTerms_pos hde
    rw [selbergTarget]
    by_cases hdeD : d * e ≤ D
    · have heD : e ≤ D := (Nat.le_mul_of_pos_left e hdpos).trans hdeD
      rw [if_pos hdeD, if_pos heD, abs_mul, abs_div, abs_mul,
        abs_of_pos (BoundingSieve.selbergTerms_pos hde), abs_of_pos hG]
      have hμe : |(μ e : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
      have hμde : |(μ (d * e) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d * e))
      calc
        _ ≤ 1 * (1 * s.selbergTerms (d * e) / selbergNormalizer s D) := by
          gcongr
        _ = _ := by rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop]; ring
    · rw [if_neg hdeD, mul_zero, abs_zero]
      apply mul_nonneg (div_nonneg hg.le hG.le)
      split_ifs <;> positivity
  have hsum : (∑ e ∈ (s.prodPrimes / d).divisors,
      if e ≤ D then s.selbergTerms e else 0) ≤ selbergNormalizer s D := by
    rw [selbergNormalizer, Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Nat.mem_divisors.mpr
        ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd), hP⟩
    · intro e he _
      split_ifs
      · exact (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors he)).le
      · exact le_rfl
  rw [selbergOptimizedWeight, if_pos hd, abs_mul, abs_of_pos (inv_pos.mpr hν),
    upperMobiusTransform_cofactors _ hP hd]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hν.le)
  calc
    _ ≤ ∑ e ∈ (s.prodPrimes / d).divisors,
        |(μ e : ℝ) * selbergTarget s D (d * e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (s.prodPrimes / d).divisors,
        s.selbergTerms d / selbergNormalizer s D *
          (if e ≤ D then s.selbergTerms e else 0) := Finset.sum_le_sum hterm
    _ = s.selbergTerms d / selbergNormalizer s D *
        ∑ e ∈ (s.prodPrimes / d).divisors,
          (if e ≤ D then s.selbergTerms e else 0) := by rw [Finset.mul_sum]
    _ ≤ s.selbergTerms d / selbergNormalizer s D * selbergNormalizer s D :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hg.le hG.le)
    _ = _ := div_mul_cancel₀ _ hG.ne'

end Erdos421

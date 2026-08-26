import ErdosProblems.Erdos67b.MRAuxiliaryRamare

/-!
# Mean square of the auxiliary missing-prime error

The error coefficient is supported on the actual missing-prime set and
has norm at most `1/n`. Its vertical mean square is bounded by the finite
missing-block cardinality, uniformly in the original typical family.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace Erdos67b

noncomputable section

theorem mrAuxiliaryMissingCoefficient_eq_zero_of_not_mem
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {Z n : ℕ} (f : ℕ → ℂ)
    (hn : n ∉ missingPrimeBlockSet I Z) :
    mrAuxiliaryMissingCoefficient blocks I Z f n = 0 := by
  classical
  rw [mrAuxiliaryMissingCoefficient_eq]
  split_ifs with h
  · have htyp := mem_typicalFactorizationSet.mp h.1
    exact False.elim (hn (mem_missingPrimeBlockSet.mpr ⟨htyp.1, htyp.2.1, h.2⟩))
  · rfl

theorem norm_mrAuxiliaryMissingCoefficient_le
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {Z : ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖mrAuxiliaryMissingCoefficient blocks I Z f n‖ ≤ (n : ℝ)⁻¹ := by
  classical
  rw [mrAuxiliaryMissingCoefficient_eq]
  split_ifs
  · rw [norm_div, Complex.norm_natCast]
    simpa only [one_div] using
      div_le_div_of_nonneg_right (hbound n hn) (Nat.cast_nonneg n)
  · simp

theorem sum_normSq_mrAuxiliaryMissingCoefficient_le
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) {X : ℕ} (hX : 0 < X)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (mrAuxiliaryMissingCoefficient blocks I (2 * X) f n)) ≤
        (missingPrimeBlockSet I (2 * X)).card / (X : ℝ) ^ 2 := by
  classical
  let S := (Finset.Ioc X (2 * X)).filter (fun n ↦ n ∈ missingPrimeBlockSet I (2 * X))
  have hsubset : S ⊆ missingPrimeBlockSet I (2 * X) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have heq : (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (mrAuxiliaryMissingCoefficient blocks I (2 * X) f n)) =
      ∑ n ∈ S, Complex.normSq (mrAuxiliaryMissingCoefficient blocks I (2 * X) f n) := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hm : n ∈ missingPrimeBlockSet I (2 * X)
    · simp only [hm, ↓reduceIte]
    · rw [if_neg hm, mrAuxiliaryMissingCoefficient_eq_zero_of_not_mem f hm]
      simp
  rw [heq]
  calc
    _ ≤ ∑ _n ∈ S, (X : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnX := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      have hh := norm_mrAuxiliaryMissingCoefficient_le (blocks := blocks) (I := I)
        (Z := 2 * X) hbound (hX.trans hnX)
      have hinv : (n : ℝ)⁻¹ ≤ (X : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hX) (by exact_mod_cast hnX.le)
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hh.trans hinv) 2
    _ = (S.card : ℝ) * (X : ℝ)⁻¹ ^ 2 := by simp
    _ ≤ (missingPrimeBlockSet I (2 * X)).card * (X : ℝ)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsubset) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, inv_pow]

theorem intervalIntegral_mrAuxiliaryMissingPolynomial_le
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) {X : ℕ} (hX : 0 < X)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrAuxiliaryMissingPolynomial blocks I f X t‖ ^ 2) ≤
      (2 * T + 4 * Real.pi * X) *
        (missingPrimeBlockSet I (2 * X)).card / (X : ℝ) ^ 2 := by
  have hmass := sum_normSq_mrAuxiliaryMissingCoefficient_le blocks I hX hbound
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le_support
    (show 0 < 2 * X by omega)
    (fun n hn ↦ hX.trans (Finset.mem_Ioc.mp hn).1)
    (fun n hn ↦ (Finset.mem_Ioc.mp hn).2)
    (mrAuxiliaryMissingCoefficient blocks I (2 * X) f) hT
  unfold mrAuxiliaryMissingPolynomial
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
          (mrAuxiliaryMissingCoefficient blocks I (2 * X) f) t) *
        logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
          (mrAuxiliaryMissingCoefficient blocks I (2 * X) f) t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) *
        ∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (mrAuxiliaryMissingCoefficient blocks I (2 * X) f n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) *
        ((missingPrimeBlockSet I (2 * X)).card / (X : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by push_cast; ring

end

end Erdos67b

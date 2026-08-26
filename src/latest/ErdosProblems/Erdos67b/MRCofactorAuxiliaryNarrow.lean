import ErdosProblems.Erdos67b.MRCofactorAuxiliaryRectangle
import ErdosProblems.Erdos67b.MRSmallPrimeSaving

/-!
# Pointwise extraction of the actual auxiliary cofactor

The auxiliary narrow rectangle bounds follow from the source logarithmic
range. An empty prime subblock contributes zero; a nonempty one certifies
the order of the rounded endpoints without a prime-existence assumption.
-/

open Filter

namespace Erdos67b

noncomputable section

theorem mrNarrowPrimeInterval_lower_ge_four {H : ℝ} {r : ℕ}
    (hu : 3 ≤ (r : ℝ) / H) : 4 ≤ (mrNarrowPrimeInterval H r).1 := by
  have he := Real.add_one_le_exp ((r : ℝ) / H)
  have hc := Nat.le_ceil (Real.exp ((r : ℝ) / H))
  have hh : (4 : ℝ) ≤ (mrNarrowPrimeInterval H r).1 := by
    change (4 : ℝ) ≤ (⌈Real.exp ((r : ℝ) / H)⌉₊ : ℝ)
    linarith
  exact_mod_cast hh

theorem mrNarrowPrimeInterval_order_of_nonempty
    {H : ℝ} (hH : 0 < H) {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {r : ℕ} (hnonempty : (mrPrimeSubblock H A r).Nonempty) :
    (mrNarrowPrimeInterval H r).1 ≤ (mrNarrowPrimeInterval H r).2 := by
  obtain ⟨p, hp⟩ := hnonempty
  have hh := mrPrimeSubblock_integer_bounds hH hA hp
  exact hh.1.trans hh.2

theorem mrNarrowPrimeInterval_twice_upper_sq_le
    {H : ℝ} (hH : 1 ≤ H) {r X : ℕ} (hX : 0 < X)
    (hL : 8 ≤ Real.log (X : ℝ)) (hLL : 8 ≤ Real.log (Real.log (X : ℝ)))
    (hu : (r : ℝ) / H ≤ Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) :
    2 * (mrNarrowPrimeInterval H r).2 ^ 2 ≤ X := by
  have hupper := mrNarrowPrimeInterval_upper_le_small_power
    (eta := 1) (by norm_num) (by simpa using hL) (by simpa using hLL) hH hu
  simp only [one_mul] at hupper
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hreal : 2 * ((mrNarrowPrimeInterval H r).2 : ℝ) ^ 2 ≤ (X : ℝ) := by
    calc
      _ ≤ 2 * Real.exp (Real.log (X : ℝ) / 4) ^ 2 := by
        gcongr
      _ = Real.exp (Real.log 2 + 2 * (Real.log (X : ℝ) / 4)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        congr 1
        simpa using (Real.exp_nat_mul (Real.log (X : ℝ) / 4) 2).symm
      _ ≤ Real.exp (Real.log (X : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = (X : ℝ) := Real.exp_log (by exact_mod_cast hX)
  exact_mod_cast hreal

theorem mrExists_uniform_small_auxiliary_prime_cofactor_product
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤
          Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) →
      ∀ {H : ℝ}, 2 ≤ H → ∀ r : ℕ, 3 ≤ (r : ℝ) / H →
        (r : ℝ) / H ≤ Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A r)
            (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
              (mrNarrowPrimeInterval H r) X) (mrFiniteCofactorLineCoefficient A f) t‖ ≤
          epsilon * ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A r)
            (mrFinitePrimeLineCoefficient f) t‖ := by
  classical
  obtain ⟨M₀, X₁, hM₀, hX₁, hrectangle⟩ :=
    mrExists_uniform_small_auxiliary_cofactor_rectangle hepsilon
  have hall : ∀ᶠ X : ℕ in atTop,
      8 ≤ Real.log (X : ℝ) ∧ 8 ≤ Real.log (Real.log (X : ℝ)) := by
    filter_upwards [EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 8),
      (Real.tendsto_log_atTop.comp EulerSubpower.tendsto_log_nat_atTop).eventually
        (eventually_ge_atTop 8)] with X hL hLL
    exact ⟨hL, hLL⟩
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 hall
  refine ⟨M₀, max X₁ X₂, hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper I A hA hAlog H hH r hu3 hu f hmul hbound hnonpret t ht
  by_cases hempty : mrPrimeSubblock H A r = ∅
  · simp [hempty, logarithmicDirichletPolynomial]
  have hnonempty : (mrPrimeSubblock H A r).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hL, hLL⟩ := hX₂ X ((le_max_right _ _).trans hX)
  have hXpos : 0 < X := lt_of_lt_of_le (by omega : 0 < X₁) ((le_max_left _ _).trans hX)
  have hP := mrNarrowPrimeInterval_lower_ge_four hu3
  have hPQ := mrNarrowPrimeInterval_order_of_nonempty (by linarith : 0 < H) hA hnonempty
  have hQP := mrNarrowPrimeInterval_dyadic_width hH r
  have hsize := mrNarrowPrimeInterval_twice_upper_sq_le (by linarith : 1 ≤ H) hXpos hL hLL hu
  have hcofactor := hrectangle hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq
    hbudget hmertens J hupper I A hA hAlog hP hPQ hQP hsize
    hmul hbound hnonpret (-t) (by simpa only [abs_neg] using ht)
  simp only [neg_neg] at hcofactor
  rw [norm_mul]
  calc
    _ ≤ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A r)
        (mrFinitePrimeLineCoefficient f) t‖ * epsilon :=
      mul_le_mul_of_nonneg_left hcofactor (norm_nonneg _)
    _ = _ := mul_comm _ _

end

end Erdos67b

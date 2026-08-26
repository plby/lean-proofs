import ErdosProblems.Erdos67b.MRCofactorSelectedScheduledRectangle
import ErdosProblems.Erdos67b.MRSelectedCofactorParameters
import ErdosProblems.Erdos67b.MRCofactorAuxiliaryNarrow

/-!
# Selected-cofactor smallness paying the fixed-power energy factor

The upper exponent is chosen before all ambient thresholds. The actual
cofactor bound is proportional to that exponent, and so its square pays
the corresponding inverse-square scalar cost. No prime-energy theorem
is assumed or asserted here.
-/

open Filter

namespace Erdos67b

noncomputable section

theorem mrExists_selected_linear_amplitude {C xi thetaMax : ℝ}
    (hC : 0 < C) (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ tau : ℝ, 0 ≤ tau ∧ ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      (tau + 1) * theta ≤ 1 / 4 ∧ ∃ epsilon : ℝ, 0 < epsilon ∧
        C * (epsilon + Real.exp (-tau)) ≤ xi * theta := by
  obtain ⟨tau, htau, theta, htheta, hthetaMax', _, hproduct, epsilon, hepsilon, hbudget⟩ :=
    mrExists_selected_tail_and_prefix_budget (D := C ^ 2) (sq_pos_of_pos hxi) hthetaMax
  refine ⟨tau, htau, theta, htheta, hthetaMax', by linarith, epsilon, hepsilon, ?_⟩
  have heq : (C * (epsilon + Real.exp (-tau)) / theta) ^ 2 =
      C ^ 2 * theta⁻¹ ^ 2 * (epsilon + Real.exp (-tau)) ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  rw [← heq] at hbudget
  have hnonneg : 0 ≤ C * (epsilon + Real.exp (-tau)) / theta := by positivity
  have hh : C * (epsilon + Real.exp (-tau)) / theta ≤ xi := by nlinarith
  exact (div_le_iff₀ htheta).1 hh

theorem mrExists_fixedPower_small_selected_rectangle
    {r xi thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧ ∃ M₀ X₀ : ℕ,
      0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P →
        (Q : ℝ) ≤ Real.exp (theta * Real.log (X : ℝ) + 1) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient A f) (-t)‖ ≤ xi * theta := by
  obtain ⟨tau, htau, theta, htheta, hthetaMax', hpower, epsilon, hepsilon, hsmall⟩ :=
    mrExists_selected_linear_amplitude
      (mul_pos (by norm_num : (0 : ℝ) < 9) (mrSelectedPrimeRatioCost_pos r)) hxi hthetaMax
  obtain ⟨M₀, X₀, hM₀, hX₀, hrectangle⟩ :=
    mrExists_selected_scheduled_cofactor_rectangle hr hrOne htau htheta hpower hepsilon
  refine ⟨theta, htheta, hthetaMax', M₀, X₀, hM₀, hX₀, ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens J hupper
    I A hA hlower hAupper P Q hP hPQ hQP hQ f hmul hbound hnonpret t ht
  exact (hrectangle hM hX heta hp hq hpq hlogq hbudget hmertens J hupper
    I A hA hlower hAupper hP hPQ hQP hQ hmul hbound hnonpret t ht).trans hsmall

theorem mrPrimeSubblock_log_parameter_bounds {H b : ℝ} (hH : 2 ≤ H)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hlower : ∀ p ∈ A, 4 ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b)
    {s : ℕ} (hnonempty : (mrPrimeSubblock H A s).Nonempty) :
    3 ≤ (s : ℝ) / H ∧ (s : ℝ) / H ≤ b := by
  obtain ⟨p, hp⟩ := hnonempty
  have hpA := mrPrimeSubblock_subset H A s hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (hA p hpA).pos
  have hHpos : 0 < H := by linarith
  have hreal := mrPrimeSubblock_real_bounds hHpos hA hp
  have hlo := Real.log_le_log (Real.exp_pos _) hreal.1
  have hhi := Real.log_le_log hpPos hreal.2
  rw [Real.log_exp] at hlo hhi
  have hinv : 1 / H ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hHpos).2
    linarith
  have hpFour := hlower p hpA
  have hpUpper := hupper p hpA
  push_cast at hhi
  rw [add_div] at hhi
  exact ⟨by linarith, hlo.trans hpUpper⟩

theorem mrExists_fixedPower_small_selected_product
    {r xi thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧ ∃ M₀ X₀ : ℕ,
      0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {H : ℝ}, 2 ≤ H → ∀ s : ℕ,
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
            (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
              (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ≤
          xi * theta * ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
            (mrFinitePrimeLineCoefficient f) t‖ := by
  classical
  obtain ⟨theta, htheta, hthetaMax', M₀, X₁, hM₀, hX₁, hrectangle⟩ :=
    mrExists_fixedPower_small_selected_rectangle hr hrOne hxi hthetaMax
  have hrt : 0 < r * theta := mul_pos hr htheta
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / (r * theta))))
  refine ⟨theta, htheta, hthetaMax', M₀, max X₁ X₂, hM₀,
    hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens J hupper
    I A hA hlower hAupper H hH s f hmul hbound hnonpret t ht
  by_cases hempty : mrPrimeSubblock H A s = ∅
  · simp [hempty, logarithmicDirichletPolynomial]
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have ha : 4 ≤ r * (theta * Real.log (X : ℝ)) := by
    have hh := (div_le_iff₀ hrt).1 (hX₂ X ((le_max_right _ _).trans hX))
    nlinarith
  obtain ⟨hsLower, hsUpper⟩ := mrPrimeSubblock_log_parameter_bounds hH hA
    (fun p hpA ↦ ha.trans (hlower p hpA)) hAupper hnonempty
  have hP := mrNarrowPrimeInterval_lower_ge_four hsLower
  have hPQ := mrNarrowPrimeInterval_order_of_nonempty (by linarith : 0 < H) hA hnonempty
  have hQP := mrNarrowPrimeInterval_dyadic_width hH s
  have hQ : ((mrNarrowPrimeInterval H s).2 : ℝ) ≤
      Real.exp (theta * Real.log (X : ℝ) + 1) :=
    (mrNarrowPrimeInterval_upper_le_exp_shift (by linarith : 1 ≤ H) s).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hh := hrectangle hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq hbudget
    hmertens J hupper I A hA hlower hAupper hP hPQ hQP hQ hmul hbound hnonpret
    (-t) (by simpa only [abs_neg] using ht)
  simp only [neg_neg] at hh
  rw [norm_mul]
  calc
    _ ≤ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
        (mrFinitePrimeLineCoefficient f) t‖ * (xi * theta) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by ring

end

end Erdos67b

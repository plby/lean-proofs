import ErdosProblems.Erdos67b.MRFixedPowerAuxiliaryEnergy
import ErdosProblems.Erdos67b.MRSelectedNoSmallEnergy

/-! # Full exceptional energy for the actual scheduled typical polynomial -/

open Filter MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrExists_noSmall_typical_energy_small
    {eta p₁ q₁ epsilon : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hsourceBudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) ∧
        Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q₁ (J + 1) ∧
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
        (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2),
          (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J).indicator
          (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t) ≤
            epsilon := by
  let H := max (4 : ℝ) (24576 * (1 + Real.pi) / epsilon)
  have hH : 4 ≤ H := le_max_left _ _
  have hHpos : 0 < H := by linarith
  have hHlarge : 24576 * (1 + Real.pi) / epsilon ≤ H := le_max_right _ _
  obtain ⟨r, thetaMax, hr, hrHalf, hthetaMax, hmissing⟩ :=
    mrExists_fixedPower_missing_energy_small (by positivity : 0 < epsilon / 8)
  let xi := epsilon / (128 * H ^ 2)
  have hxi : 0 < xi := by dsimp [xi]; positivity
  obtain ⟨theta, htheta, hthetaMax', hthetaEta, M₀, X₁, hM₀, hX₁, hproducts⟩ :=
    mrExists_selected_noSmall_product_energy_small heta0 heta1 hp hq hpq hlogq
      hsourceBudget hmertens hr (by linarith : r ≤ 1) hxi hthetaMax
  have hthetaOne : theta ≤ 1 := by linarith
  obtain ⟨X₂, _, hmissing⟩ := hmissing theta htheta hthetaMax'
  obtain ⟨X₃, hgeometry⟩ := eventually_atTop.1 (mrEventually_fixedPower_auxiliary_scale
    hr htheta hHpos (by positivity : 0 < epsilon / (4096 * (1 + Real.pi))))
  refine ⟨M₀, max X₁ (max X₂ X₃), hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX
  obtain ⟨J, hJ, hupper, hnext, hproducts⟩ := hproducts hM ((le_max_left _ _).trans hX)
  refine ⟨J, hJ, hupper, hnext, ?_⟩
  intro f hmul hbound hnonpret
  obtain ⟨hXtwo, hlog, _, hgap, hcountScale, hendpoint⟩ :=
    hgeometry X (((le_max_right _ _).trans (le_max_right _ _)).trans hX)
  have hXpos : 0 < X := by omega
  have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
  let I := mrFixedPowerAuxiliaryInterval r theta X
  let V := mrFixedPowerAuxiliarySubblocks H r theta X
  let E := mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J
  let e : ℕ → ℝ := fun s ↦
    ∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2), E.indicator
      (fun t ↦ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H (primesInBlock I) s)
          (mrFinitePrimeLineCoefficient f) t *
        logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
            (mrNarrowPrimeInterval H s) X)
          (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t
  have he : ∀ s ∈ V, (Real.log (X : ℝ)) ^ 2 * e s ≤ xi := by
    intro s _
    exact hproducts I (fun p hp ↦ (mem_primesInBlock_mrLogPrimeInterval_bounds hp).1)
      (fun p hp ↦ (mem_primesInBlock_mrLogPrimeInterval_bounds hp).2)
      (by linarith : 2 ≤ H) s hmul hbound hnonpret
  have hcard := mrFixedPowerAuxiliary_card_le (r := r) hHpos.le hthetaOne
    (by linarith : 0 ≤ Real.log (X : ℝ)) hcountScale
  have hsum := mrSelectedProduct_card_sum_le V e hHpos.le (by linarith) hxi.le hcard he
  have hmain : 8 * (V.card : ℝ) * (∑ s ∈ V, e s) ≤ epsilon / 4 := by
    have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
    have heq : 8 * (4 * H ^ 2 * xi) = epsilon / 4 := by
      dsimp [xi]
      field_simp
      norm_num
    rw [heq] at hh
    simpa only [mul_assoc] using hh
  have hdisj := mrAuxiliaryInterval_disjoint_scheduled (b := theta * Real.log (X : ℝ))
    heta1 hp hq
    (by linarith : p₁ ≤ q₁) hlogq hsourceBudget hupper hgap
  have hE : MeasurableSet E := measurableSet_mrArithmeticNoSmall eta p₁ q₁ f J
  have hT : 0 ≤ (X : ℝ) / 2 := by positivity
  have hfull := mrFixedPowerAuxiliary_energy_le (mrScheduledBlocks p₁ q₁ J) r theta hH hXpos
    (fun B hB _ ↦ hdisj B hB) hmul hbound hE hT
  have htau : (X : ℝ) / 2 / X + 1 ≤ 2 := by field_simp; linarith
  have herror := mrFixedPowerAuxiliary_scalar_error_le hHpos hepsilon hHlarge
    (by positivity : 0 ≤ 1 / (X : ℝ) + Real.exp (-r * (theta * Real.log (X : ℝ))))
    hendpoint (by positivity : 0 ≤ (X : ℝ) / 2 / X + 1) htau
  have hmiss := hmissing X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
    (mrScheduledBlocks p₁ q₁ J) hbound hT
  have hmissSmall : 2 * (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2),
      ‖mrAuxiliaryMissingPolynomial (mrScheduledBlocks p₁ q₁ J) I f X t‖ ^ 2) ≤
        epsilon / 2 := by
    have hh := mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ epsilon / 8)
    linarith
  change _ ≤ 8 * (V.card : ℝ) * (∑ s ∈ V, e s) + _ + _ at hfull
  have herror' : 256 * (1 + Real.pi) * ((X : ℝ) / 2 / X + 1) *
      (6 / H + 1 / X + Real.exp (-r * (theta * Real.log (X : ℝ)))) ≤ epsilon / 4 := by
    simpa only [add_assoc] using herror
  linarith

end

end Erdos67b

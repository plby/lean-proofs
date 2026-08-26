import ErdosProblems.Erdos67b.MRCofactorSelectedPaidProduct
import ErdosProblems.Erdos67b.MRSelectedSubblockScale
import ErdosProblems.Erdos67b.MRSelectedPaidSampleScalar

/-! # Sampled energy of the actual selected narrow prime-cofactor product -/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_selected_paid_sample_energy
    {r E thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hE : 0 < E) (hthetaMax : 0 < thetaMax) :
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
      ∀ S : Finset ℝ,
        (∀ u ∈ S, ∀ t ∈ S, u ≠ t → 1 ≤ |u - t|) →
        (∀ t ∈ S, |t| ≤ (X : ℝ) / 2) →
        (∑ t ∈ S, ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
            (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
              (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ^ 2) ≤
          mrSelectedPaidPrimeEnergyBudget r theta E X S.card := by
  classical
  obtain ⟨theta, htheta, hthetaMax', M₀, X₁, hM₀, hX₁, hpaid⟩ :=
    mrExists_selected_cutoff_paid_product hr hrOne hE hthetaMax
  let R := mrSelectedPowerOrder r theta
  let alpha := r * theta
  have halpha : 0 < alpha := mul_pos hr htheta
  have hR : 2 ≤ R := mrSelectedPowerOrder_ge_two r theta
  have hheight : 2 * (2 / alpha) ≤ (R : ℝ) := by
    have hh := mrSelectedPowerOrder_ge_height r theta
    change 4 / alpha ≤ (R : ℝ) at hh
    convert hh using 1
    ring
  obtain ⟨V₀, _hV₀, hprimeEnergy⟩ :=
    mrExists_sparsePrime_normalized_energy_bound R hR hheight
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (mrEventually_selected_subblock_scale halpha V₀)
  refine ⟨theta, htheta, hthetaMax', M₀, max X₁ X₂, hM₀,
    hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hsourceBudget hmertens J hupper
    I A hA hlower hAupper H hH s f hmul hbound hnonpret S hsep hwindow
  obtain ⟨hXtwo, hlarge, hVscale⟩ := hX₂ X ((le_max_right _ _).trans hX)
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  by_cases hempty : mrPrimeSubblock H A s = ∅
  · simp only [hempty, logarithmicDirichletPolynomial, Finset.sum_empty, zero_mul,
      norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    exact mrSelectedPaidPrimeEnergyBudget_nonneg hr htheta hE.le hXone.le S.card
  have hne := Finset.nonempty_iff_ne_empty.2 hempty
  obtain ⟨hlogScale, hpowerScale, hheightScale⟩ := mrSelectedSubblock_power_scale hH halpha
    hXone hlarge hA (by simpa only [alpha, mul_assoc] using hlower) hne
  let V := Real.exp ((s : ℝ) / H)
  have hV : V₀ ≤ V := hVscale.trans hpowerScale
  have hblockPrime : ∀ p ∈ mrPrimeSubblock H A s, p.Prime :=
    fun p hpA ↦ hA p (mrPrimeSubblock_subset H A s hpA)
  have hblock : ∀ p ∈ mrPrimeSubblock H A s, (p : ℝ) ∈ Set.Icc V (2 * V) :=
    fun p hpA ↦ mrSelectedSubblock_real_dyadic hH hA hpA
  have hdiam : ∀ u ∈ S, ∀ t ∈ S, |t - u| ≤ V ^ (2 / alpha) := by
    intro u hu t ht
    have hab : |t - u| ≤ |t| + |u| := by simpa using abs_sub_le t 0 u
    have hh : |t - u| ≤ (X : ℝ) := by linarith [hwindow t ht, hwindow u hu]
    exact hh.trans hheightScale
  have hprime := hprimeEnergy V hV (mrPrimeSubblock H A s) hblockPrime hblock S hsep hdiam
    f (fun p hpA ↦ hbound p (hblockPrime p hpA).pos)
  have hpoint (t : ℝ) (ht : t ∈ S) :=
    hpaid hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq hsourceBudget hmertens J hupper
      I A hA hlower hAupper hH s hmul hbound hnonpret t (hwindow t ht)
  have hsum := mrSum_normSquare_le_of_cutoff_paid S
    (fun t ↦ logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
      (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial
        (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
          (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t)
    (fun t ↦ logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
      (mrFinitePrimeLineCoefficient f) t)
    htheta hE.le hpoint hprime
  apply hsum.trans
  apply mrSelectedPaid_primeBudget_le hr htheta hE.le hXone hpowerScale
  simpa only [V, Real.log_exp, alpha] using hlogScale

end

end Erdos67b

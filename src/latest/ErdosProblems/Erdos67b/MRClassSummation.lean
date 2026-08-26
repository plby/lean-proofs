import ErdosProblems.Erdos67b.MRPrimeSquareEnergy

/-!
# Summing the first-small frequency classes

All classes concern one fixed typical polynomial. The explicit finite
budgets are summed before isolating the no-small-block frequency energy.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

theorem mrSum_Icc_inv_sq_le_two (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hsets : Finset.Ioo 0 (J + 1) = Finset.Icc 1 J := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  have hh := sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1)
  simpa only [hsets, Nat.cast_zero, zero_add, div_one] using hh

theorem mrLogBlockResolution_eq_sq_mul_first (eta p₁ q₁ : ℝ) (j : ℕ) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) =
      (j : ℝ) ^ 2 * mrLogBlockResolution eta p₁ q₁ 1 := by
  unfold mrLogBlockResolution
  norm_num

theorem mrSum_inv_resolution_le (eta p₁ q₁ : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, 1 / mrLogBlockResolution eta p₁ q₁ (j : ℝ)) ≤
      2 / mrLogBlockResolution eta p₁ q₁ 1 := by
  have hH0 : 0 < mrLogBlockResolution eta p₁ q₁ 1 := by
    unfold mrLogBlockResolution
    positivity
  calc
    _ = (1 / mrLogBlockResolution eta p₁ q₁ 1) * ∑ j ∈ Finset.Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mrLogBlockResolution_eq_sq_mul_first, one_div, mul_inv_rev]
    _ ≤ (1 / mrLogBlockResolution eta p₁ q₁ 1) * 2 :=
      mul_le_mul_of_nonneg_left (mrSum_Icc_inv_sq_le_two J) (by positivity)
    _ = _ := by ring

theorem mrLogScheduleLower_ge_sq_mul
    {p₁ q₁ : ℝ} (hp : 0 ≤ p₁) (hq : 1 ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ 2 * p₁ ≤ mrLogScheduleLower p₁ q₁ j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpow : (j : ℝ) ^ 2 ≤ (j : ℝ) ^ (4 * j) := pow_le_pow_right₀ hjr (by omega)
  have hqpow : (1 : ℝ) ≤ q₁ ^ (j - 1) := one_le_pow₀ hq
  have hweight : (j : ℝ) ^ 2 ≤ mrLogScheduleWeight q₁ j := by
    unfold mrLogScheduleWeight
    nlinarith [show 0 ≤ (j : ℝ) ^ (4 * j) by positivity]
  exact mul_le_mul_of_nonneg_right hweight hp

theorem mrLogScheduleLower_exp_decay
    {p₁ q₁ : ℝ} (hp : 1 ≤ p₁) (hq : 1 ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ 2 * Real.exp (-mrLogScheduleLower p₁ q₁ j) ≤ Real.exp (-p₁) := by
  have hlower := mrLogScheduleLower_ge_sq_mul (by linarith : 0 ≤ p₁) hq hj
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsq : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hjr
  have hgap : (j : ℝ) ^ 2 ≤ Real.exp (mrLogScheduleLower p₁ q₁ j - p₁) := by
    have hh := Real.add_one_le_exp (mrLogScheduleLower p₁ q₁ j - p₁)
    nlinarith
  calc
    _ ≤ Real.exp (mrLogScheduleLower p₁ q₁ j - p₁) * Real.exp (-mrLogScheduleLower p₁ q₁ j) :=
      mul_le_mul_of_nonneg_right hgap (Real.exp_pos _).le
    _ = Real.exp (-p₁) := by rw [← Real.exp_add]; congr 1; ring

theorem mrSum_exp_neg_lower_le
    {p₁ q₁ : ℝ} (hp : 1 ≤ p₁) (hq : 1 ≤ q₁) (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, Real.exp (-mrLogScheduleLower p₁ q₁ j)) ≤ 2 * Real.exp (-p₁) := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 J, Real.exp (-p₁) * ((j : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hh : Real.exp (-mrLogScheduleLower p₁ q₁ j) ≤ Real.exp (-p₁) / (j : ℝ) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hj0)).mpr
        have hb := mrLogScheduleLower_exp_decay hp hq hj1
        nlinarith
      simpa only [div_eq_mul_inv] using hh
    _ = Real.exp (-p₁) * ∑ j ∈ Finset.Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-p₁) * 2 := mul_le_mul_of_nonneg_left (mrSum_Icc_inv_sq_le_two J) (Real.exp_pos _).le
    _ = _ := by ring

theorem mrSum_higher_class_weight_le
    {p₁ q₁ : ℝ} (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (J : ℕ) :
    (∑ j ∈ Finset.Icc 2 J,
      1 / ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1)))) ≤ 2 * Real.exp (-p₁) := by
  have hsub : Finset.Icc 2 J ⊆ Finset.Icc 1 J := by
    intro j hj
    have hh := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 J, Real.exp (-p₁) * ((j : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj2 := (Finset.mem_Icc.mp hj).1
      have hprev : p₁ ≤ mrLogScheduleUpper q₁ (j - 1) :=
        hpq.trans (mrLogScheduleUpper_ge hq (by omega))
      have hexp : Real.exp (-mrLogScheduleUpper q₁ (j - 1)) ≤ Real.exp (-p₁) :=
        Real.exp_le_exp.mpr (by linarith)
      calc
        _ = Real.exp (-mrLogScheduleUpper q₁ (j - 1)) * ((j : ℝ) ^ 2)⁻¹ := by
          rw [one_div, mul_inv_rev, Real.exp_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ ∑ j ∈ Finset.Icc 1 J, Real.exp (-p₁) * ((j : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = Real.exp (-p₁) * ∑ j ∈ Finset.Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-p₁) * 2 := mul_le_mul_of_nonneg_left (mrSum_Icc_inv_sq_le_two J) (Real.exp_pos _).le
    _ = _ := by ring

theorem mrSum_class_error_terms_le
    {eta p₁ q₁ : ℝ} (hp : 1 ≤ p₁) (hq : 1 ≤ q₁) (J X : ℕ) :
    (∑ j ∈ Finset.Icc 1 J,
      (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / (X : ℝ) + Real.exp (-mrLogScheduleLower p₁ q₁ j))) ≤
      12 / mrLogBlockResolution eta p₁ q₁ 1 + J / (X : ℝ) + 2 * Real.exp (-p₁) := by
  have hresolution := mul_le_mul_of_nonneg_left (mrSum_inv_resolution_le eta p₁ q₁ J)
    (by norm_num : (0 : ℝ) ≤ 6)
  have hexp := mrSum_exp_neg_lower_le hp hq J
  have hsumres : (∑ j ∈ Finset.Icc 1 J, 6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ)) =
      6 * ∑ j ∈ Finset.Icc 1 J, 1 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumres]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  have hh := add_le_add (add_le_add hresolution (le_refl ((J : ℝ) * (1 / X)))) hexp
  calc
    _ ≤ 6 * (2 / mrLogBlockResolution eta p₁ q₁ 1) +
        (J : ℝ) * (1 / X) + 2 * Real.exp (-p₁) := hh
    _ = _ := by ring

theorem mrSum_Icc_split_first {J : ℕ} (hJ : 1 ≤ J) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 J, g j) = g 1 + ∑ j ∈ Finset.Icc 2 J, g j := by
  have hsets : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsets, Finset.sum_insert (by simp)]

theorem mrFinite_firstClass_sum_le
    {J : ℕ} (hJ : 1 ≤ J) (F a b : ℕ → ℝ) (A : ℝ)
    (hfirst : F 1 ≤ A + b 1)
    (hnext : ∀ j ∈ Finset.Icc 2 J, F j ≤ a j + b j) :
    (∑ j ∈ Finset.Icc 1 J, F j) ≤ A + (∑ j ∈ Finset.Icc 2 J, a j) + ∑ j ∈ Finset.Icc 1 J, b j := by
  rw [mrSum_Icc_split_first hJ F, mrSum_Icc_split_first hJ b]
  have hsum := Finset.sum_le_sum hnext
  rw [Finset.sum_add_distrib] at hsum
  linarith

noncomputable section

/-- The fully explicit sum of the first-small class budgets. -/
def mrFirstSmallEnergyBudget (eta p₁ q₁ : ℝ) (X J : ℕ) (T : ℝ) : ℝ :=
  2048 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
      Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁) +
    8192 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) * Real.exp (-p₁) +
    128 * (1 + Real.pi) * (T / X + 1) *
      (12 / mrLogBlockResolution eta p₁ q₁ 1 + (J : ℝ) / X + 2 * Real.exp (-p₁))

theorem mrAllFirstSmall_energy_le
    (J : ℕ) (hJ : 1 ≤ J) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∑ j ∈ Finset.Icc 1 J, ∫ t in -T..T,
      (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator
        (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t) ≤
      mrFirstSmallEnergyBudget eta p₁ q₁ X J T := by
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  let C : ℝ := (1 + Real.pi) * (T / X + 1)
  let A : ℝ := 2048 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
    Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁)
  let a (j : ℕ) : ℝ := 4096 * Real.exp 13 * C /
    ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1)))
  let b (j : ℕ) : ℝ := 128 * C *
    (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X + Real.exp (-mrLogScheduleLower p₁ q₁ j))
  let F (j : ℕ) : ℝ := ∫ t in -T..T,
    (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator
      (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hfirst : F 1 ≤ A + b 1 := by
    have hh := mrArithmetic_typical_firstClass_energy_le J hJ heta0 heta1 hp hqexp hpq hbudget
      hmul hbound hX hscale hT
    have hlower : mrLogScheduleLower p₁ q₁ 1 = p₁ := by norm_num [mrLogScheduleLower, mrLogScheduleWeight]
    dsimp only [F, A, b, C]
    simpa only [Nat.cast_one, hlower, mul_assoc] using hh
  have hnext : ∀ j ∈ Finset.Icc 2 J, F j ≤ a j + b j := by
    intro j hj
    have hh := mrArithmetic_typical_firstSmallClass_energy_le J heta0 heta1 hp hqexp hpq hbudget
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hmul hbound hX hT
    dsimp only [F, a, b, C]
    simpa only [mul_assoc] using hh
  have hsum := mrFinite_firstClass_sum_le hJ F a b A hfirst hnext
  have ha : (∑ j ∈ Finset.Icc 2 J, a j) ≤ 8192 * Real.exp 13 * C * Real.exp (-p₁) := by
    calc
      _ = (4096 * Real.exp 13 * C) * ∑ j ∈ Finset.Icc 2 J,
          1 / ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [a]
        ring
      _ ≤ (4096 * Real.exp 13 * C) * (2 * Real.exp (-p₁)) :=
        mul_le_mul_of_nonneg_left (mrSum_higher_class_weight_le hq hpq J) (by positivity)
      _ = _ := by ring
  have hb : (∑ j ∈ Finset.Icc 1 J, b j) ≤ 128 * C *
      (12 / mrLogBlockResolution eta p₁ q₁ 1 + (J : ℝ) / X + 2 * Real.exp (-p₁)) := by
    dsimp only [b]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (mrSum_class_error_terms_le (by linarith : 1 ≤ p₁) hq J X) (by positivity)
  calc
    _ ≤ A + (∑ j ∈ Finset.Icc 2 J, a j) + ∑ j ∈ Finset.Icc 1 J, b j := hsum
    _ ≤ A + 8192 * Real.exp 13 * C * Real.exp (-p₁) +
        128 * C * (12 / mrLogBlockResolution eta p₁ q₁ 1 + (J : ℝ) / X + 2 * Real.exp (-p₁)) :=
      add_le_add (add_le_add le_rfl ha) hb
    _ = _ := by unfold mrFirstSmallEnergyBudget; dsimp only [A, C]; ring

theorem mrArithmetic_firstSmall_zero (eta p₁ q₁ : ℝ) (f : ℕ → ℂ) :
    disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 0 = ∅ := by
  rw [disjointed_zero]
  simp only [mrArithmeticSmallFrequencySet, mrScheduledSmallFrequencySet, mrSmallPrimeBlockSet,
    ↓reduceIte]

/-- The first-small contribution is fully paid. Only the actual
no-small-block energy of the same typical polynomial remains. -/
theorem mrTypical_energy_le_firstSmallBudget_add_noSmall
    (J : ℕ) (hJ : 1 ≤ J) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) ≤
      mrFirstSmallEnergyBudget eta p₁ q₁ X J T +
        ∫ t in -T..T, (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J).indicator
          (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t := by
  let g : ℝ → ℝ := fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2
  have hg : Continuous g := (continuous_logarithmicDirichletPolynomial _ _).norm.pow 2
  have hint : IntervalIntegrable g volume (-T) T := hg.intervalIntegrable _ _
  have hsmall (j : ℕ) : MeasurableSet (mrArithmeticSmallFrequencySet eta p₁ q₁ f j) :=
    measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _ j
  have hsplit := intervalIntegral_eq_firstSmall_add_noSmall hsmall J hint
  have hsets : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : (∫ t in -T..T, (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 0).indicator g t) = 0 := by
    rw [mrArithmetic_firstSmall_zero]
    simp only [Set.indicator_empty, intervalIntegral.integral_zero]
  rw [hsets, Finset.sum_insert (by simp), hzero, zero_add] at hsplit
  calc
    _ = (∑ j ∈ Finset.Icc 1 J, ∫ t in -T..T,
        (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator g t) +
        ∫ t in -T..T, (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J).indicator g t := hsplit
    _ ≤ _ := add_le_add (mrAllFirstSmall_energy_le J hJ heta0 heta1 hp hqexp hpq hbudget
      hmul hbound hX hscale hT) le_rfl

end

end Erdos67b

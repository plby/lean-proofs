import ErdosProblems.Erdos67b.MRExceptionalCountBounds

/-!
# Large additional prime values

An explicit cardinality estimate at an inverse-logarithmic threshold,
derived from the already proved finite sampled moments. This is not the
sparse prime energy estimate.
-/

namespace Erdos67b

noncomputable section

def mrLargePrimeCountConstant : ℝ := 44 * Real.exp 1 * (4 + 2 * Real.pi)

theorem mrMomentCostBase_log_le_log_scale {R : ℝ} (hR : 1 ≤ R)
    (hlogR : 1 ≤ Real.log R) : Real.log (mrMomentCostBase R) ≤ 4 * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hB : mrMomentCostBase R ≤ 4 * Real.exp 1 * R := by
    unfold mrMomentCostBase
    nlinarith [Real.exp_pos 1]
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ Real.log (4 * Real.exp 1 * R) :=
      Real.log_le_log (by have hh := mrMomentCostBase_one_le hR; linarith) hB
    _ = 2 * Real.log 2 + 1 + Real.log R := by
      rw [Real.log_mul (by positivity) hR0.ne', Real.log_mul (by norm_num) (by positivity),
        Real.log_exp, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    _ ≤ _ := by linarith

theorem mrOptimizedPrimeSampleBudget_le_log_threshold
    {T v R a : ℝ} (hT : 1 ≤ T) (hv : 1 ≤ v) (hR : 1 ≤ R)
    (hvR : v ≤ R) (hTR : Real.log T ≤ R) (hlogR : 1 ≤ Real.log R) (ha : 0 ≤ a) :
    mrOptimizedPrimeSampleBudget T v (a * Real.log R / v) ≤
      mrLargePrimeCountConstant * R ^ 2 *
        Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R) := by
  let alpha := a * Real.log R / v
  let sigma := Real.log (mrMomentCostBase R) / v
  have hv0 : 0 < v := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hL : 0 ≤ Real.log R := by linarith
  have hB0 : 0 ≤ Real.log (mrMomentCostBase R) :=
    Real.log_nonneg (mrMomentCostBase_one_le hR)
  have hB : mrMomentCostBase R ≤ 4 * Real.exp 1 * R := by
    unfold mrMomentCostBase
    nlinarith [Real.exp_pos 1]
  have hcost : Real.log (mrMomentCostBase R) ≤ sigma * v := by
    dsimp only [sigma]
    rw [div_mul_cancel₀ _ hv0.ne']
  have hmain := mrOptimizedPrimeSampleBudget_le_uniform (alpha := alpha) hT hv hR hTR hcost
  have hlinear : 3 + 4 * R + 4 * v ≤ 11 * R := by linarith
  have hpref : (4 + 2 * Real.pi) * (3 + 4 * R + 4 * v) * mrMomentCostBase R ≤
      mrLargePrimeCountConstant * R ^ 2 := by
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 4 + 2 * Real.pi by positivity)) hB
      (by have hh := mrMomentCostBase_one_le hR; linarith) (by positivity)
    calc
      _ ≤ ((4 + 2 * Real.pi) * (11 * R)) * (4 * Real.exp 1 * R) := hh
      _ = _ := by unfold mrLargePrimeCountConstant; ring
  have hexponent : 2 * alpha * v + (2 * alpha + sigma) * Real.log T ≤
      2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R := by
    have hcoef : 0 ≤ 2 * alpha + sigma := by dsimp only [alpha, sigma]; positivity
    have htime := mul_le_mul_of_nonneg_left hTR hcoef
    have hlogB := mrMomentCostBase_log_le_log_scale hR hlogR
    have hquot := div_le_div_of_nonneg_right hlogB hv0.le
    have hprod := mul_le_mul_of_nonneg_right hquot hR0
    have halpha : alpha * v = a * Real.log R := by
      dsimp only [alpha]
      exact div_mul_cancel₀ _ hv0.ne'
    have heq : (2 * alpha + 4 * Real.log R / v) * R =
        (2 * a + 4) * (R / v) * Real.log R := by dsimp only [alpha]; ring
    change sigma * R ≤ 4 * Real.log R / v * R at hprod
    nlinarith
  calc
    _ ≤ ((4 + 2 * Real.pi) * (3 + 4 * R + 4 * v) * mrMomentCostBase R) *
        Real.exp (2 * alpha * v + (2 * alpha + sigma) * Real.log T) := by
      simpa only [Real.exp_add, mul_assoc] using hmain
    _ ≤ _ := mul_le_mul hpref (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
      (by unfold mrLargePrimeCountConstant; positivity)

theorem mrPrimeLine_large_log_values_card_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {L N : ℕ} (hN : 0 < N) {T v R a : ℝ}
    (hT : 1 ≤ T) (hv : 1 ≤ v) (hR : 1 ≤ R)
    (hvR : v ≤ R) (hTR : Real.log T ≤ R) (hlogR : 1 ≤ Real.log R) (ha : 0 ≤ a)
    (hL : Real.exp v ≤ L) (hNhi : (N : ℝ) ≤ Real.exp (v + 1))
    (hlo : ∀ p ∈ P, L ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hlarge : ∀ t ∈ S,
      Real.exp (-a * Real.log R) ≤ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖) :
    (S.card : ℝ) ≤ mrLargePrimeCountConstant * R ^ 2 *
      Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R) := by
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by
    have hh : (0 : ℝ) < L := (Real.exp_pos v).trans_le hL
    exact_mod_cast hh
  have hbase := mrPrimeLine_sampled_largeValues_card_le (k := ⌈Real.log T / v⌉₊)
    hP hL0 hN hlo hhi hbound S (by linarith) (Real.exp_pos _) hST hsep hlarge
  have hthreshold : Real.exp (-a * Real.log R) = Real.exp (-(a * Real.log R / v) * v) := by
    congr 1
    field_simp
  rw [hthreshold] at hbase
  have hopt := mrPrimeLineSampleBudget_ceil_le hN hT hv0
    (show 0 ≤ a * Real.log R / v by positivity) hL hNhi
  exact (hbase.trans hopt).trans (mrOptimizedPrimeSampleBudget_le_log_threshold
    hT hv hR hvR hTR hlogR ha)

theorem mrPrimeSubblock_large_log_values_card_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {H T R a : ℝ} (hH : 1 ≤ H) {r : ℕ}
    (hT : 1 ≤ T) (hv : 1 ≤ (r : ℝ) / H) (hR : 1 ≤ R)
    (hvR : (r : ℝ) / H ≤ R) (hTR : Real.log T ≤ R)
    (hlogR : 1 ≤ Real.log R) (ha : 0 ≤ a)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hlarge : ∀ t ∈ S,
      Real.exp (-a * Real.log R) ≤
        ‖logarithmicDirichletPolynomial (mrPrimeSubblock H P r) (mrFinitePrimeLineCoefficient f) t‖) :
    (S.card : ℝ) ≤ mrLargePrimeCountConstant * R ^ 2 *
      Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / ((r : ℝ) / H)) * Real.log R) := by
  have hH0 : 0 < H := by linarith
  exact mrPrimeLine_large_log_values_card_le
    (fun p hp ↦ hP p (mrPrimeSubblock_subset H P r hp))
    (mrNarrowPrimeInterval_upper_pos hH0 r) hT hv hR hvR hTR hlogR ha
    (Nat.le_ceil _) (mrNarrowPrimeInterval_upper_le_exp_shift hH r)
    (fun p hp ↦ (mrPrimeSubblock_integer_bounds hH0 hP hp).1)
    (fun p hp ↦ (mrPrimeSubblock_integer_bounds hH0 hP hp).2)
    hbound S hST hsep hlarge

theorem mrLargePrimeCountBudget_le_fixed_power
    {R v a delta : ℝ} (hR : 1 ≤ R) (hv : 0 < v) (ha : 0 ≤ a)
    (hdelta : 0 < delta) (hvlo : delta * R ≤ v) :
    mrLargePrimeCountConstant * R ^ 2 *
        Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R) ≤
      mrLargePrimeCountConstant *
        Real.exp ((2 + 2 * a + (2 * a + 4) / delta) * Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hratio : R / v ≤ 1 / delta := by
    apply (div_le_div_iff₀ hv hdelta).mpr
    nlinarith
  have hexp : Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R) ≤
      Real.exp ((2 * a + (2 * a + 4) / delta) * Real.log R) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ (2 * a + 4) * Real.log R by positivity)
    calc
      _ = 2 * a * Real.log R + (R / v) * ((2 * a + 4) * Real.log R) := by ring
      _ ≤ 2 * a * Real.log R + (1 / delta) * ((2 * a + 4) * Real.log R) := add_le_add le_rfl hh
      _ = _ := by ring
  calc
    _ ≤ mrLargePrimeCountConstant * R ^ 2 *
        Real.exp ((2 * a + (2 * a + 4) / delta) * Real.log R) :=
      mul_le_mul_of_nonneg_left hexp (by unfold mrLargePrimeCountConstant; positivity)
    _ = mrLargePrimeCountConstant * (Real.exp (2 * Real.log R) *
        Real.exp ((2 * a + (2 * a + 4) / delta) * Real.log R)) := by
      rw [show Real.exp (2 * Real.log R) = R ^ 2 by
        simpa only [Nat.cast_ofNat, Real.exp_log hR0] using Real.exp_nat_mul (Real.log R) 2]
      ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end

end Erdos67b

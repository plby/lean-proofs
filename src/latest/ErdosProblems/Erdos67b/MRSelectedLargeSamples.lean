import ErdosProblems.Erdos67b.MRLargePrimeSamples
import ErdosProblems.Erdos67b.MRSelectedSubblockScale

/-! # Polylogarithmic counts of actual large selected-prime samples -/

open Filter

namespace Erdos67b

noncomputable section

def mrSelectedLargeSampleOrder (r theta a : ℝ) : ℕ :=
  ⌈2 + 2 * a + (2 * a + 4) / (r * theta / 2)⌉₊

theorem mrLargePrimeCountConstant_pos : 0 < mrLargePrimeCountConstant := by
  unfold mrLargePrimeCountConstant
  positivity

theorem mrLargePrimeCountBudget_le_nat_power
    {R v a delta : ℝ} (hR : 1 ≤ R) (hv : 0 < v) (ha : 0 ≤ a)
    (hdelta : 0 < delta) (hvlo : delta * R ≤ v) :
    mrLargePrimeCountConstant * R ^ 2 *
        Real.exp (2 * a * Real.log R + (2 * a + 4) * (R / v) * Real.log R) ≤
      mrLargePrimeCountConstant * R ^ ⌈2 + 2 * a + (2 * a + 4) / delta⌉₊ := by
  apply (mrLargePrimeCountBudget_le_fixed_power hR hv ha hdelta hvlo).trans
  apply mul_le_mul_of_nonneg_left _ mrLargePrimeCountConstant_pos.le
  have hRpos : 0 < R := by linarith
  calc
    _ = R ^ (2 + 2 * a + (2 * a + 4) / delta) := by
      rw [Real.rpow_def_of_pos hRpos]
      congr 1
      ring
    _ ≤ R ^ ((⌈2 + 2 * a + (2 * a + 4) / delta⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR (Nat.le_ceil _)
    _ = _ := Real.rpow_natCast _ _

theorem mrSelectedSubblock_large_values_card_le
    {r theta X a H : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    (hthetaOne : theta ≤ 1) (hX : 1 < X) (hlog : 1 ≤ Real.log X)
    (hloglog : 1 ≤ Real.log (Real.log X)) (ha : 0 ≤ a) (hH : 2 ≤ H)
    (hscale : 2 ≤ (r * theta) * Real.log X)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hlower : ∀ p ∈ A, r * (theta * Real.log X) ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log X)
    (s : ℕ) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) (hwindow : ∀ t ∈ S, |t| ≤ X / 2)
    (hsep : ∀ u ∈ S, ∀ t ∈ S, u ≠ t → 1 ≤ |u - t|)
    (hlarge : ∀ t ∈ S, Real.exp (-a * Real.log (Real.log X)) ≤
      ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
        (mrFinitePrimeLineCoefficient f) t‖) :
    (S.card : ℝ) ≤ mrLargePrimeCountConstant *
      (Real.log X) ^ mrSelectedLargeSampleOrder r theta a := by
  classical
  by_cases hne : (mrPrimeSubblock H A s).Nonempty
  · have hscale' := (mrSelectedSubblock_power_scale hH (mul_pos hr htheta)
        hX hscale hA (by simpa only [mul_assoc] using hlower) hne).1
    have hv : 1 ≤ (s : ℝ) / H := by nlinarith
    obtain ⟨p, hp⟩ := hne
    have hpA := mrPrimeSubblock_subset H A s hp
    have hpBounds := mrPrimeSubblock_real_bounds (by linarith : 0 < H) hA hp
    have hlogp := Real.log_le_log (Real.exp_pos _) hpBounds.1
    rw [Real.log_exp] at hlogp
    have hvhi : (s : ℝ) / H ≤ Real.log X := by
      have hh := mul_le_mul_of_nonneg_right hthetaOne (by linarith : 0 ≤ Real.log X)
      nlinarith [hupper p hpA]
    have hcount := mrPrimeSubblock_large_log_values_card_le hA (by linarith : 1 ≤ H)
      hX.le hv hlog hvhi le_rfl hloglog ha hbound S
      (fun t ht ↦ (hwindow t ht).trans (by linarith)) hsep hlarge
    exact hcount.trans (mrLargePrimeCountBudget_le_nat_power hlog (by linarith) ha
      (by positivity : 0 < r * theta / 2) hscale')
  · have hzero : mrPrimeSubblock H A s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hh := hlarge t ht
      simp only [hzero, logarithmicDirichletPolynomial, Finset.sum_empty, norm_zero] at hh
      exact (not_le_of_gt (Real.exp_pos _)) hh
    rw [hS, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg mrLargePrimeCountConstant_pos.le (pow_nonneg (by linarith) _)

theorem mrEventually_selected_large_sample_scale {r theta : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ X ∧ 1 ≤ Real.log (X : ℝ) ∧ 1 ≤ Real.log (Real.log (X : ℝ)) ∧
        2 ≤ (r * theta) * Real.log (X : ℝ) := by
  filter_upwards [mrEventually_selected_subblock_scale (mul_pos hr htheta) 1,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
    (Real.tendsto_log_atTop.comp EulerSubpower.tendsto_log_nat_atTop).eventually
      (eventually_ge_atTop 1)] with X hscale hlog hloglog
  exact ⟨hscale.1, hlog, hloglog, hscale.2.1⟩

end

end Erdos67b

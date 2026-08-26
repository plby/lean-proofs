import ErdosProblems.Erdos67b.MRCofactorSelectedSmallMean

/-! # Uniform real scales of nonempty fixed-power selected subblocks -/

open Filter

namespace Erdos67b

noncomputable section

theorem mrSelectedSubblock_log_scale_lower {H c : ℝ} (hH : 2 ≤ H)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (hlower : ∀ p ∈ A, c ≤ Real.log (p : ℝ))
    {s : ℕ} (hne : (mrPrimeSubblock H A s).Nonempty) :
    c - 1 ≤ (s : ℝ) / H := by
  obtain ⟨p, hp⟩ := hne
  have hpA := mrPrimeSubblock_subset H A s hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (hA p hpA).pos
  have hbounds := mrPrimeSubblock_real_bounds (by linarith : 0 < H) hA hp
  have hh := Real.log_le_log hpPos hbounds.2
  rw [Real.log_exp] at hh
  have hinv : 1 / H ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) hH
  push_cast at hh
  rw [add_div] at hh
  linarith [hlower p hpA]

theorem mrSelectedSubblock_real_dyadic {H : ℝ} (hH : 2 ≤ H)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {s p : ℕ}
    (hp : p ∈ mrPrimeSubblock H A s) :
    (p : ℝ) ∈ Set.Icc (Real.exp ((s : ℝ) / H)) (2 * Real.exp ((s : ℝ) / H)) := by
  have hb := mrPrimeSubblock_real_bounds (by linarith : 0 < H) hA hp
  refine ⟨hb.1, hb.2.trans ?_⟩
  push_cast
  rw [add_div, Real.exp_add]
  have hh := mul_le_mul_of_nonneg_left (exp_inv_resolution_le_two hH)
    (Real.exp_nonneg ((s : ℝ) / H))
  simpa only [mul_comm] using hh

theorem mrSelectedSubblock_power_scale {H alpha X : ℝ} (hH : 2 ≤ H)
    (halpha : 0 < alpha) (hX : 1 < X) (hlarge : 2 ≤ alpha * Real.log X)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hlower : ∀ p ∈ A, alpha * Real.log X ≤ Real.log (p : ℝ))
    {s : ℕ} (hne : (mrPrimeSubblock H A s).Nonempty) :
    (alpha / 2) * Real.log X ≤ (s : ℝ) / H ∧
    X ^ (alpha / 2) ≤ Real.exp ((s : ℝ) / H) ∧
    X ≤ (Real.exp ((s : ℝ) / H)) ^ (2 / alpha) := by
  have hh := mrSelectedSubblock_log_scale_lower hH hA hlower hne
  have hlog : (alpha / 2) * Real.log X ≤ (s : ℝ) / H := by nlinarith
  have hXpos : 0 < X := by linarith
  have hpower : X ^ (alpha / 2) ≤ Real.exp ((s : ℝ) / H) := by
    rw [Real.rpow_def_of_pos hXpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  refine ⟨hlog, hpower, ?_⟩
  have hexp : Real.log X ≤ ((s : ℝ) / H) * (2 / alpha) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ halpha).2
    nlinarith
  calc
    X = Real.exp (Real.log X) := (Real.exp_log hXpos).symm
    _ ≤ Real.exp (((s : ℝ) / H) * (2 / alpha)) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

theorem mrEventually_selected_subblock_scale {alpha : ℝ} (halpha : 0 < alpha) (P₀ : ℝ) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ X ∧ 2 ≤ alpha * Real.log (X : ℝ) ∧ P₀ ≤ (X : ℝ) ^ (alpha / 2) := by
  filter_upwards [eventually_ge_atTop 2,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (2 / alpha)),
    ((tendsto_rpow_atTop (by positivity : 0 < alpha / 2)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop P₀)] with X hX hlog hpower
  refine ⟨hX, ?_, hpower⟩
  have hh := (div_le_iff₀ halpha).1 hlog
  nlinarith

end

end Erdos67b

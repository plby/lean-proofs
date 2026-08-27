/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceTupleConcentration

/-! # Uniform coarse density and subpower normalization bounds -/

namespace Erdos4b.FGKMT

open Filter
open scoped BigOperators

theorem residueSieveDensity_le_one {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    residueSieveDensity S ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpR.le)
  · intro p _hp
    exact sub_le_self _ (by positivity)

theorem residueSieveDensity_inv_le_partialEuler {S : Finset ℕ} {x : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hupper : ∀ p ∈ S, p ≤ x) :
    (residueSieveDensity S)⁻¹ ≤ partial_euler_product x := by
  rw [residueSieveDensity, ← Finset.prod_inv_distrib, partial_euler_product]
  simp only [one_div]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(hS p hp).one_le, hupper p hp⟩, hS p hp⟩
  · intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    exact (inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR))).le
  · intro p hp _hnot
    have hpR : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    apply (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR))).mpr
    exact sub_le_self _ (inv_nonneg.mpr (by linarith))

theorem eventually_residueSieveDensity_inv_le_log_sq :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
        (residueSieveDensity S)⁻¹ ≤ Real.log (x : ℝ) ^ 2 := by
  obtain ⟨C, _hC, hM⟩ := weak_mertens_third_upper_all
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlog.eventually (eventually_ge_atTop C)] with x hx hLC
  intro S hS hupper
  have hL0 := Real.log_natCast_nonneg x
  have hM' : partial_euler_product x ≤ C * Real.log (x : ℝ) := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_nonneg (zero_le_one.trans (partial_euler_trivial_lower_bound (n := x)))]
      using hM (x : ℝ) (by exact_mod_cast hx)
  exact (residueSieveDensity_inv_le_partialEuler hS hupper).trans
    (hM'.trans (by nlinarith [mul_le_mul_of_nonneg_right hLC hL0]))

theorem eventually_residueSieveDensity_inv_pow_le_rpow {d : ℝ} (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ k : ℕ, (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        (residueSieveDensity S ^ k)⁻¹ ≤ (x : ℝ) ^ d := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_residueSieveDensity_inv_le_log_sq,
    eventually_uniform_squareDimension_loss (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1),
    eventually_exp_mul_sqrtLog_le_rpow 1 hd,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hσinv hdim hexp hL hx
  intro S hS hupper k hk
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  by_cases hk0 : k = 0
  · subst k
    simpa only [pow_zero, inv_one] using Real.one_le_rpow hxR hd.le
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hlogL : Real.log (Real.log (x : ℝ)) ≤ dimensionLogLossScale x := by
    have hh := Real.log_le_log hLpos (show Real.log (x : ℝ) ≤ 1 + Real.log (x : ℝ) by linarith)
    unfold dimensionLogLossScale
    linarith
  have hscale0 := zero_le_one.trans (one_le_dimensionLogLossScale x)
  have hbudget : (k : ℝ) * (2 * Real.log (Real.log (x : ℝ))) ≤
      Real.sqrt (Real.log (x : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hlogL (by positivity : 0 ≤ 2 * (k : ℝ))
    have h2 := mul_le_mul_of_nonneg_right
      (show 2 * (k : ℝ) ≤ 2 * (k : ℝ) ^ 2 by nlinarith) hscale0
    have h3 := hdim k hk1 hk
    simp only [one_mul] at h3
    nlinarith
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  calc
    _ = ((residueSieveDensity S)⁻¹) ^ k := (inv_pow _ _).symm
    _ ≤ (Real.log (x : ℝ) ^ 2) ^ k :=
      pow_le_pow_left₀ (inv_nonneg.mpr hσ.le) (hσinv S hS hupper) k
    _ ≤ Real.exp (Real.sqrt (Real.log (x : ℝ))) := by
      apply (Real.log_le_iff_le_exp (pow_pos (sq_pos_of_pos hLpos) k)).mp
      rw [Real.log_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      exact hbudget
    _ ≤ _ := by simpa only [one_mul] using hexp

theorem eventually_residueSieveDensity_inv_square_pow_le_rpow {d : ℝ} (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ k : ℕ, (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        ((residueSieveDensity S ^ k) ^ 2)⁻¹ ≤ (x : ℝ) ^ d := by
  filter_upwards [eventually_residueSieveDensity_inv_pow_le_rpow
    (by positivity : 0 < d / 2)] with x hx
  intro S hS hupper k hk
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  calc
    _ = ((residueSieveDensity S ^ k)⁻¹) ^ 2 := (inv_pow _ _).symm
    _ ≤ ((x : ℝ) ^ (d / 2)) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (pow_nonneg hσ.le k)) (hx S hS hupper k hk) 2
    _ = _ := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg x)]
      congr 1
      norm_num

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueSieveDensity_inv_le_partialEuler
#print axioms Erdos4b.FGKMT.eventually_residueSieveDensity_inv_square_pow_le_rpow

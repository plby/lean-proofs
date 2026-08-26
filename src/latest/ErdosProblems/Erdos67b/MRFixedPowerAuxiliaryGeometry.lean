import ErdosProblems.Erdos67b.MRFixedPowerAuxiliaryDensity
import ErdosProblems.Erdos67b.MRAuxiliaryBlockSeparation
import ErdosProblems.Erdos67b.MRCofactorSelectedScheduledRectangle

/-! # Actual fixed-power auxiliary partition and simultaneous scale conditions -/

open Filter
open scoped Topology BigOperators

namespace Erdos67b

noncomputable section

def mrFixedPowerAuxiliarySubblocks (H r theta : ℝ) (X : ℕ) : Finset ℕ :=
  mrLogBlockIndices H (r * (theta * Real.log (X : ℝ))) (theta * Real.log (X : ℝ))

theorem mrFixedPowerAuxiliary_prime_partition (r theta H : ℝ) (X : ℕ) (hH : 0 ≤ H) :
    Set.PairwiseDisjoint (↑(mrFixedPowerAuxiliarySubblocks H r theta X) : Set ℕ)
      (mrPrimeSubblock H (primesInBlock (mrFixedPowerAuxiliaryInterval r theta X))) ∧
    (mrFixedPowerAuxiliarySubblocks H r theta X).biUnion
      (mrPrimeSubblock H (primesInBlock (mrFixedPowerAuxiliaryInterval r theta X))) =
        primesInBlock (mrFixedPowerAuxiliaryInterval r theta X) := by
  exact ⟨mrPrimeSubblock_pairwiseDisjoint _ _ _,
    mrPrimeSubblock_biUnion_eq hH _ (fun p hp ↦ mem_primesInBlock_mrLogPrimeInterval_bounds hp)⟩

theorem mrFixedPowerAuxiliary_card_le {r theta H : ℝ} {X : ℕ}
    (hH : 0 ≤ H) (htheta : theta ≤ 1) (hlog : 0 ≤ Real.log (X : ℝ))
    (hscale : 1 ≤ H * (theta * Real.log (X : ℝ))) :
    ((mrFixedPowerAuxiliarySubblocks H r theta X).card : ℝ) ≤ 2 * H * Real.log (X : ℝ) := by
  have hh := card_mrLogBlockIndices_le (p := r * (theta * Real.log (X : ℝ))) hscale
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right htheta hlog) (by positivity : 0 ≤ 2 * H)
  simpa only [one_mul, mul_assoc] using hmul

theorem mrFixedPowerAuxiliary_inv_lower_le (r theta : ℝ) (X : ℕ) :
    1 / ((mrFixedPowerAuxiliaryInterval r theta X).1 : ℝ) ≤
      Real.exp (-r * (theta * Real.log (X : ℝ))) := by
  rw [neg_mul, Real.exp_neg, one_div]
  exact inv_anti₀ (Real.exp_pos _) (Nat.le_ceil _)

theorem mrEventually_fixedPower_auxiliary_scale {r theta H epsilon : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (hH : 0 < H) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ X ∧ 1 ≤ Real.log (X : ℝ) ∧ 2 ≤ r * (theta * Real.log (X : ℝ)) ∧
      Real.sqrt (Real.log (X : ℝ)) < r * (theta * Real.log (X : ℝ)) ∧
      1 ≤ H * (theta * Real.log (X : ℝ)) ∧
      1 / (X : ℝ) + Real.exp (-r * (theta * Real.log (X : ℝ))) ≤ epsilon := by
  have hlogScale : Tendsto (fun X : ℕ ↦ (r * theta) * Real.log (X : ℝ)) atTop atTop :=
    EulerSubpower.tendsto_log_nat_atTop.const_mul_atTop (mul_pos hr htheta)
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlogScale
  have hinv : Tendsto (fun X : ℕ ↦ (X : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsum := hinv.add hexp
  simp only [zero_add] at hsum
  filter_upwards [eventually_ge_atTop 2,
    mrEventually_selected_scheduled_scale (mul_pos hr htheta) (by norm_num : (0 : ℝ) < 1) 1,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 / (H * theta))),
    hsum.eventually (gt_mem_nhds hepsilon)] with X hX hschedule hlarge herror
  have hh := (div_le_iff₀ (mul_pos hH htheta)).1 hlarge
  refine ⟨hX, by linarith [hschedule.2.1], by nlinarith [hschedule.2.2.2.1], ?_,
    by nlinarith, ?_⟩
  · simpa only [mul_assoc] using hschedule.2.2.2.2.1
  · simpa only [Function.comp_apply, one_div, neg_mul, mul_assoc] using herror.le

theorem mrSelectedProduct_card_sum_le {ι : Type*} (V : Finset ι) (e : ι → ℝ)
    {H L xi : ℝ} (hH : 0 ≤ H) (hL : 0 < L) (hxi : 0 ≤ xi)
    (hcard : (V.card : ℝ) ≤ 2 * H * L) (he : ∀ v ∈ V, L ^ 2 * e v ≤ xi) :
    (V.card : ℝ) * (∑ v ∈ V, e v) ≤ 4 * H ^ 2 * xi := by
  have hsum : (∑ v ∈ V, e v) ≤ (V.card : ℝ) * (xi / L ^ 2) := by
    calc
      _ ≤ ∑ _v ∈ V, xi / L ^ 2 := Finset.sum_le_sum
        (fun v hv ↦ (le_div_iff₀ (sq_pos_of_pos hL)).2 (by nlinarith [he v hv]))
      _ = _ := by simp
  calc
    _ ≤ (V.card : ℝ) * ((V.card : ℝ) * (xi / L ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (2 * H * L) * ((2 * H * L) * (xi / L ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

end

end Erdos67b

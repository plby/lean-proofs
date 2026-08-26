import ErdosProblems.Erdos1002.GaussPrefixLateAggregateCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial families dominated by a moving geometric gap

The late marked-Fourier argument produces several estimates whose
geometric base is not the fixed Gauss mixing base.  This file records the
corresponding abstract summation lemma with an arbitrary base `theta > 1`.
All finite-sum norms are taken before the cardinality bound is applied.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- A nested family with polynomial cardinality has vanishing total norm
when every summand is bounded by an inverse geometric in a gap tending to
infinity. -/
theorem
    tendsto_nested_sum_zero_of_pairCount_le_scalePow_inverseGeometric
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (z : ℕ → α → β → ℂ)
    (scale gap : ℕ → ℕ)
    (hgap : Tendsto gap atTop atTop)
    (dimension dilation : ℕ)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta : 1 < theta)
    (hscale : ∀ᶠ N : ℕ in atTop,
      scale N ≤ dilation * (gap N + 1))
    (hcard : ∀ᶠ N : ℕ in atTop,
      nestedPairCount (prefixes N) (futures N) ≤
        scale N ^ dimension)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        ‖z N p u‖ ≤ C * (theta ^ gap N)⁻¹) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u)
      atTop (nhds 0) := by
  let gapSucc : ℕ → ℕ := fun N ↦ gap N + 1
  let upper : ℕ → ℝ := fun N ↦
    (C * (dilation : ℝ) ^ dimension * theta) *
      ((gapSucc N : ℝ) ^ dimension *
        (theta ^ gapSucc N)⁻¹)
  have hgapSucc : Tendsto gapSucc atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun N ↦ Nat.le_add_right (gap N) 1) hgap
  have hpoly :
      Tendsto
        (fun N ↦
          (gapSucc N : ℝ) ^ dimension *
            (theta ^ gapSucc N)⁻¹)
        atTop (nhds 0) := by
    have h :=
      (tendsto_natPower_mul_inverse_geometric
        dimension 1 (by omega) htheta).comp hgapSucc
    simpa only [one_mul] using! h
  have hupper : Tendsto upper atTop (nhds 0) := by
    have h :=
      hpoly.const_mul
        (C * (dilation : ℝ) ^ dimension * theta)
    simpa only [upper, mul_zero] using! h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · filter_upwards [hscale, hcard, hbound] with
      N hscaleN hcardN hboundN
    have hpairReal :
        (nestedPairCount (prefixes N) (futures N) : ℝ) ≤
          (scale N : ℝ) ^ dimension := by
      exact_mod_cast hcardN
    have hscaleReal :
        (scale N : ℝ) ^ dimension ≤
          ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension := by
      exact pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast hscaleN) dimension
    have hrateNonneg :
        0 ≤ C * (theta ^ gap N)⁻¹ := by
      positivity
    have hfactor :
        (theta ^ gap N)⁻¹ =
          theta * (theta ^ gapSucc N)⁻¹ := by
      dsimp only [gapSucc]
      rw [pow_succ, mul_inv_rev]
      field_simp [ne_of_gt (zero_lt_one.trans htheta)]
    calc
      ‖∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u‖ ≤
          ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖ := by
        calc
          ‖∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u‖ ≤
              ∑ p ∈ prefixes N,
                ‖∑ u ∈ futures N p, z N p u‖ :=
            norm_sum_le _ _
          _ ≤
              ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖ := by
            apply Finset.sum_le_sum
            intro p _hp
            exact norm_sum_le _ _
      _ ≤
          ∑ p ∈ prefixes N, ∑ _u ∈ futures N p,
            C * (theta ^ gap N)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro u hu
        exact hboundN p hp u hu
      _ =
          (nestedPairCount (prefixes N) (futures N) : ℝ) *
            (C * (theta ^ gap N)⁻¹) := by
        simp only [Finset.sum_const, nsmul_eq_mul, nestedPairCount,
          Nat.cast_sum]
        rw [Finset.sum_mul]
      _ ≤
          (scale N : ℝ) ^ dimension *
            (C * (theta ^ gap N)⁻¹) :=
        mul_le_mul_of_nonneg_right hpairReal hrateNonneg
      _ ≤
          ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension *
            (C * (theta ^ gap N)⁻¹) :=
        mul_le_mul_of_nonneg_right hscaleReal hrateNonneg
      _ = upper N := by
        rw [hfactor]
        dsimp only [upper, gapSucc]
        push_cast
        rw [mul_pow]
        ring
  · exact hupper

/-- Real nonnegative version tailored to factorized norm sums. -/
theorem
    tendsto_nested_nonnegative_sum_zero_of_pairCount_le_scalePow_inverseGeometric
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (z : ℕ → α → β → ℝ)
    (scale gap : ℕ → ℕ)
    (hgap : Tendsto gap atTop atTop)
    (dimension dilation : ℕ)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta : 1 < theta)
    (hscale : ∀ᶠ N : ℕ in atTop,
      scale N ≤ dilation * (gap N + 1))
    (hcard : ∀ᶠ N : ℕ in atTop,
      nestedPairCount (prefixes N) (futures N) ≤
        scale N ^ dimension)
    (hnonneg : ∀ N p u, 0 ≤ z N p u)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        z N p u ≤ C * (theta ^ gap N)⁻¹) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u)
      atTop (nhds 0) := by
  let zComplex : ℕ → α → β → ℂ :=
    fun N p u ↦ (z N p u : ℂ)
  have hcomplex :
      Tendsto
        (fun N ↦
          ∑ p ∈ prefixes N,
            ∑ u ∈ futures N p, zComplex N p u)
        atTop (nhds 0) := by
    apply
      tendsto_nested_sum_zero_of_pairCount_le_scalePow_inverseGeometric
        prefixes futures zComplex scale gap hgap
        dimension dilation hC htheta hscale hcard
    filter_upwards [hbound] with N hboundN
    intro p hp u hu
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg N p u)]
    exact hboundN p hp u hu
  have hreal :
      Tendsto
        (fun N ↦
          (∑ p ∈ prefixes N,
            ∑ u ∈ futures N p, zComplex N p u).re)
        atTop (nhds 0) := by
    simpa only [Complex.zero_re] using!
      (Complex.continuous_re.tendsto 0).comp hcomplex
  exact hreal.congr' (Eventually.of_forall fun N ↦ by
    simp [zComplex])

/-- Direct factorized-norm corollary.  The future factor is used only
through its unit bound after the exact joint event has already been
formed; no approximation error is estimated by this lemma. -/
theorem
    tendsto_nested_factorized_norm_sum_zero_of_prefix_inverseGeometric
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (prefixMean : ℕ → α → ℂ)
    (futureMean : ℕ → α → β → ℂ)
    (scale gap : ℕ → ℕ)
    (hgap : Tendsto gap atTop atTop)
    (dimension dilation : ℕ)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta : 1 < theta)
    (hscale : ∀ᶠ N : ℕ in atTop,
      scale N ≤ dilation * (gap N + 1))
    (hcard : ∀ᶠ N : ℕ in atTop,
      nestedPairCount (prefixes N) (futures N) ≤
        scale N ^ dimension)
    (hprefix : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N,
        ‖prefixMean N p‖ ≤ C * (theta ^ gap N)⁻¹)
    (hfuture : ∀ N p, ∀ u ∈ futures N p,
      ‖futureMean N p u‖ ≤ 1) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N,
          ‖prefixMean N p‖ *
            ∑ u ∈ futures N p, ‖futureMean N p u‖)
      atTop (nhds 0) := by
  let z : ℕ → α → β → ℝ :=
    fun N p u ↦ ‖prefixMean N p‖ * ‖futureMean N p u‖
  have hz :
      Tendsto
        (fun N ↦
          ∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u)
        atTop (nhds 0) := by
    apply
      tendsto_nested_nonnegative_sum_zero_of_pairCount_le_scalePow_inverseGeometric
        prefixes futures z scale gap hgap dimension dilation
        hC htheta hscale hcard
    · intro N p u
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · filter_upwards [hprefix] with N hprefixN
      intro p hp u hu
      calc
        z N p u ≤ ‖prefixMean N p‖ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (hfuture N p u hu) (norm_nonneg _)
        _ = ‖prefixMean N p‖ := mul_one _
        _ ≤ C * (theta ^ gap N)⁻¹ := hprefixN p hp
  convert! hz using 1
  funext N
  unfold z
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]

/-- Pair-dependent form used when the delayed split, and hence the frozen
prefix factor, depends on the complete chronological tuple. -/
theorem
    tendsto_nested_pairwise_product_norm_sum_zero_of_prefix_inverseGeometric
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (prefixFactor futureFactor : ℕ → α → β → ℂ)
    (scale gap : ℕ → ℕ)
    (hgap : Tendsto gap atTop atTop)
    (dimension dilation : ℕ)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta : 1 < theta)
    (hscale : ∀ᶠ N : ℕ in atTop,
      scale N ≤ dilation * (gap N + 1))
    (hcard : ∀ᶠ N : ℕ in atTop,
      nestedPairCount (prefixes N) (futures N) ≤
        scale N ^ dimension)
    (hprefix : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        ‖prefixFactor N p u‖ ≤ C * (theta ^ gap N)⁻¹)
    (hfuture : ∀ N p, ∀ u ∈ futures N p,
      ‖futureFactor N p u‖ ≤ 1) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
          ‖prefixFactor N p u‖ * ‖futureFactor N p u‖)
      atTop (nhds 0) := by
  apply
    tendsto_nested_nonnegative_sum_zero_of_pairCount_le_scalePow_inverseGeometric
      prefixes futures
      (fun N p u ↦
        ‖prefixFactor N p u‖ * ‖futureFactor N p u‖)
      scale gap hgap dimension dilation hC htheta hscale hcard
  · intro N p u
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · filter_upwards [hprefix] with N hprefixN
    intro p hp u hu
    calc
      ‖prefixFactor N p u‖ * ‖futureFactor N p u‖ ≤
          ‖prefixFactor N p u‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (hfuture N p u hu) (norm_nonneg _)
      _ = ‖prefixFactor N p u‖ := mul_one _
      _ ≤ C * (theta ^ gap N)⁻¹ := hprefixN p hp u hu

end

end Erdos1002

import ErdosProblems.Erdos1002.GaussPrefixAnnularLateErrorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfer of full joint errors to factorized mean errors

A prefix error must not be estimated tuple by tuple and then multiplied by
the polynomial number of tuples.  The correct route keeps the future
factor attached.  Functional prefix--future mixing then compares the full
joint error with the product of its two means.  This file records that
argument with every norm inside the finite aggregate.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Deterministic aggregate inequality transferring a joint error to its
factorized product of means. -/
theorem sum_nested_norm_product_le_joint_add_covariance
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : Finset α) (futures : α → Finset β)
    (joint : α → β → ℂ)
    (prefixMean futureMean : α → β → ℂ) :
    (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖prefixMean p u * futureMean p u‖) ≤
      (∑ p ∈ prefixes, ∑ u ∈ futures p, ‖joint p u‖) +
        ∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖joint p u - prefixMean p u * futureMean p u‖ := by
  calc
    (∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖prefixMean p u * futureMean p u‖) ≤
      ∑ p ∈ prefixes, ∑ u ∈ futures p,
        (‖joint p u‖ +
          ‖joint p u - prefixMean p u * futureMean p u‖) := by
      apply Finset.sum_le_sum
      intro p _hp
      apply Finset.sum_le_sum
      intro u _hu
      have hrewrite :
          prefixMean p u * futureMean p u =
            joint p u -
              (joint p u - prefixMean p u * futureMean p u) := by
        ring
      calc
        ‖prefixMean p u * futureMean p u‖ =
            ‖joint p u -
              (joint p u - prefixMean p u * futureMean p u)‖ :=
          congrArg norm hrewrite
        _ ≤ ‖joint p u‖ +
            ‖joint p u - prefixMean p u * futureMean p u‖ :=
          norm_sub_le _ _
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

/-- Abstract limiting form: vanishing joint mass and vanishing summed
covariance imply vanishing products of means. -/
theorem tendsto_sum_nested_norm_product_zero_of_joint_covariance
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (joint prefixMean futureMean : ℕ → α → β → ℂ)
    (hjoint : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖joint N p u‖)
      atTop (nhds 0))
    (hcovariance : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖joint N p u -
          prefixMean N p u * futureMean N p u‖)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖prefixMean N p u * futureMean N p u‖)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦
        Finset.sum_nonneg fun _u _hu ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦
      sum_nested_norm_product_le_joint_add_covariance
        (prefixes N) (futures N)
        (joint N) (prefixMean N) (futureMean N)
  · simpa only [zero_add] using! hjoint.add hcovariance

/-- A uniform covariance rate converts directly into a summed covariance
limit once pair-count times rate tends to zero. -/
theorem tendsto_sum_nested_norm_covariance_zero_of_uniform_rate
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (joint prefixMean futureMean : ℕ → α → β → ℂ)
    (rate : ℕ → ℝ)
    (hrateNonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ rate N)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        ‖joint N p u -
          prefixMean N p u * futureMean N p u‖ ≤ rate N)
    (hrate : Tendsto
      (fun N ↦
        (nestedPairCount (prefixes N) (futures N) : ℝ) * rate N)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖joint N p u -
          prefixMean N p u * futureMean N p u‖)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦
        Finset.sum_nonneg fun _u _hu ↦ norm_nonneg _
  · filter_upwards [hrateNonneg, hbound] with N hrateN hboundN
    calc
      (∑ p ∈ prefixes N, ∑ u ∈ futures N p,
          ‖joint N p u -
            prefixMean N p u * futureMean N p u‖) ≤
        ∑ p ∈ prefixes N, ∑ _u ∈ futures N p, rate N := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro u hu
        exact hboundN p hp u hu
      _ = (nestedPairCount (prefixes N) (futures N) : ℝ) *
          rate N := by
        simp only [Finset.sum_const, nsmul_eq_mul, nestedPairCount,
          Nat.cast_sum]
        rw [Finset.sum_mul]
  · exact hrate

/-- Combined form used for bad-prefix and boundary-prefix fragments.  The
future factor remains attached through `hjoint`; only after the full
joint mass has been deleted is functional mixing used to factor it. -/
theorem tendsto_sum_nested_norm_product_zero_of_joint_uniformMixing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (joint prefixMean futureMean : ℕ → α → β → ℂ)
    (rate : ℕ → ℝ)
    (hjoint : Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖joint N p u‖)
      atTop (nhds 0))
    (hrateNonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ rate N)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        ‖joint N p u -
          prefixMean N p u * futureMean N p u‖ ≤ rate N)
    (hrate : Tendsto
      (fun N ↦
        (nestedPairCount (prefixes N) (futures N) : ℝ) * rate N)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖prefixMean N p u * futureMean N p u‖)
      atTop (nhds 0) := by
  apply tendsto_sum_nested_norm_product_zero_of_joint_covariance
    prefixes futures joint prefixMean futureMean hjoint
  exact tendsto_sum_nested_norm_covariance_zero_of_uniform_rate
    prefixes futures joint prefixMean futureMean rate
    hrateNonneg hbound hrate

end

end Erdos1002

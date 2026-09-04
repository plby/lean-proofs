/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointPageBand
import ErdosProblems.Erdos48.EndpointMiddleZero

/-!
# Aggregate endpoint zero-kernel bounds outside the Page conductor

This file sums the pointwise Page-band decomposition over primitive
characters and conductors.  Every middle band is bounded by the aggregate
high-zero multiplicity; the only remaining term is a far-left kernel mass.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- Aggregate complete zero-kernel norm outside one excluded conductor. -/
noncomputable def nonexcludedPrimitiveZeroKernelMass
    (Q m₀ : ℕ) (x T : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀),
    ∑ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖

/-- Aggregate norm of the far-left remainders at all primitive conductors. -/
noncomputable def primitiveFarZeroKernelMass
    (Q : ℕ) (x eta : ℝ) (J : ℕ) (T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
    ‖primitiveFarZeroKernelSumAt q psi x eta J T‖

theorem primitiveZeroKernelMass_eq_sum_norm_primitiveZeroKernelSumAt
    (x : ℕ) {q : ℕ} (hq : 1 < q) (T : ℝ) :
    primitiveZeroKernelMass x q T =
      ∑ psi : primitiveCharacters q,
        ‖primitiveZeroKernelSumAt q psi (x : ℝ) T‖ := by
  let : NeZero q := ⟨by omega⟩
  rw [primitiveZeroKernelMass_eq x (by omega) T]
  apply Fintype.sum_congr
  intro psi
  rw [primitiveZeroKernelSumAt_eq hq]

/-- Summing the pointwise Page decomposition and enlarging the nonexcluded
conductor set to all conductors bounds the complete kernel mass by the middle
bands and the global far-left remainder. -/
theorem nonexcludedPrimitiveZeroKernelMass_le_linearBands_add_far
    {Q T : ℕ} {eta : ℝ} {m₀ : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    {x : ℝ} (hx : 0 < x) (heta : 0 < eta) (heta1 : eta < 1)
    (J : ℕ) :
    nonexcludedPrimitiveZeroKernelMass Q m₀ x T ≤
      (∑ j ∈ Finset.range J,
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi x
            (((j + 1 : ℕ) : ℝ) * eta)
            (((j + 2 : ℕ) : ℝ) * eta) T‖) +
        primitiveFarZeroKernelMass Q x eta J T := by
  classical
  let S := (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m₀)
  let B : (j q : ℕ) → primitiveCharacters q → ℝ := fun j q psi ↦
    ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi x
      (((j + 1 : ℕ) : ℝ) * eta)
      (((j + 2 : ℕ) : ℝ) * eta) T‖
  let F : (q : ℕ) → primitiveCharacters q → ℝ := fun q psi ↦
    ‖primitiveFarZeroKernelSumAt q psi x eta J T‖
  have hpoint : ∀ q ∈ S, ∀ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖ ≤
        (∑ j ∈ Finset.range J, B j q psi) + F q psi := by
    intro q hq psi
    have hqData := Finset.mem_filter.mp hq
    exact norm_zeroKernel_le_linearBands_add_far_of_ne_excluded
      hpage hqData.1 hqData.2 psi hx heta heta1 J
  unfold nonexcludedPrimitiveZeroKernelMass primitiveFarZeroKernelMass
  change (∑ q ∈ S, ∑ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖) ≤ _
  calc
    (∑ q ∈ S, ∑ psi : primitiveCharacters q,
        ‖primitiveZeroKernelSumAt q psi x T‖) ≤
      ∑ q ∈ S, ∑ psi : primitiveCharacters q,
        ((∑ j ∈ Finset.range J, B j q psi) + F q psi) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro psi _
      exact hpoint q hq psi
    _ = (∑ j ∈ Finset.range J,
          ∑ q ∈ S, ∑ psi : primitiveCharacters q, B j q psi) +
        ∑ q ∈ S, ∑ psi : primitiveCharacters q, F q psi := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
    _ ≤ (∑ j ∈ Finset.range J,
          ∑ q ∈ Finset.Ioc 1 Q,
            ∑ psi : primitiveCharacters q, B j q psi) +
        ∑ q ∈ Finset.Ioc 1 Q,
          ∑ psi : primitiveCharacters q, F q psi := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          exact (Finset.mem_filter.mp hq).1
        · intro q hqAll hqS
          exact Finset.sum_nonneg fun psi _ ↦ norm_nonneg _
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          exact (Finset.mem_filter.mp hq).1
        · intro q hqAll hqS
          exact Finset.sum_nonneg fun psi _ ↦ norm_nonneg _
    _ = _ := rfl

/-- Apply the aggregate high-zero rectangle estimate to every middle band. -/
theorem nonexcludedPrimitiveZeroKernelMass_le_densityBands_add_far
    {Q T : ℕ} {eta : ℝ} {m₀ : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    {x : ℝ} (hx : 1 ≤ x) (heta : 0 < eta) (heta1 : eta < 1)
    (J : ℕ)
    (hwidth : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) < 1) :
    nonexcludedPrimitiveZeroKernelMass Q m₀ x T ≤
      (∑ j ∈ Finset.range J,
        2 * ((primitiveHighZeroMass Q
            (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
          (x ^ (1 - (((j + 1 : ℕ) : ℝ) * eta)) * Real.log x))) +
        primitiveFarZeroKernelMass Q x eta J T := by
  apply (nonexcludedPrimitiveZeroKernelMass_le_linearBands_add_far
    hpage (zero_lt_one.trans_le hx) heta heta1 J).trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    exact sum_norm_primitiveTwoSidedZeroRealBandKernelSumAt_le
      hx (hwidth j hj) (by positivity)
  · exact le_rfl

/-- The endpoint form of the preceding theorem.  If every retained band
lies in `Re rho >= 1/2`, the quotient kernel removes the extraneous
`log x` factor. -/
theorem nonexcludedPrimitiveZeroKernelMass_le_sharpDensityBands_add_far
    {Q T : ℕ} {eta : ℝ} {m₀ : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    {x : ℝ} (hx : 1 ≤ x) (heta : 0 < eta) (heta1 : eta < 1)
    (J : ℕ)
    (hwidth : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 2) :
    nonexcludedPrimitiveZeroKernelMass Q m₀ x T ≤
      (∑ j ∈ Finset.range J,
        8 * ((primitiveHighZeroMass Q
            (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
          x ^ (1 - (((j + 1 : ℕ) : ℝ) * eta)))) +
        primitiveFarZeroKernelMass Q x eta J T := by
  apply (nonexcludedPrimitiveZeroKernelMass_le_linearBands_add_far
    hpage (zero_lt_one.trans_le hx) heta heta1 J).trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    exact sum_norm_primitiveTwoSidedZeroRealBandKernelSumAt_le_eight
      hx (hwidth j hj) (by positivity)
  · exact le_rfl

end

end Erdos48

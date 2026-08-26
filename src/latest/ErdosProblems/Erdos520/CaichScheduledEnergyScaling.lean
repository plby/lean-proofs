import ErdosProblems.Erdos520.CaichScheduledMainCleanup
import Mathlib.Algebra.Order.GroupWithZero.Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Honest constant scaling for the scheduled main-term cleanup

The paper's near-ratio range contains a fixed `O_K(ell log ell)` number of
thin blocks, not literally at most `ell log ell` blocks with unit constant.
The fixed constant is absorbed transparently by scaling the block-energy
family.  This file records the exact algebra needed for that repair.
-/

/-- Multiply every member of a block-energy family by one fixed constant. -/
noncomputable def caichScaledBlockEnergy
    (D0 : ℝ) (U : ℕ → ℕ → Omega → ℝ) :
    ℕ → ℕ → Omega → ℝ :=
  fun ell j omega ↦ D0 * U ell j omega

/-- Pointwise order of energy families passes to the finite running maximum. -/
theorem caichBlockEnergyMax_mono_family
    {J : ℕ → ℕ} {U V : ℕ → ℕ → Omega → ℝ}
    {ell : ℕ} {omega : Omega}
    (hUV : ∀ j ≤ J ell, U ell j omega ≤ V ell j omega) :
    caichBlockEnergyMax J U ell omega ≤
      caichBlockEnergyMax J V ell omega := by
  unfold caichBlockEnergyMax
  apply Finset.sup'_mono_fun
  intro j hj
  exact hUV j (Finset.mem_range_succ_iff.mp hj)

/-- The running maximum commutes exactly with multiplication by a
nonnegative scalar. -/
theorem caichBlockEnergyMax_scaled
    {J : ℕ → ℕ} {U : ℕ → ℕ → Omega → ℝ}
    {D0 : ℝ} (hD0 : 0 ≤ D0) (ell : ℕ) (omega : Omega) :
    caichBlockEnergyMax J (caichScaledBlockEnergy D0 U) ell omega =
      D0 * caichBlockEnergyMax J U ell omega := by
  unfold caichBlockEnergyMax caichScaledBlockEnergy
  exact (Finset.mul₀_sup' hD0
    (fun j ↦ U ell j omega)
    (Finset.range (J ell + 1)) Finset.nonempty_range_add_one).symm

theorem caichBlockEnergyMax_nonneg_of_family
    {J : ℕ → ℕ} {U : ℕ → ℕ → Omega → ℝ}
    {ell : ℕ} {omega : Omega}
    (hU : ∀ j ≤ J ell, 0 ≤ U ell j omega) :
    0 ≤ caichBlockEnergyMax J U ell omega := by
  have hzero : 0 ≤ U ell 0 omega := hU 0 (Nat.zero_le _)
  exact hzero.trans (by
    unfold caichBlockEnergyMax
    have hmem : 0 ∈ Finset.range (J ell + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    exact Finset.le_sup' (fun j ↦ U ell j omega) hmem)

/-- A block-maximum good estimate transfers to the scaled energy family,
with the displayed constant multiplied by exactly the same scalar. -/
theorem blockEnergyMaxGoodAtScale_scaled
    {J : ℕ → ℕ} {U : ℕ → ℕ → Omega → ℝ}
    {D0 B : ℝ} {K ell : ℕ} {omega : Omega}
    (hD0 : 0 ≤ D0)
    (hgood : blockEnergyMaxGoodAtScale J U B K ell omega) :
    blockEnergyMaxGoodAtScale J (caichScaledBlockEnergy D0 U)
      (D0 * B) K ell omega := by
  unfold blockEnergyMaxGoodAtScale at hgood ⊢
  rw [caichBlockEnergyMax_scaled hD0]
  have hmul := mul_le_mul_of_nonneg_left hgood hD0
  calc
    D0 * caichBlockEnergyMax J U ell omega ≤
        D0 * (B * Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2)) := hmul
    _ = (D0 * B) * Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
          (ell : ℝ) ^ ((K : ℝ) / 2) := by ring

/-- Eventual almost-sure block control transfers through the same explicit
scaling, without changing any exponent. -/
theorem ae_eventually_blockEnergyMaxGoodAtScale_scaled
    {J : ℕ → ℕ} {U : ℕ → ℕ → Omega → ℝ}
    {D0 B : ℝ} {K : ℕ} (hD0 : 0 ≤ D0)
    (hgood : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in Filter.atTop,
      blockEnergyMaxGoodAtScale J U B K ell omega) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in Filter.atTop,
      blockEnergyMaxGoodAtScale J (caichScaledBlockEnergy D0 U)
        (D0 * B) K ell omega := by
  filter_upwards [hgood] with omega homega
  filter_upwards [homega] with ell hell
  exact blockEnergyMaxGoodAtScale_scaled hD0 hell

/-- Capped scheduled cleanup with the honest fixed near-block coefficient.

The assumption is now the true estimate

`(# near blocks) * C ≤ D0 * (ell * log ell)`.

The left side is the unaccounted main term formed with the explicitly scaled
energy family.  Thus no fixed `O_K(1)` is hidden or incorrectly replaced by
one. -/
theorem caichUnaccountedSmoothedMain_le_scaledScheduledL12_add_L2
    {X C D0 : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (hD0 : 0 ≤ D0)
    (omega : Omega)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hfinal : x ≤ endpoint N)
    (hJ : ∀ j ∈ Finset.range N, near j → blockIndex j ≤ J ell)
    (hright : ∀ j ∈ Finset.range N, near j →
      2 ≤ caichCappedThinEndpoint x endpoint (j + 1))
    (hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ Finset.range N, near j → ∀ z ∈
      Ioc
        ((x : ℝ) /
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ))
        ((x : ℝ) / (caichCappedThinEndpoint x endpoint j : ℝ)),
      caichShortWindowReciprocalMass X x
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) z ≤
        C / (X * Real.log
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ)))
    (hmax : 0 ≤ caichBlockEnergyMax J U ell omega)
    (hbudget : (((Finset.range N).filter near).card : ℝ) * C ≤
      D0 * caichAuxiliaryLogFactor ell) :
    caichUnaccountedSmoothedMain X J (caichScaledBlockEnergy D0 U)
        ell omega x (caichCappedThinEndpoint x endpoint 0) x ≤
      caichScheduledL12 X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) near +
        caichScheduledL2 X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) := by
  let blocks := Finset.range N
  let left : ℕ → ℕ := caichCappedThinEndpoint x endpoint
  let right : ℕ → ℕ := fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)
  let M : ℝ := caichBlockEnergyMax J U ell omega
  let Mscaled : ℝ :=
    caichBlockEnergyMax J (caichScaledBlockEnergy D0 U) ell omega
  have hscale : Mscaled = D0 * M := by
    simpa only [Mscaled, M] using!
      caichBlockEnergyMax_scaled (J := J) (U := U) hD0 ell omega
  have hcleanup := caichInitialSmoothedMain_le_nearMax_add_residuals
    J U endpoint N near blockIndex hX hx hC omega hmono hone hfinal
      hJ hright hU hshort
  have hcoeff :
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M ≤
        caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled := by
    calc
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M ≤
          (D0 * caichAuxiliaryLogFactor ell) * (x : ℝ) * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbudget (by positivity)) hmax
      _ = caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled := by
        rw [hscale]
        ring
  have hcleanupScaled :
      caichInitialSmoothedMain X omega x
          (caichCappedThinEndpoint x endpoint 0) x ≤
        caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled +
          caichLongRatioAveragedMain X omega x blocks left right near +
          caichBoundaryAveragedMain X omega x blocks left right := by
    calc
      caichInitialSmoothedMain X omega x
          (caichCappedThinEndpoint x endpoint 0) x ≤
          (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) * M +
            caichLongRatioAveragedMain X omega x blocks left right near +
            caichBoundaryAveragedMain X omega x blocks left right := by
        simpa only [blocks, left, right, M] using! hcleanup
      _ ≤ caichAuxiliaryLogFactor ell * (x : ℝ) * Mscaled +
            caichLongRatioAveragedMain X omega x blocks left right near +
            caichBoundaryAveragedMain X omega x blocks left right := by
        gcongr
  have hmaxScaled : 0 ≤ Mscaled := by
    rw [hscale]
    exact mul_nonneg hD0 hmax
  exact caichUnaccountedSmoothedMain_le_scheduledL12_add_L2
    J (caichScaledBlockEnergy D0 U) blocks left right near hX.le hx omega
      hmaxScaled le_rfl (by
        simpa only [Mscaled] using! hcleanupScaled)

end Problem520
end Erdos

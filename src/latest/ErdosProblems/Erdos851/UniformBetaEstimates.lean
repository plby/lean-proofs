/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaParameterChoice
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos851.FinalAssembly

/-!
# Uniform beta-sieve cardinal estimates

This file discharges the last analytic interface of `FinalAssembly`.  A
single Rosser depth is chosen from the two Mertens constants, and the moving
prime cutoff is then eventually beyond every fixed lower endpoint.
-/

open Filter
open scoped Topology

namespace Erdos851

open ShiftSieve

/-- The concrete beta sieve supplies the one- and two-shift interval bounds
uniformly in the fixed lower prime endpoint. -/
theorem uniform_beta_cardinal_estimates : UniformBetaCardinalEstimates := by
  obtain ⟨A₁, hA₁, hone⟩ := exists_oneShift_concrete_cardinality_bounds
  obtain ⟨A₂, hA₂, hpair⟩ := exists_pairShift_concrete_cardinality_bounds
  intro theta htheta _hthetaOne
  let A := max A₁ A₂
  have hA : 1 ≤ A := hA₁.trans (le_max_left A₁ A₂)
  obtain ⟨S, hS, hlogA, heta⟩ := exists_betaDepth hA htheta
  have hSpos : 0 < S := by omega
  have hlogA₁ : Real.log A₁ ≤ 2 * ((S - 100 : ℕ) : ℝ) / 99 := by
    exact (Real.log_le_log (by positivity) (le_max_left A₁ A₂)).trans hlogA
  have hlogA₂ : Real.log A₂ ≤ 4 * ((S - 100 : ℕ) : ℝ) / 99 := by
    have hle := Real.log_le_log (by positivity) (le_max_right A₁ A₂)
    have hstart : (0 : ℝ) ≤ (S - 100 : ℕ) := by positivity
    calc
      Real.log A₂ ≤ Real.log A := hle
      _ ≤ 2 * ((S - 100 : ℕ) : ℝ) / 99 := hlogA
      _ ≤ 4 * ((S - 100 : ℕ) : ℝ) / 99 := by nlinarith
  let eta₁ : ℝ := (4 * A₁ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let eta₂ : ℝ := (4 * A₂ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have heta₁ : eta₁ < theta := by
    apply lt_of_le_of_lt _ heta
    dsimp [eta₁, A]
    gcongr
    exact le_max_left A₁ A₂
  have heta₂ : eta₂ < theta := by
    apply lt_of_le_of_lt _ heta
    dsimp [eta₂, A]
    gcongr
    exact le_max_right A₁ A₂
  refine ⟨S, hSpos, ?_⟩
  intro z hz
  unfold BetaCardinalEstimatesAt
  have hyTendsto : Tendsto
      (fun X : ℕ ↦ roughCutoff S (logIndex X)) atTop atTop :=
    (tendsto_roughCutoff_atTop S hSpos).comp tendsto_logIndex_atTop
  have hzyEventually : ∀ᶠ X : ℕ in atTop,
      z ≤ roughCutoff S (logIndex X) :=
    hyTendsto.eventually (eventually_ge_atTop z)
  have hyEventually : ∀ᶠ X : ℕ in atTop,
      2 ≤ roughCutoff S (logIndex X) :=
    hyTendsto.eventually (eventually_ge_atTop 2)
  filter_upwards [hzyEventually, hyEventually, eventually_gt_atTop 0] with
      X hzy hy hX
  dsimp only
  let J := logIndex X
  let y := roughCutoff S J
  let D := distributionLevel J
  have hzy' : z ≤ y := by simpa [y, J] using hzy
  have hy' : 1 < y := by
    have : 2 ≤ y := by simpa [y, J] using hy
    omega
  have hcutoffPow : y ^ S ≤ D := by
    exact roughCutoff_pow_le_distributionLevel hSpos
  have hcutoffSq : ((y ^ S : ℕ) : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hcutoffPow 2
  have hV₁ : 0 ≤ localEulerProduct oneShiftDensity z y :=
    oneShift_localEulerProduct_pos.le
  have hXnonneg : (0 : ℝ) ≤ X := by positivity
  have honeEta : eta₁ ≤ theta := heta₁.le
  have hpairEta : eta₂ ≤ theta := heta₂.le
  have honeLowerCoeff :
      (1 - theta) * localEulerProduct oneShiftDensity z y ≤
        (1 - eta₁) * localEulerProduct oneShiftDensity z y :=
    mul_le_mul_of_nonneg_right (sub_le_sub_left honeEta 1) hV₁
  have honeUpperCoeff :
      (1 + eta₁) * localEulerProduct oneShiftDensity z y ≤
        (1 + theta) * localEulerProduct oneShiftDensity z y :=
    mul_le_mul_of_nonneg_right
      (by simpa [add_comm] using add_le_add_left honeEta 1) hV₁
  constructor
  · intro k hk
    have hkX : 2 ^ k ≤ X :=
      pow_le_of_mem_powIndices_logIndex hX hk
    have hb := hone (2 ^ k) X z y S hkX hz hzy' hy' hS hlogA₁
    dsimp only at hb
    change
      (1 - theta) * localEulerProduct oneShiftDensity z y * (X : ℝ) -
          (D : ℝ) ^ 2 ≤
        ((siftedShiftCandidates {2 ^ k} X z (y + 1)).card : ℝ)
    calc
      (1 - theta) * localEulerProduct oneShiftDensity z y * (X : ℝ) -
            (D : ℝ) ^ 2 ≤
          (X : ℝ) * ((1 - eta₁) *
            localEulerProduct oneShiftDensity z y) -
              ((y ^ S : ℕ) : ℝ) ^ 2 := by
        exact sub_le_sub
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left honeLowerCoeff hXnonneg)
          hcutoffSq
      _ ≤ ((siftedShiftCandidates {2 ^ k} X z (y + 1)).card : ℝ) := by
        simpa [eta₁] using hb.1
  · constructor
    · intro k hk
      have hkX : 2 ^ k ≤ X :=
        pow_le_of_mem_powIndices_logIndex hX hk
      have hb := hone (2 ^ k) X z y S hkX hz hzy' hy' hS hlogA₁
      dsimp only at hb
      change
        ((siftedShiftCandidates {2 ^ k} X z (y + 1)).card : ℝ) ≤
          (1 + theta) * localEulerProduct oneShiftDensity z y * (X : ℝ) +
            (D : ℝ) ^ 2
      calc
        ((siftedShiftCandidates {2 ^ k} X z (y + 1)).card : ℝ) ≤
            (X : ℝ) * ((1 + eta₁) *
              localEulerProduct oneShiftDensity z y) +
                ((y ^ S : ℕ) : ℝ) ^ 2 := by
          simpa [eta₁] using hb.2
        _ ≤ (1 + theta) * localEulerProduct oneShiftDensity z y *
              (X : ℝ) + (D : ℝ) ^ 2 := by
          exact add_le_add
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_left honeUpperCoeff hXnonneg)
            hcutoffSq
    · intro k hk l hl hkl
      have hkX : 2 ^ k ≤ X :=
        pow_le_of_mem_powIndices_logIndex hX hk
      have hlX : 2 ^ l ≤ X :=
        pow_le_of_mem_powIndices_logIndex hX hl
      have hb := hpair (2 ^ k) (2 ^ l) X z y S hkX hlX hz hzy'
        hy' hS hlogA₂
      dsimp only at hb
      have hV₂ : 0 ≤ localEulerProduct
          (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y :=
        (pairShift_localEulerProduct_pos
          (Nat.dist (2 ^ k) (2 ^ l)) hz).le
      have hpairUpperCoeff :
          (1 + eta₂) * localEulerProduct
              (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y ≤
            (1 + theta) * localEulerProduct
              (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y :=
        mul_le_mul_of_nonneg_right
          (by simpa [add_comm] using add_le_add_left hpairEta 1) hV₂
      change
        ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z (y + 1)).card : ℝ) ≤
          (1 + theta) * localEulerProduct
              (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y * (X : ℝ) +
            (D : ℝ) ^ 2
      calc
        ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z (y + 1)).card : ℝ) ≤
            (X : ℝ) * ((1 + eta₂) * localEulerProduct
              (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y) +
                ((y ^ S : ℕ) : ℝ) ^ 2 := by
          simpa [eta₂] using hb.2
        _ ≤ (1 + theta) * localEulerProduct
              (pairShiftDensity (Nat.dist (2 ^ k) (2 ^ l))) z y *
                (X : ℝ) + (D : ℝ) ^ 2 := by
          exact add_le_add
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_left hpairUpperCoeff hXnonneg)
            hcutoffSq

end Erdos851

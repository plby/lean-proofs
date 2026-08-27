/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialCoupledRegularity
import ErdosProblems.Erdos207.InitialSupportPowerArithmetic
import ErdosProblems.Erdos207.PowerAbsorberCrudeCoefficients

/-! # Discharging initial regularity for the constructed power absorber -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def initialSupportPower (rootPower : ℕ) : ℕ := 156 * rootPower + 1

def initialRegularityCoefficientPower (q rootPower : ℕ) : ℕ :=
  max (powerAbsorberCrudeExponent q rootPower) (3 * initialSupportPower rootPower + 2)

theorem InitialPowerVortexPackage.support_power_bounds
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hc : powerAbsorberCoefficient q ≤ t) :
    (∀ x, P.H.degree x ≤ t ^ initialSupportPower rootPower) ∧
      (graphSupportFinset P.H).card ≤ t ^ initialSupportPower rootPower ∧
      (verticesOn P.B).card ≤ t ^ initialSupportPower rootPower := by
  have hbound : highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156 ≤
      t ^ initialSupportPower rootPower := by
    rw [highGirthAbsorber_power_normalize, initialSupportPower, pow_succ]
    calc
      _ ≤ t * t ^ (156 * rootPower) := Nat.mul_le_mul_right _ hc
      _ = _ := Nat.mul_comm _ _
  exact ⟨fun x ↦ (P.graphDegree x).trans hbound, P.graphSupport.trans hbound,
    P.bankSupport.trans hbound⟩

theorem InitialPowerVortexPackage.initial_coupled_regularity
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (R s b : ℕ) (ht : 16 ≤ t) (hb : 1 ≤ b)
    (hc : powerAbsorberCoefficient q ≤ t)
    (hcrude : powerAbsorberCrudeCoefficient q ≤ t)
    (hempty : pairBankPolynomialCoefficient q ≤ t)
    (hvertex : 2 ^ (q ^ 3) * (q + 1) ≤ t) (hbinomial : 2 ^ q ≤ t)
    (hscale : t ^ R ≤ n)
    (hrootGap : initialRegularityCoefficientPower q rootPower + 2 + s + b * q ≤ R)
    (hpairGap : initialSupportPower rootPower + s + 2 ≤ R) :
    let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)
    let Q := initialResidualPairs P.H
    let A : ℝ := S.available.card
    KSSSInitialRegularity (initialRestrictedAbsorberFamily q P.B S.available) S q Q
      (initialErdosTrajectoryCoefficient (Fin n) A) Q.card A (1 / (t : ℝ) ^ s) := by
  let v := initialSupportPower rootPower
  let u := initialRegularityCoefficientPower q rootPower
  have htR : (16 : ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hscaleR : (t : ℝ) ^ R ≤ n := by exact_mod_cast hscale
  have hn1 : 1 ≤ n := (Nat.one_le_pow _ _ (by omega : 1 ≤ t)).trans hscale
  have hN : (1 : ℝ) ≤ Fintype.card (Fin n) := by simpa using (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
  obtain ⟨hdegree, hgraph, hbank⟩ := P.support_power_bounds hc
  have hvR : (t : ℝ) ^ (v + 1) ≤ n :=
    (pow_le_pow_right₀ ht1 (by dsimp only [v]; omega)).trans hscaleR
  have hlarge : 6 * t ^ v + 4 ≤ Fintype.card (Fin n) := by
    have hreal := (initial_support_density_power (t : ℝ) v (by linarith)).trans hvR
    simpa using (show 6 * t ^ v + 4 ≤ n by exact_mod_cast hreal)
  have hrootCoeff : (pairExactBankExtensionCoefficient q P.B : ℝ) ≤ (t : ℝ) ^ u := by
    have hraw := (P.crude_coefficients_le_power hcrude).1
    have hone : (1 : ℝ≥0) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
    have hweak : (pairExactBankExtensionCoefficient q P.B : ℝ≥0) ≤
        2 ^ q * pairExactBankExtensionCoefficient q P.B := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hone
          (show (0 : ℝ≥0) ≤ pairExactBankExtensionCoefficient q P.B from zero_le)
    have hbase : (pairExactBankExtensionCoefficient q P.B : ℝ≥0) ≤
        (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower := hweak.trans hraw
    exact (show (pairExactBankExtensionCoefficient q P.B : ℝ) ≤
        (t : ℝ) ^ powerAbsorberCrudeExponent q rootPower by exact_mod_cast hbase).trans
      (pow_le_pow_right₀ ht1 (le_max_left _ _))
  have hemptyC : pairExactBankExtensionCoefficient q (∅ : TripleSystemOn (Fin n)) ≤ t := by
    have hx := pairExactBankExtensionCoefficient_le_bank_polynomial q (∅ : TripleSystemOn (Fin n))
    simpa only [card_empty, zero_add, one_pow, mul_one] using hx.trans (by simpa using hempty)
  have hbad : (((graphSupportFinset P.H).card : ℝ) ^ 2 * Fintype.card (Fin n) +
      ((verticesOn P.B).card : ℝ) ^ 3) * pairExactBankExtensionCoefficient q (∅ : TripleSystemOn (Fin n)) ≤
        (t : ℝ) ^ u * Fintype.card (Fin n) := by
    have hx := initial_support_unavailable_power (Fintype.card (Fin n)) t
      (graphSupportFinset P.H).card (verticesOn P.B).card
      (pairExactBankExtensionCoefficient q (∅ : TripleSystemOn (Fin n))) v hN (by linarith)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hgraph) (by exact_mod_cast hbank) (by exact_mod_cast hemptyC)
    exact hx.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht1 (le_max_right _ _)) (Nat.cast_nonneg _))
  have hvertices : ((verticesOn P.B).card : ℝ) * (2 ^ (q ^ 3) * (q + 1) : ℕ) ≤ (t : ℝ) ^ u := by
    calc
      _ ≤ (t : ℝ) ^ v * t := mul_le_mul (by exact_mod_cast hbank) (by exact_mod_cast hvertex)
        (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)
      _ = (t : ℝ) ^ (v + 1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ ht1 (by dsimp only [u, v, initialRegularityCoefficientPower]; omega)
  have hratio : (6 : ℝ) ≤ (t : ℝ) ^ b := by
    have hp : (t : ℝ) ≤ (t : ℝ) ^ b := by simpa using pow_le_pow_right₀ ht1 hb
    linarith
  have hloss : 3 * ((t ^ v : ℕ) : ℝ) + 2 ≤ (Fintype.card (Fin n) : ℝ) / (2 * (t : ℝ) ^ s) := by
    simpa only [Nat.cast_pow, Fintype.card_fin] using
      initial_support_pair_loss_power (n : ℝ) t v s R (by linarith) hscaleR hpairGap
  exact initial_absorber_coupled_regularity q (t ^ v) u R s b P.H P.B t
    hdegree hbank hlarge (by linarith) (by exact_mod_cast hbinomial)
    hrootCoeff hbad hvertices (by simpa using hscaleR) hrootGap hratio hloss

end

end Erdos207

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherNegativeHybrid
import ErdosProblems.Erdos48.GallagherSelection

/-!
# Unweighted selected-zero aggregation for Gallagher's amplifier

The Bombieri--Davenport amplifier controls the unweighted sum over
primitive characters.  This module rebuilds the selected-ordinate and
endpoint-separated Abel aggregation in precisely that normalization.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable def unweightedPrimitiveCutoffVonMangoldtEnergy
    (Q A N : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
    unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A m)
      cutoffVonMangoldtCoefficient t

noncomputable def unweightedPrimitiveGallagherEndpointSquare
    (Q A N j : ℕ) (eta t : ℝ) : ℝ :=
  |gallagherWeight eta (j - 1) N| ^ 2 *
    unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
      cutoffVonMangoldtCoefficient t

theorem continuous_unweightedPrimitiveNegativeDirichletMass
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (unweightedPrimitiveNegativeDirichletMass Q s c) := by
  unfold unweightedPrimitiveNegativeDirichletMass
  fun_prop

theorem sum_selectedOrdinates_card_mul_le_variableUnweightedPrimitiveMass
    (Q : ℕ) (Y : ℕ → ℕ) (c : ℕ → ℕ → ℂ)
    (N T L J : ℕ) (eta delta b : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hb : 0 ≤ b)
    (S : ∀ q : ℕ, primitiveCharacters q → Finset ℝ)
    (order : ∀ q : ℕ, primitiveCharacters q → ℝ → ℕ)
    (hS : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ x ∈ S q psi, ∀ y ∈ S q psi, x ≠ y →
        2 * delta * eta < dist x y)
    (horder : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, L ≤ order q psi t ∧ order q psi t ≤ J)
    (hlower : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, ∀ u : ℝ, |u - t| ≤ delta * eta →
        b ≤
          ‖∑ n ∈ Finset.Ioc (Y (order q psi t)) N,
            c (order q psi t) n * psi.1 n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * b ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          unweightedPrimitiveNegativeDirichletMass Q
            (Finset.Ioc (Y j) N) (c j) u := by
  classical
  have hone (q : ℕ) (hq : q ∈ Finset.Ioc 1 Q)
      (psi : primitiveCharacters q) :
      ((S q psi).card : ℝ) * (delta * eta) * b ^ 2 ≤
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            ‖∑ n ∈ Finset.Ioc (Y j) N,
              c j n * psi.1 n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 :=
    selectedOrdinates_card_mul_le_variableDetector_integrals
      psi Y c N T L J eta delta b heta heta1 hdelta hdelta1 hb
      (S q psi) (order q psi) (hS q hq psi) (hsep q hq psi)
      (horder q hq psi) (hlower q hq psi)
  have hsum :
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ((S q psi).card : ℝ) * (delta * eta) * b ^ 2) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    exact Finset.sum_le_sum fun q hq ↦
      Finset.sum_le_sum fun psi hpsi ↦ hone q hq psi
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * b ^ 2 =
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ((S q psi).card : ℝ) * (delta * eta) * b ^ 2 := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := hsum
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
          ∑ j ∈ Finset.Icc L J,
            ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨hq1, hqQ⟩ := Finset.mem_Ioc.mp hq
        exact Finset.mem_Ioc.mpr ⟨by omega, hqQ⟩
      · intro q hq hnot
        apply Finset.sum_nonneg
        intro psi hpsi
        apply Finset.sum_nonneg
        intro j hj
        exact intervalIntegral.integral_nonneg (by positivity)
          (fun u hu ↦ by positivity)
    _ = ∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          unweightedPrimitiveNegativeDirichletMass Q
            (Finset.Ioc (Y j) N) (c j) u := by
      calc
        (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
            ∑ j ∈ Finset.Icc L J,
              ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                ‖∑ n ∈ Finset.Ioc (Y j) N,
                  c j n * psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
          ∑ q ∈ Finset.Ioc 0 Q, ∑ j ∈ Finset.Icc L J,
            ∑ psi : primitiveCharacters q,
              ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                ‖∑ n ∈ Finset.Ioc (Y j) N,
                  c j n * psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]
        _ = ∑ j ∈ Finset.Icc L J, ∑ q ∈ Finset.Ioc 0 Q,
            ∑ psi : primitiveCharacters q,
              ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
                ‖∑ n ∈ Finset.Ioc (Y j) N,
                  c j n * psi.1 n *
                    Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
            rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          unfold unweightedPrimitiveNegativeDirichletMass
          rw [intervalIntegral.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro q hq
            rw [intervalIntegral.integral_finsetSum]
            intro psi hpsi
            exact (show Continuous (fun u : ℝ ↦
              ‖∑ n ∈ Finset.Ioc (Y j) N,
                c j n * psi.1 n *
                  Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖ ^ 2) by
                fun_prop).intervalIntegrable _ _
          · intro q hq
            exact (continuous_finsetSum _ fun psi hpsi ↦ by fun_prop).intervalIntegrable
              0 ((T + 1 : ℕ) : ℝ)

private theorem unweightedPrimitiveCutoffVonMangoldtEnergy_eq_characterSum
    (Q A N : ℕ) (t : ℝ) :
    unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t =
      ∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
            ‖∑ n ∈ Finset.Ioc A m,
              cutoffVonMangoldtCoefficient n * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
  classical
  unfold unweightedPrimitiveCutoffVonMangoldtEnergy
    unweightedPrimitiveNegativeDirichletMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]

theorem unweightedPrimitiveWeightedDetectorMass_le_two_endpoint_add_derivative
    (Q A N j : ℕ) {eta : ℝ} (hA : 0 < A) (hAN : A ≤ N) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
        (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t ≤
      2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t +
        2 * gallagherDerivativeVariation eta j A N *
          unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by
  classical
  let W : ℝ := |gallagherWeight eta (j - 1) N| ^ 2
  let D : ℝ := gallagherDerivativeVariation eta j A N
  let F : (q : ℕ) → primitiveCharacters q → ℝ := fun q psi ↦
    ‖∑ n ∈ Finset.Ioc A N,
      cutoffVonMangoldtCoefficient n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2
  let E : (q : ℕ) → primitiveCharacters q → ℝ := fun q psi ↦
    ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
      ‖∑ n ∈ Finset.Ioc A m,
        cutoffVonMangoldtCoefficient n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2
  have hone (q : ℕ) (psi : primitiveCharacters q) :
      ‖∑ n ∈ Finset.Ioc A N,
          (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤
        2 * W * F q psi + 2 * D * E q psi := by
    simpa only [W, D, F, E] using
      norm_weightedDetector_sq_le_two_endpoint_add_derivative
        psi.1 A N j hA hAN t
  unfold unweightedPrimitiveNegativeDirichletMass
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ Finset.Ioc A N,
            (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          (2 * W * F q psi + 2 * D * E q psi) := by
      exact Finset.sum_le_sum fun q hq ↦
        Finset.sum_le_sum fun psi hpsi ↦ hone q psi
    _ = 2 * W * (∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, F q psi) +
        2 * D * (∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, E q psi) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t +
        2 * gallagherDerivativeVariation eta j A N *
          unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by
      rw [unweightedPrimitiveCutoffVonMangoldtEnergy_eq_characterSum]
      unfold unweightedPrimitiveGallagherEndpointSquare
        unweightedPrimitiveNegativeDirichletMass
      change 2 * W * (∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, F q psi) +
        2 * D * (∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, E q psi) = _
      ring

theorem sum_selectedOrdinates_card_mul_le_two_unweightedEndpoint_add_derivativeEnergy
    (Q : ℕ) (Y : ℕ → ℕ)
    (N T L J : ℕ) (eta delta b : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hb : 0 ≤ b)
    (hYpos : ∀ j ∈ Finset.Icc L J, 0 < Y j)
    (hYN : ∀ j ∈ Finset.Icc L J, Y j ≤ N)
    (S : ∀ q : ℕ, primitiveCharacters q → Finset ℝ)
    (order : ∀ q : ℕ, primitiveCharacters q → ℝ → ℕ)
    (hS : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ x ∈ S q psi, ∀ y ∈ S q psi, x ≠ y →
        2 * delta * eta < dist x y)
    (horder : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, L ≤ order q psi t ∧ order q psi t ≤ J)
    (hlower : ∀ q ∈ Finset.Ioc 1 Q, ∀ psi : primitiveCharacters q,
      ∀ t ∈ S q psi, ∀ u : ℝ, |u - t| ≤ delta * eta →
        b ≤
          ‖∑ n ∈ Finset.Ioc (Y (order q psi t)) N,
            (weightedVonMangoldtMajorant eta
              (order q psi t - 1) n : ℂ) * psi.1 n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * b ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        ((2 * ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta u) +
        2 * gallagherDerivativeVariation eta j (Y j) N *
          (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N u)) := by
  let c : ℕ → ℕ → ℂ := fun j n ↦
    (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)
  have hselected :=
    sum_selectedOrdinates_card_mul_le_variableUnweightedPrimitiveMass
      Q Y c N T L J eta delta b heta heta1 hdelta hdelta1 hb S order
        hS hsep horder (by simpa only [c] using hlower)
  refine hselected.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hpoint : ∀ u : ℝ,
      unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
          (c j) u ≤
        2 * unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta u +
          2 * gallagherDerivativeVariation eta j (Y j) N *
            unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N u := by
    intro u
    simpa only [c] using
      unweightedPrimitiveWeightedDetectorMass_le_two_endpoint_add_derivative
        Q (Y j) N j (hYpos j hj) (hYN j hj) u
  have hendpointContinuous : Continuous
      (unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta) := by
    unfold unweightedPrimitiveGallagherEndpointSquare
    exact continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc (Y j) N) cutoffVonMangoldtCoefficient)
  have hcutContinuous : Continuous
      (unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N) := by
    unfold unweightedPrimitiveCutoffVonMangoldtEnergy
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc (Y j) m) cutoffVonMangoldtCoefficient)
  have hendpointIntegrable : IntervalIntegrable
      (fun u : ℝ ↦ 2 *
        unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta u)
      MeasureTheory.volume 0 ((T + 1 : ℕ) : ℝ) :=
    (continuous_const.mul hendpointContinuous).intervalIntegrable _ _
  have hderivativeIntegrable : IntervalIntegrable
      (fun u : ℝ ↦
        2 * gallagherDerivativeVariation eta j (Y j) N *
          unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N u)
      MeasureTheory.volume 0 ((T + 1 : ℕ) : ℝ) :=
    (continuous_const.mul hcutContinuous).intervalIntegrable _ _
  calc
    (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N)
          (c j) u) ≤
      ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        (2 * unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta u +
          2 * gallagherDerivativeVariation eta j (Y j) N *
            unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact (continuous_unweightedPrimitiveNegativeDirichletMass Q
          (Finset.Ioc (Y j) N) (c j)).intervalIntegrable _ _
      · exact ((continuous_const.mul hendpointContinuous).add
          (continuous_const.mul hcutContinuous)).intervalIntegrable _ _
      · intro u hu
        exact hpoint u
    _ = (2 * ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          unweightedPrimitiveGallagherEndpointSquare Q (Y j) N j eta u) +
        2 * gallagherDerivativeVariation eta j (Y j) N *
          (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
      rw [intervalIntegral.integral_add hendpointIntegrable hderivativeIntegrable,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

end Erdos48

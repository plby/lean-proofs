/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherGamma
import ErdosProblems.Erdos48.GallagherCutoffGlobalImproved
import ErdosProblems.Erdos48.GallagherUnweightedSelection
import BoundedGaps.BombieriVinogradov.Analytic.BilinearPerronAggregate

/-!
# Normalized Gallagher mean values

This file combines the factorial normalization of the variable zero detector
with Gallagher's endpoint-separated Abel estimate.  The derivative variation
is bounded by the Gamma moment from `GallagherGamma`; after normalization it
therefore carries the decisive factor `eta^3`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

/-- The finite derivative variation is dominated by its cutoff-independent
Gamma moment. -/
theorem gallagherDerivativeVariation_le_gammaBound
    {eta : ℝ} (heta : 0 < eta) (j : ℕ) {A N : ℕ}
    (hA : 2 ≤ A) (hAN : A ≤ N) :
    gallagherDerivativeVariation eta j A N ≤
      gallagherDerivativeGammaBound eta (j - 1) := by
  unfold gallagherDerivativeVariation
  calc
    (∑ m ∈ Finset.Ico A N, (m : ℝ) *
        |gallagherWeight eta (j - 1) m -
          gallagherWeight eta (j - 1) (m + 1)| ^ 2) ≤
      ∑ m ∈ Finset.Ico A N, (m : ℝ) *
        gallagherWeightSlopeMajorant eta (j - 1) m ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < m := by
        have := (Finset.mem_Ico.mp hm).1
        omega
      have hstep := abs_gallagherWeight_sub_succ_le
        heta.le (j - 1) hmpos
      gcongr
    _ = ∑ m ∈ Finset.Ico A N,
        gallagherLogDerivativeMajorant eta (j - 1) m ^ 2 *
          (m : ℝ) ^ (-2 * eta - 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact natCast_mul_gallagherWeightSlopeMajorant_sq
        eta (j - 1) (by
          have := (Finset.mem_Ico.mp hm).1
          omega)
    _ ≤ gallagherDerivativeGammaBound eta (j - 1) :=
      sum_Ico_gallagherLogDerivativeMajorant_sq_rpow_le_gammaBound
        (j - 1) hA hAN heta

/-- Scaling every coefficient by a nonnegative real scales the unweighted
primitive square mass by its square. -/
theorem unweightedPrimitiveNegativeDirichletMass_real_mul
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) :
    unweightedPrimitiveNegativeDirichletMass Q s
        (fun n ↦ (a : ℂ) * c n) t =
      a ^ 2 * unweightedPrimitiveNegativeDirichletMass Q s c t := by
  classical
  unfold unweightedPrimitiveNegativeDirichletMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ psi : primitiveCharacters q,
        ‖∑ n ∈ s, ((a : ℂ) * c n) * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
      ∑ psi : primitiveCharacters q,
        a ^ 2 * ‖∑ n ∈ s, c n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro psi hpsi
      have hsum :
          (∑ n ∈ s, ((a : ℂ) * c n) * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
            (a : ℂ) * ∑ n ∈ s, c n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
      ring
    _ = a ^ 2 * ∑ psi : primitiveCharacters q,
        ‖∑ n ∈ s, c n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- The variable detector normalization factors out of the unweighted
primitive mean square. -/
theorem unweightedPrimitiveNegativeDirichletMass_variableNormalized
    (Q : ℕ) (s : Finset ℕ) (eta : ℝ) (J j : ℕ) (t : ℝ)
    (heta : 0 ≤ eta) :
    unweightedPrimitiveNegativeDirichletMass Q s
        (variableNormalizedDetectorCoefficient eta J j) t =
      variableDetectorNormalization eta J j ^ 2 *
        unweightedPrimitiveNegativeDirichletMass Q s
          (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t := by
  change unweightedPrimitiveNegativeDirichletMass Q s
      (fun n ↦ (variableDetectorNormalization eta J j : ℂ) *
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t = _
  exact unweightedPrimitiveNegativeDirichletMass_real_mul Q s
    (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ))
    (variableDetectorNormalization eta J j) t
    (variableDetectorNormalization_nonneg heta J j)

/-- The total number of primitive characters through `Q`, without weights,
is at most `Q^2`. -/
theorem sum_card_primitiveCharacters_le_sq (Q : ℕ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (Fintype.card (primitiveCharacters q) : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (Fintype.card (primitiveCharacters q) : ℝ)) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          (Fintype.card (primitiveCharacters q) : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
      have hphi : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hw : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        (one_le_div hphi).2 (by exact_mod_cast Nat.totient_le q)
      have hcard : 0 ≤ (Fintype.card (primitiveCharacters q) : ℝ) := by
        positivity
      nlinarith
    _ ≤ (Q : ℝ) ^ 2 := sum_weighted_card_primitiveCharacters_le_sq Q

private theorem gallagherBaseCoefficient_eq_cutoff'
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (hn : 0 < n) :
    gallagherBaseCoefficient chi t n =
      cutoffVonMangoldtCoefficient n * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
  unfold gallagherBaseCoefficient cutoffVonMangoldtCoefficient
  rw [Real.rpow_neg_one]

/-- The terminal Abel contribution at the canonical exponential cutoff,
summed over all primitive characters, is exponentially small. -/
theorem unweightedPrimitiveGallagherEndpointSquare_zeroDetectorCutoff_le
    (Q A j : ℕ) {eta R : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hA : 0 < A) (hcut : A ≤ zeroDetectorCutoff R eta) (t : ℝ) :
    unweightedPrimitiveGallagherEndpointSquare Q A
        (zeroDetectorCutoff R eta) j eta t ≤
      (Q : ℝ) ^ 2 *
        ((6 * (Real.log 4 + 4) / eta) ^ 2 *
          Real.log (zeroDetectorCutoff R eta) ^ (2 * (j - 1)) *
            Real.exp (-R)) := by
  let E : ℝ := (6 * (Real.log 4 + 4) / eta) ^ 2 *
    Real.log (zeroDetectorCutoff R eta) ^ (2 * (j - 1)) * Real.exp (-R)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hone : ∀ q ∈ Finset.Ioc 0 Q, ∀ psi : primitiveCharacters q,
      |gallagherWeight eta (j - 1) (zeroDetectorCutoff R eta)| ^ 2 *
          ‖∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
            cutoffVonMangoldtCoefficient n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤ E := by
    intro q hq psi
    have hsum :
        (∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
            cutoffVonMangoldtCoefficient n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
          ∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
            gallagherBaseCoefficient psi.1 t n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (gallagherBaseCoefficient_eq_cutoff' psi.1 t
        (by have := (Finset.mem_Ioc.mp hn).1; omega)).symm
    rw [hsum]
    have hend := norm_gallagherAbelEndpoint_zeroDetectorCutoff_sq_le
      psi.1 t (j - 1) heta heta1 hA hcut
    dsimp only [E]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hend
    nlinarith [sq_nonneg
      (|gallagherWeight eta (j - 1) (zeroDetectorCutoff R eta)| *
        ‖∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
          gallagherBaseCoefficient psi.1 t n‖)]
  unfold unweightedPrimitiveGallagherEndpointSquare
    unweightedPrimitiveNegativeDirichletMass
  calc
    |gallagherWeight eta (j - 1) (zeroDetectorCutoff R eta)| ^ 2 *
        (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
            cutoffVonMangoldtCoefficient n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) =
      ∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
        (|gallagherWeight eta (j - 1) (zeroDetectorCutoff R eta)| ^ 2 *
          ‖∑ n ∈ Finset.Ioc A (zeroDetectorCutoff R eta),
            cutoffVonMangoldtCoefficient n * psi.1 n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q,
        ∑ _psi : primitiveCharacters q, E := by
      exact Finset.sum_le_sum fun q hq ↦
        Finset.sum_le_sum fun psi hpsi ↦ hone q hq psi
    _ = (∑ q ∈ Finset.Ioc 0 Q,
        (Fintype.card (primitiveCharacters q) : ℝ)) * E := by
      calc
        (∑ q ∈ Finset.Ioc 0 Q,
            ∑ _psi : primitiveCharacters q, E) =
          ∑ q ∈ Finset.Ioc 0 Q,
            (Fintype.card (primitiveCharacters q) : ℝ) * E := by
          apply Finset.sum_congr rfl
          intro q hq
          simp
        _ = (∑ q ∈ Finset.Ioc 0 Q,
            (Fintype.card (primitiveCharacters q) : ℝ)) * E := by
          rw [Finset.sum_mul]
    _ ≤ (Q : ℝ) ^ 2 * E :=
      mul_le_mul_of_nonneg_right (sum_card_primitiveCharacters_le_sq Q) hE
    _ = _ := by rfl

/-- Pointwise normalized Gallagher mean: the derivative term has already
been converted to the normalized Gamma coefficient and hence to `eta^3`. -/
theorem unweightedPrimitiveNegativeDirichletMass_normalized_le_endpoint_add_gamma
    (Q A N J j : ℕ) {eta : ℝ} (heta : 0 < eta)
    (hj : 2 ≤ j) (hA : 2 ≤ A) (hAN : A ≤ N) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
        (variableNormalizedDetectorCoefficient eta J j) t ≤
      variableDetectorNormalization eta J j ^ 2 *
          (2 * unweightedPrimitiveGallagherEndpointSquare
            Q A N j eta t) +
        2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
            unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by
  rw [unweightedPrimitiveNegativeDirichletMass_variableNormalized
    Q (Finset.Ioc A N) eta J j t heta.le]
  have hraw :=
    unweightedPrimitiveWeightedDetectorMass_le_two_endpoint_add_derivative
      Q A N j (eta := eta) (by omega) hAN t
  have hvar := gallagherDerivativeVariation_le_gammaBound
    heta j hA hAN
  have henergy : 0 ≤ unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by
    unfold unweightedPrimitiveCutoffVonMangoldtEnergy
      unweightedPrimitiveNegativeDirichletMass
    positivity
  have hnorm : 0 ≤ variableDetectorNormalization eta J j ^ 2 := sq_nonneg _
  calc
    variableDetectorNormalization eta J j ^ 2 *
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
          (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t ≤
      variableDetectorNormalization eta J j ^ 2 *
        (2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t +
          2 * gallagherDerivativeVariation eta j A N *
            unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t) :=
      mul_le_mul_of_nonneg_left hraw hnorm
    _ ≤ variableDetectorNormalization eta J j ^ 2 *
          (2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) +
        2 * (variableDetectorNormalization eta J j ^ 2 *
          gallagherDerivativeGammaBound eta (j - 1)) *
            unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by
      calc
        _ = variableDetectorNormalization eta J j ^ 2 *
              (2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) +
            2 * variableDetectorNormalization eta J j ^ 2 *
              gallagherDerivativeVariation eta j A N *
                unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t := by ring
        _ ≤ _ := by
          apply add_le_add le_rfl
          have hd : variableDetectorNormalization eta J j ^ 2 *
                gallagherDerivativeVariation eta j A N ≤
              variableDetectorNormalization eta J j ^ 2 *
                gallagherDerivativeGammaBound eta (j - 1) :=
            mul_le_mul_of_nonneg_left hvar hnorm
          have htwo : 2 *
                (variableDetectorNormalization eta J j ^ 2 *
                  gallagherDerivativeVariation eta j A N) ≤
              2 * (variableDetectorNormalization eta J j ^ 2 *
                gallagherDerivativeGammaBound eta (j - 1)) :=
            mul_le_mul_of_nonneg_left hd (by norm_num)
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right htwo henergy
    _ = _ := by
      rw [variableDetectorNormalization_sq_mul_gallagherDerivativeGammaBound
        heta J j hj]
      ring

/-- Interval-integrated form of the normalized Gallagher estimate.  This
form is arranged so that the amplified cutoff-energy theorem can be applied
directly to the second summand. -/
theorem intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le
    (Q A N T J j : ℕ) {eta : ℝ} (heta : 0 < eta)
    (hj : 2 ≤ j) (hA : 2 ≤ A) (hAN : A ≤ N) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      variableDetectorNormalization eta J j ^ 2 *
          (2 * ∫ t in (0 : ℝ)..(T : ℝ),
            unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) +
        2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
            (∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t) := by
  have hendpointContinuous : Continuous
      (unweightedPrimitiveGallagherEndpointSquare Q A N j eta) := by
    unfold unweightedPrimitiveGallagherEndpointSquare
    exact continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc A N) cutoffVonMangoldtCoefficient)
  have hcutContinuous : Continuous
      (unweightedPrimitiveCutoffVonMangoldtEnergy Q A N) := by
    unfold unweightedPrimitiveCutoffVonMangoldtEnergy
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc A m) cutoffVonMangoldtCoefficient)
  have hendpointIntegrable : IntervalIntegrable
      (fun t : ℝ ↦ variableDetectorNormalization eta J j ^ 2 *
        (2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t))
      MeasureTheory.volume 0 (T : ℝ) :=
    (continuous_const.mul (continuous_const.mul hendpointContinuous)).intervalIntegrable _ _
  have henergyIntegrable : IntervalIntegrable
      (fun t : ℝ ↦ 2 * eta ^ 3 *
        normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
          unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t)
      MeasureTheory.volume 0 (T : ℝ) :=
    (continuous_const.mul hcutContinuous).intervalIntegrable _ _
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      ∫ t in (0 : ℝ)..(T : ℝ),
        (variableDetectorNormalization eta J j ^ 2 *
            (2 * unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) +
          2 * eta ^ 3 *
            normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t) := by
        apply intervalIntegral.integral_mono_on (by positivity)
        · exact (continuous_unweightedPrimitiveNegativeDirichletMass Q
            (Finset.Ioc A N) (variableNormalizedDetectorCoefficient eta J j)).intervalIntegrable _ _
        · exact (hendpointIntegrable.add henergyIntegrable)
        · intro t ht
          exact unweightedPrimitiveNegativeDirichletMass_normalized_le_endpoint_add_gamma
            Q A N J j heta hj hA hAN t
    _ = _ := by
      rw [intervalIntegral.integral_add hendpointIntegrable henergyIntegrable,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- The integrated terminal Abel contribution at the canonical cutoff. -/
theorem intervalIntegral_unweightedPrimitiveGallagherEndpointSquare_zeroDetectorCutoff_le
    (Q A T j : ℕ) {eta R : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hA : 0 < A) (hcut : A ≤ zeroDetectorCutoff R eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveGallagherEndpointSquare Q A
          (zeroDetectorCutoff R eta) j eta t) ≤
      (T : ℝ) * ((Q : ℝ) ^ 2 *
        ((6 * (Real.log 4 + 4) / eta) ^ 2 *
          Real.log (zeroDetectorCutoff R eta) ^ (2 * (j - 1)) *
            Real.exp (-R))) := by
  let E : ℝ := (Q : ℝ) ^ 2 *
    ((6 * (Real.log 4 + 4) / eta) ^ 2 *
      Real.log (zeroDetectorCutoff R eta) ^ (2 * (j - 1)) * Real.exp (-R))
  have hcontinuous : Continuous
      (unweightedPrimitiveGallagherEndpointSquare Q A
        (zeroDetectorCutoff R eta) j eta) := by
    unfold unweightedPrimitiveGallagherEndpointSquare
    exact continuous_const.mul
      (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc A (zeroDetectorCutoff R eta)) cutoffVonMangoldtCoefficient)
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveGallagherEndpointSquare Q A
          (zeroDetectorCutoff R eta) j eta t) ≤
      ∫ _t in (0 : ℝ)..(T : ℝ), E := by
        apply intervalIntegral.integral_mono_on (by positivity)
        · exact hcontinuous.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro t ht
          exact unweightedPrimitiveGallagherEndpointSquare_zeroDetectorCutoff_le
            Q A j heta heta1 hA hcut t
    _ = (T : ℝ) * E := by
      simp [E]
      ring
    _ = _ := by rfl

/-- Explicit integral bound for the terminal Abel term. -/
noncomputable def gallagherCanonicalEndpointBound
    (Q T j : ℕ) (eta R : ℝ) : ℝ :=
  (T : ℝ) * ((Q : ℝ) ^ 2 *
    ((6 * (Real.log 4 + 4) / eta) ^ 2 *
      Real.log (zeroDetectorCutoff R eta) ^ (2 * (j - 1)) *
        Real.exp (-R)))

/-- The explicit right hand side in the amplified cutoff-energy theorem. -/
noncomputable def gallagherAmplifiedCutoffEnergyBound
    (L : ℝ) (Y N : ℕ) : ℝ :=
  (8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2 +
      8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
        gallagherHigherPrimePowerShellTail Y N) *
    ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹

/-- The amplified hybrid bound for one complete cutoff polynomial. -/
noncomputable def gallagherAmplifiedCutoffBandBound
    (L : ℝ) (Y N : ℕ) : ℝ :=
  8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
      ∑ a ∈ detectorActiveShells Y N,
        ((a + 1 : ℕ) : ℝ) * Real.log 2 +
    8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
      gallagherHigherPrimePowerShellTail Y N

/-- Fully amplified normalized Gallagher mean at the canonical cutoff.  The
rough-modulus coefficient remains on the left; the derivative term on the
right contains the small factor `eta^3`. -/
theorem mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le
    (Q Amp A T J j : ℕ) (L : ℝ) {eta R : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hj : 2 ≤ j)
    (hA : 2 ≤ A) (hcut : A ≤ zeroDetectorCutoff R eta)
    (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q Amp)
    (hheight : 4 * (T + 1) ≤ A)
    (hrough : Q * Amp ≤ A)
    (hroughConductor : 2 * ((T + 1) * (Q * Amp) ^ 2) ≤ A)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ A) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q
          (Finset.Ioc A (zeroDetectorCutoff R eta))
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      L * (variableDetectorNormalization eta J j ^ 2 *
        (2 * gallagherCanonicalEndpointBound Q T j eta R)) +
      (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
        gallagherAmplifiedCutoffEnergyBound L A
          (zeroDetectorCutoff R eta) := by
  have hmean :=
    intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le
      Q A (zeroDetectorCutoff R eta) T J j heta hj hA hcut
  have hendpoint :=
    intervalIntegral_unweightedPrimitiveGallagherEndpointSquare_zeroDetectorCutoff_le
      Q A T j heta heta1 (by omega) hcut
  have henergy := mul_intervalIntegral_unweightedPrimitiveCutoffEnergy_le
    Q Amp A (zeroDetectorCutoff R eta) T L hL hcoeff (by omega)
      hheight hrough hroughConductor hconductor
  have hnorm : 0 ≤ variableDetectorNormalization eta J j ^ 2 := sq_nonneg _
  have hgamma : 0 ≤
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) := by
    unfold normalizedGallagherDerivativeGammaCoefficient
    positivity
  have hderivative : 0 ≤ 2 * eta ^ 3 *
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) := by
    positivity
  calc
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q
          (Finset.Ioc A (zeroDetectorCutoff R eta))
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      L * (variableDetectorNormalization eta J j ^ 2 *
          (2 * ∫ t in (0 : ℝ)..(T : ℝ),
            unweightedPrimitiveGallagherEndpointSquare Q A
              (zeroDetectorCutoff R eta) j eta t) +
        2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
            (∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A
                (zeroDetectorCutoff R eta) t)) :=
      mul_le_mul_of_nonneg_left hmean hL
    _ ≤ L * (variableDetectorNormalization eta J j ^ 2 *
          (2 * gallagherCanonicalEndpointBound Q T j eta R) +
        2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
            (∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A
                (zeroDetectorCutoff R eta) t)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hnorm)
        le_rfl
    _ = L * (variableDetectorNormalization eta J j ^ 2 *
          (2 * gallagherCanonicalEndpointBound Q T j eta R)) +
        (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
            (L * ∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A
                (zeroDetectorCutoff R eta) t) := by ring
    _ ≤ L * (variableDetectorNormalization eta J j ^ 2 *
          (2 * gallagherCanonicalEndpointBound Q T j eta R)) +
        (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
            gallagherAmplifiedCutoffEnergyBound L A
              (zeroDetectorCutoff R eta) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by
          simpa only [gallagherAmplifiedCutoffEnergyBound] using henergy) hderivative)
    _ = _ := by rfl

/-- Amplified normalized Gallagher mean with the terminal Abel contribution
itself estimated by the rough hybrid large sieve.  This is the form used in
the log-free density theorem: it has no factor counting all characters. -/
theorem mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le_band
    (Q Amp A N T J j : ℕ) (L : ℝ) {eta : ℝ}
    (heta : 0 < eta) (hj : 2 ≤ j)
    (hA : 2 ≤ A) (hAN : A ≤ N)
    (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q Amp)
    (hheight : 4 * (T + 1) ≤ A)
    (hrough : Q * Amp ≤ A)
    (hroughConductor : 2 * ((T + 1) * (Q * Amp) ^ 2) ≤ A)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ A) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      (variableDetectorNormalization eta J j ^ 2 *
          (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
        gallagherAmplifiedCutoffBandBound L A N +
      (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
        gallagherAmplifiedCutoffEnergyBound L A N := by
  have hmean :=
    intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le
      Q A N T J j heta hj hA hAN
  have hband := mul_intervalIntegral_unweightedCutoff_adaptive_le
    Q Amp A N T L hL hcoeff (by omega) hheight hrough
      hroughConductor hconductor
  have henergy := mul_intervalIntegral_unweightedPrimitiveCutoffEnergy_le
    Q Amp A N T L hL hcoeff (by omega) hheight hrough
      hroughConductor hconductor
  have hendpointEq :
      (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) =
      |gallagherWeight eta (j - 1) N| ^ 2 *
        ∫ t in (0 : ℝ)..(T : ℝ),
          unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
            cutoffVonMangoldtCoefficient t := by
    unfold unweightedPrimitiveGallagherEndpointSquare
    rw [intervalIntegral.integral_const_mul]
  have hnorm : 0 ≤ variableDetectorNormalization eta J j ^ 2 := sq_nonneg _
  have hweight : 0 ≤ |gallagherWeight eta (j - 1) N| ^ 2 := sq_nonneg _
  have hgamma : 0 ≤
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) := by
    unfold normalizedGallagherDerivativeGammaCoefficient
    positivity
  have hderivative : 0 ≤ 2 * eta ^ 3 *
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) := by
    positivity
  have hendpointCoefficient : 0 ≤
      variableDetectorNormalization eta J j ^ 2 *
        (2 * |gallagherWeight eta (j - 1) N| ^ 2) := by positivity
  calc
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
          (variableNormalizedDetectorCoefficient eta J j) t) ≤
      L * (variableDetectorNormalization eta J j ^ 2 *
          (2 * ∫ t in (0 : ℝ)..(T : ℝ),
            unweightedPrimitiveGallagherEndpointSquare Q A N j eta t) +
        2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) *
            (∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t)) :=
      mul_le_mul_of_nonneg_left hmean hL
    _ = (variableDetectorNormalization eta J j ^ 2 *
          (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
            (L * ∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc A N)
                cutoffVonMangoldtCoefficient t) +
        (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
            (L * ∫ t in (0 : ℝ)..(T : ℝ),
              unweightedPrimitiveCutoffVonMangoldtEnergy Q A N t) := by
      rw [hendpointEq]
      ring
    _ ≤ (variableDetectorNormalization eta J j ^ 2 *
          (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
            gallagherAmplifiedCutoffBandBound L A N +
        (2 * eta ^ 3 *
          normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
            gallagherAmplifiedCutoffEnergyBound L A N := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by
          simpa only [gallagherAmplifiedCutoffBandBound,
            gallagherHigherPrimePowerShellTail] using hband)
          hendpointCoefficient
      · exact mul_le_mul_of_nonneg_left (by
          simpa only [gallagherAmplifiedCutoffEnergyBound] using henergy)
          hderivative
    _ = _ := by rfl

end Erdos48

end

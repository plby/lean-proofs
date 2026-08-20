/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableSelectedZeroBandMass
import ErdosProblems.Erdos48.GallagherDetectorWeight
import ErdosProblems.Erdos48.GallagherCutoffMean

/-!
# Gallagher cutoff-energy aggregation for selected zeros

This file combines the selected-ordinate counting inequality with finite
Abel summation.  It provides both the fixed-endpoint API, in which the full
variation factor multiplies Gallagher's cutoff energy, and the sharper
endpoint-separated API, in which the terminal Abel square is retained
separately and only the derivative variation multiplies the cutoff energy.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

/-- The exact finite variation factor attached to detector order `j`. -/
noncomputable def variableGallagherVariation
    (eta : ℝ) (j A N : ℕ) : ℝ :=
  gallagherWeightVariationFactor eta (j - 1) A N

/-- The variation contribution after Gallagher's upper endpoint has been
split off before Cauchy--Schwarz. -/
noncomputable def gallagherDerivativeVariation
    (eta : ℝ) (j A N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico A N, (m : ℝ) *
    |gallagherWeight eta (j - 1) m -
      gallagherWeight eta (j - 1) (m + 1)| ^ 2

/-- The primitive-character square of the upper endpoint in finite Abel
summation, including the terminal smooth weight. -/
noncomputable def primitiveGallagherEndpointSquare
    (Q A N j : ℕ) (eta t : ℝ) : ℝ :=
  |gallagherWeight eta (j - 1) N| ^ 2 *
    primitiveNegativeDirichletMass Q (Finset.Ioc A N)
      cutoffVonMangoldtCoefficient t

private theorem gallagherBaseCoefficient_eq_cutoff
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (_hn : 0 < n) :
    gallagherBaseCoefficient chi t n =
      cutoffVonMangoldtCoefficient n * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
  unfold gallagherBaseCoefficient cutoffVonMangoldtCoefficient
  rw [Real.rpow_neg_one]
private theorem weightedDetector_eq_gallagherAbelSum
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (A N j : ℕ) (eta t : ℝ) :
    (∑ n ∈ Finset.Ioc A N,
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
      ∑ n ∈ Finset.Ioc A N,
        gallagherBaseCoefficient chi t n *
          (gallagherWeight eta (j - 1) n : ℂ) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  exact (gallagherBaseCoefficient_mul_weight chi t eta (j - 1)
    (by have := (Finset.mem_Ioc.mp hn).1; omega : 0 < n)).symm

private theorem norm_weightedDetector_sq_le_cutoffEnergy_mul_variation
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (A N j : ℕ) {eta : ℝ} (hA : 0 < A) (hAN : A ≤ N) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc A N,
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
          ‖∑ n ∈ Finset.Ioc A m,
            cutoffVonMangoldtCoefficient n * chi n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) *
        variableGallagherVariation eta j A N := by
  rw [weightedDetector_eq_gallagherAbelSum]
  have h := norm_sum_Ioc_mul_sq_le_partialSumEnergy_mul_weightVariation
    (fun n ↦ gallagherBaseCoefficient chi t n)
    (fun n ↦ (gallagherWeight eta (j - 1) n : ℂ)) hA hAN
  have hbase (m : ℕ) (hm : m ∈ Finset.Icc A N) :
      (∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n) =
        ∑ n ∈ Finset.Ioc A m,
          cutoffVonMangoldtCoefficient n * chi n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact gallagherBaseCoefficient_eq_cutoff chi t
      (by have := (Finset.mem_Ioc.mp hn).1; omega)
  have henergy :
      (∑ m ∈ Finset.Icc A N,
          ‖∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n‖ ^ 2 /
            (m : ℝ)) =
        ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
          ‖∑ n ∈ Finset.Ioc A m,
            cutoffVonMangoldtCoefficient n * chi n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hbase m hm]
    ring
  have hvariation :
      ((N : ℝ) * ‖(gallagherWeight eta (j - 1) N : ℂ)‖ ^ 2 +
          ∑ m ∈ Finset.Ico A N,
            (m : ℝ) *
              ‖(gallagherWeight eta (j - 1) m : ℂ) -
                (gallagherWeight eta (j - 1) (m + 1) : ℂ)‖ ^ 2) =
        variableGallagherVariation eta j A N := by
    unfold variableGallagherVariation gallagherWeightVariationFactor
    congr 1
    · rw [Complex.norm_real, Real.norm_eq_abs]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [henergy, hvariation] at h
  exact h

theorem norm_weightedDetector_sq_le_two_endpoint_add_derivative
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (A N j : ℕ) {eta : ℝ} (hA : 0 < A) (hAN : A ≤ N) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc A N,
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤
      2 * |gallagherWeight eta (j - 1) N| ^ 2 *
          ‖∑ n ∈ Finset.Ioc A N,
            cutoffVonMangoldtCoefficient n * chi n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 +
        2 * gallagherDerivativeVariation eta j A N *
          (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
            ‖∑ n ∈ Finset.Ioc A m,
              cutoffVonMangoldtCoefficient n * chi n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
  rw [weightedDetector_eq_gallagherAbelSum]
  let P : ℕ → ℂ := fun m ↦
    ∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n
  let w : ℕ → ℂ := fun m ↦ (gallagherWeight eta (j - 1) m : ℂ)
  rw [sum_Ioc_mul_eq_prefix_mul_add_sum_prefix_mul_sub
    (fun n ↦ gallagherBaseCoefficient chi t n) w hAN]
  have hadd :
      ‖P N * w N + ∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖ ^ 2 ≤
        2 * ‖P N * w N‖ ^ 2 +
          2 * ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖ ^ 2 := by
    have hnorm := norm_add_le (P N * w N)
      (∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1)))
    have ha : 0 ≤ ‖P N * w N‖ := norm_nonneg _
    have hb : 0 ≤ ‖∑ m ∈ Finset.Ico A N,
        P m * (w m - w (m + 1))‖ := norm_nonneg _
    calc
      _ ≤ (‖P N * w N‖ +
          ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖) ^ 2 := by
        gcongr
      _ ≤ 2 * ‖P N * w N‖ ^ 2 +
          2 * ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖ ^ 2 := by
        nlinarith [sq_nonneg (‖P N * w N‖ -
          ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖)]
  have hpos : ∀ m ∈ Finset.Ico A N, 0 < (m : ℝ) := by
    intro m hm
    exact_mod_cast hA.trans_le (Finset.mem_Ico.mp hm).1
  have hcauchy := norm_sum_mul_sq_le_weighted
    (Finset.Ico A N) (fun m ↦ (m : ℝ)) hpos P
      (fun m ↦ w m - w (m + 1))
  have henergy :
      (∑ m ∈ Finset.Ico A N, ‖P m‖ ^ 2 / (m : ℝ)) ≤
        ∑ m ∈ Finset.Icc A N, ‖P m‖ ^ 2 / (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2.le⟩
    · intro m hmBig hmSmall
      positivity
  have hvariation :
      (∑ m ∈ Finset.Ico A N, (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2) =
        gallagherDerivativeVariation eta j A N := by
    unfold gallagherDerivativeVariation w
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hderiv :
      ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖ ^ 2 ≤
        (∑ m ∈ Finset.Icc A N, ‖P m‖ ^ 2 / (m : ℝ)) *
          gallagherDerivativeVariation eta j A N := by
    refine hcauchy.trans ?_
    rw [hvariation]
    apply mul_le_mul_of_nonneg_right henergy
    unfold gallagherDerivativeVariation
    positivity
  have hbase (m : ℕ) :
      P m = ∑ n ∈ Finset.Ioc A m,
        cutoffVonMangoldtCoefficient n * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact gallagherBaseCoefficient_eq_cutoff chi t
      (by have := (Finset.mem_Ioc.mp hn).1; omega)
  calc
    _ ≤ 2 * ‖P N * w N‖ ^ 2 +
        2 * ‖∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1))‖ ^ 2 := hadd
    _ ≤ 2 * ‖P N * w N‖ ^ 2 +
        2 * ((∑ m ∈ Finset.Icc A N, ‖P m‖ ^ 2 / (m : ℝ)) *
          gallagherDerivativeVariation eta j A N) := by gcongr
    _ = 2 * |gallagherWeight eta (j - 1) N| ^ 2 *
          ‖∑ n ∈ Finset.Ioc A N,
            cutoffVonMangoldtCoefficient n * chi n *
              Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 +
        2 * gallagherDerivativeVariation eta j A N *
          (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
            ‖∑ n ∈ Finset.Ioc A m,
              cutoffVonMangoldtCoefficient n * chi n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      simp only [hbase, w, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        div_eq_inv_mul]
      ring

private theorem primitiveCutoffVonMangoldtEnergy_eq_characterSum
    (Q A N : ℕ) (t : ℝ) :
    primitiveCutoffVonMangoldtEnergy Q A N t =
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
              ‖∑ n ∈ Finset.Ioc A m,
                cutoffVonMangoldtCoefficient n * psi.1 n *
                  Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
  classical
  unfold primitiveCutoffVonMangoldtEnergy primitiveNegativeDirichletMass
  let F : ℕ → (q : ℕ) → primitiveCharacters q → ℝ := fun m q psi ↦
    ‖∑ n ∈ Finset.Ioc A m,
      cutoffVonMangoldtCoefficient n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2
  calc
    (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q, F m q psi) =
      ∑ m ∈ Finset.Icc A N,
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q,
            (m : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ)) * F m q psi := by
        apply Finset.sum_congr rfl
        intro m hm
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro psi hpsi
        ring
    _ = ∑ q ∈ Finset.Ioc 0 Q,
        ∑ m ∈ Finset.Icc A N,
          ∑ psi : primitiveCharacters q,
            (m : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ)) * F m q psi := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.Ioc 0 Q,
        ∑ psi : primitiveCharacters q,
          ∑ m ∈ Finset.Icc A N,
            (m : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ)) * F m q psi := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ * F m q psi := by
      apply Finset.sum_congr rfl
      intro q hq
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi hpsi
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by rfl

theorem primitiveWeightedDetectorMass_le_gallagherCutoffEnergy
    (Q A N j : ℕ) {eta : ℝ} (hA : 0 < A) (hAN : A ≤ N) (t : ℝ) :
    primitiveNegativeDirichletMass Q (Finset.Ioc A N)
        (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t ≤
      variableGallagherVariation eta j A N *
        primitiveCutoffVonMangoldtEnergy Q A N t := by
  classical
  unfold primitiveNegativeDirichletMass
  have hsum :
      (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ‖∑ n ∈ Finset.Ioc A N,
                (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                  Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) ≤
        variableGallagherVariation eta j A N *
          ∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q,
                ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
                  ‖∑ n ∈ Finset.Ioc A m,
                    cutoffVonMangoldtCoefficient n * psi.1 n *
                      Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    calc
      (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc A N,
              (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ((∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
                ‖∑ n ∈ Finset.Ioc A m,
                  cutoffVonMangoldtCoefficient n * psi.1 n *
                    Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) *
              variableGallagherVariation eta j A N) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro psi hpsi
            exact norm_weightedDetector_sq_le_cutoffEnergy_mul_variation
              psi.1 A N j hA hAN t
          · positivity
      _ = variableGallagherVariation eta j A N *
          ((q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q,
              ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
                ‖∑ n ∈ Finset.Ioc A m,
                  cutoffVonMangoldtCoefficient n * psi.1 n *
                    Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
        rw [← Finset.sum_mul]
        ring
  rw [primitiveCutoffVonMangoldtEnergy_eq_characterSum]
  exact hsum

/-- Primitive-character aggregation of the endpoint-separated Abel bound. -/
theorem primitiveWeightedDetectorMass_le_two_endpoint_add_derivative
    (Q A N j : ℕ) {eta : ℝ} (hA : 0 < A) (hAN : A ≤ N) (t : ℝ) :
    primitiveNegativeDirichletMass Q (Finset.Ioc A N)
        (fun n ↦ (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)) t ≤
      2 * primitiveGallagherEndpointSquare Q A N j eta t +
        2 * gallagherDerivativeVariation eta j A N *
          primitiveCutoffVonMangoldtEnergy Q A N t := by
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
  have hq (q : ℕ) :
      (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc A N,
              (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 ≤
        2 * W * ((q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q, F q psi) +
        2 * D * ((q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q, E q psi) := by
    calc
      _ ≤ (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            (2 * W * F q psi + 2 * D * E q psi) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun psi hpsi ↦ hone q psi
        · positivity
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
        ring
  unfold primitiveNegativeDirichletMass
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc A N,
              (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * psi.1 n *
                Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (2 * W * ((q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q, F q psi) +
          2 * D * ((q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q, E q psi)) :=
      Finset.sum_le_sum fun q hqmem ↦ hq q
    _ = 2 * W *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, F q psi) +
        2 * D *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, E q psi) := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
    _ = 2 * primitiveGallagherEndpointSquare Q A N j eta t +
        2 * gallagherDerivativeVariation eta j A N *
          primitiveCutoffVonMangoldtEnergy Q A N t := by
      rw [primitiveCutoffVonMangoldtEnergy_eq_characterSum]
      unfold primitiveGallagherEndpointSquare
      change 2 * W *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, F q psi) +
        2 * D *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, E q psi) =
        2 * (W *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, F q psi)) +
        2 * D *
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, E q psi)
      ring

/-- Selected detected ordinates, aggregated over primitive characters, are
controlled by Gallagher's cutoff energy times the exact order-dependent
finite variation factor. -/
theorem sum_selectedOrdinates_card_mul_le_variableGallagherCutoffEnergy
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
            (weightedVonMangoldtMajorant eta (order q psi t - 1) n : ℂ) *
              psi.1 n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * b ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        variableGallagherVariation eta j (Y j) N *
          (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
  let c : ℕ → ℕ → ℂ := fun j n ↦
    (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)
  have hselected := sum_selectedOrdinates_card_mul_le_variablePrimitiveMass
    Q Y c N T L J eta delta b heta heta1 hdelta hdelta1 hb S order
      hS hsep horder (by simpa only [c] using hlower)
  refine hselected.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hpoint : ∀ u : ℝ,
      primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N) (c j) u ≤
        variableGallagherVariation eta j (Y j) N *
          primitiveCutoffVonMangoldtEnergy Q (Y j) N u := by
    intro u
    simpa only [c] using
      primitiveWeightedDetectorMass_le_gallagherCutoffEnergy
        Q (Y j) N j (hYpos j hj) (hYN j hj) u
  have hcutContinuous : Continuous
      (primitiveCutoffVonMangoldtEnergy Q (Y j) N) := by
    unfold primitiveCutoffVonMangoldtEnergy
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (continuous_primitiveNegativeDirichletMass Q
        (Finset.Ioc (Y j) m) cutoffVonMangoldtCoefficient)
  calc
    (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N) (c j) u) ≤
      ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        variableGallagherVariation eta j (Y j) N *
          primitiveCutoffVonMangoldtEnergy Q (Y j) N u := by
        apply intervalIntegral.integral_mono_on (by positivity)
        · exact (continuous_primitiveNegativeDirichletMass Q
            (Finset.Ioc (Y j) N) (c j)).intervalIntegrable
              0 ((T + 1 : ℕ) : ℝ)
        · exact (continuous_const.mul hcutContinuous).intervalIntegrable
            0 ((T + 1 : ℕ) : ℝ)
        · intro u hu
          exact hpoint u
    _ = variableGallagherVariation eta j (Y j) N *
        (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
      rw [intervalIntegral.integral_const_mul]

/-- Endpoint-separated selected-ordinate aggregation.  The first summand is
the square of the terminal Abel term; only the derivative variation multiplies
the complete logarithmic cutoff energy. -/
theorem sum_selectedOrdinates_card_mul_le_two_endpoint_add_derivativeEnergy
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
            (weightedVonMangoldtMajorant eta (order q psi t - 1) n : ℂ) *
              psi.1 n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))‖) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ((S q psi).card : ℝ)) * (delta * eta) * b ^ 2 ≤
      ∑ j ∈ Finset.Icc L J,
        (2 * (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveGallagherEndpointSquare Q (Y j) N j eta u) +
          2 * gallagherDerivativeVariation eta j (Y j) N *
            (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
              primitiveCutoffVonMangoldtEnergy Q (Y j) N u)) := by
  let c : ℕ → ℕ → ℂ := fun j n ↦
    (weightedVonMangoldtMajorant eta (j - 1) n : ℂ)
  have hselected := sum_selectedOrdinates_card_mul_le_variablePrimitiveMass
    Q Y c N T L J eta delta b heta heta1 hdelta hdelta1 hb S order
      hS hsep horder (by simpa only [c] using hlower)
  refine hselected.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hpoint : ∀ u : ℝ,
      primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N) (c j) u ≤
        2 * primitiveGallagherEndpointSquare Q (Y j) N j eta u +
          2 * gallagherDerivativeVariation eta j (Y j) N *
            primitiveCutoffVonMangoldtEnergy Q (Y j) N u := by
    intro u
    simpa only [c] using
      primitiveWeightedDetectorMass_le_two_endpoint_add_derivative
        Q (Y j) N j (hYpos j hj) (hYN j hj) u
  have hendpointContinuous : Continuous
      (primitiveGallagherEndpointSquare Q (Y j) N j eta) := by
    unfold primitiveGallagherEndpointSquare
    exact continuous_const.mul
      (continuous_primitiveNegativeDirichletMass Q
        (Finset.Ioc (Y j) N) cutoffVonMangoldtCoefficient)
  have hcutContinuous : Continuous
      (primitiveCutoffVonMangoldtEnergy Q (Y j) N) := by
    unfold primitiveCutoffVonMangoldtEnergy
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (continuous_primitiveNegativeDirichletMass Q
        (Finset.Ioc (Y j) m) cutoffVonMangoldtCoefficient)
  have hendpointIntegrable : IntervalIntegrable
      (fun u : ℝ ↦ 2 *
        primitiveGallagherEndpointSquare Q (Y j) N j eta u)
      MeasureTheory.volume 0 ((T + 1 : ℕ) : ℝ) :=
    (continuous_const.mul hendpointContinuous).intervalIntegrable _ _
  have hderivativeIntegrable : IntervalIntegrable
      (fun u : ℝ ↦
        2 * gallagherDerivativeVariation eta j (Y j) N *
          primitiveCutoffVonMangoldtEnergy Q (Y j) N u)
      MeasureTheory.volume 0 ((T + 1 : ℕ) : ℝ) :=
    (continuous_const.mul hcutContinuous).intervalIntegrable _ _
  calc
    (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc (Y j) N) (c j) u) ≤
      ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
        (2 * primitiveGallagherEndpointSquare Q (Y j) N j eta u +
          2 * gallagherDerivativeVariation eta j (Y j) N *
            primitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
        apply intervalIntegral.integral_mono_on (by positivity)
        · exact (continuous_primitiveNegativeDirichletMass Q
            (Finset.Ioc (Y j) N) (c j)).intervalIntegrable
              0 ((T + 1 : ℕ) : ℝ)
        · exact ((continuous_const.mul hendpointContinuous).add
            (continuous_const.mul hcutContinuous)).intervalIntegrable
              0 ((T + 1 : ℕ) : ℝ)
        · intro u hu
          exact hpoint u
    _ = 2 * (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          primitiveGallagherEndpointSquare Q (Y j) N j eta u) +
        2 * gallagherDerivativeVariation eta j (Y j) N *
          (∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            primitiveCutoffVonMangoldtEnergy Q (Y j) N u) := by
      rw [intervalIntegral.integral_add hendpointIntegrable hderivativeIntegrable,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

end Erdos48

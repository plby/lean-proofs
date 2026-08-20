/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherUnweightedSelection

/-!
# Amplified mean square for Gallagher's complete cutoff

The von Mangoldt cutoff is split into its prime and higher-prime-power
parts.  The prime part receives the Bombieri--Davenport logarithmic gain;
the prime-power remainder is controlled by the sharp Chebyshev error.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

theorem unweightedPrimitiveNegativeDirichletMass_le_primitive
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletMass Q s c t ≤
      primitiveNegativeDirichletMass Q s c t := by
  classical
  unfold unweightedPrimitiveNegativeDirichletMass
    primitiveNegativeDirichletMass
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
  have htotPos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hw : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
    (one_le_div htotPos).2 (by exact_mod_cast Nat.totient_le q)
  have hsum0 : 0 ≤ ∑ psi : primitiveCharacters q,
      ‖∑ n ∈ s, c n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 := by
    positivity
  nlinarith

theorem intervalIntegral_unweightedHigherPrimePower_adaptive_le
    (Q Y N T : ℕ) (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ Y) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          higherPrimePowerCutoffCoefficient t) ≤
      4 * Real.exp 2 * (1 + 16 * Real.pi) *
        ∑ a ∈ detectorActiveShells Y N,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              ((2 ^ a : ℕ) : ℝ)⁻¹) := by
  let C : ℝ := 2 * Real.exp 2 * (1 + 16 * Real.pi)
  have hpoint : ∀ t : ℝ,
      unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          higherPrimePowerCutoffCoefficient t ≤
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          higherPrimePowerCutoffCoefficient t :=
    fun t ↦ unweightedPrimitiveNegativeDirichletMass_le_primitive
      Q (Finset.Ioc Y N) higherPrimePowerCutoffCoefficient t
  have hmono :
      (∫ t in (0 : ℝ)..(T : ℝ),
          unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            higherPrimePowerCutoffCoefficient t) ≤
        ∫ t in (0 : ℝ)..(T : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            higherPrimePowerCutoffCoefficient t := by
    apply intervalIntegral.integral_mono_on (by positivity)
    · exact (continuous_unweightedPrimitiveNegativeDirichletMass Q
        (Finset.Ioc Y N) higherPrimePowerCutoffCoefficient).intervalIntegrable _ _
    · exact (continuous_primitiveNegativeDirichletMass Q
        (Finset.Ioc Y N) higherPrimePowerCutoffCoefficient).intervalIntegrable _ _
    · intro t ht
      exact hpoint t
  have hmain :=
    intervalIntegral_primitiveNegativeDirichletMass_adaptive_optimized_le
      Q Y N T hY hheight hconductor higherPrimePowerCutoffCoefficient
  have hterm : ∀ a ∈ detectorActiveShells Y N,
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖higherPrimePowerCutoffCoefficient n‖ ^ 2 ≤
        2 * ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹) := by
    intro a ha
    have henergy := sum_detectorDyadicShell_higherPrimePower_energy_le
      Y N a hY
    have hApos : (0 : ℝ) < (2 ^ a : ℕ) := by positivity
    calc
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖higherPrimePowerCutoffCoefficient n‖ ^ 2 ≤
        ((2 ^ a : ℕ) : ℝ) *
          (2 * ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2) *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              (((2 ^ a : ℕ) : ℝ)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hApos.le
      _ = 2 * ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
          Real.sqrt (2 * (2 ^ a : ℕ)) *
            ((2 ^ a : ℕ) : ℝ)⁻¹) := by
        field_simp
  have hsum :
      (∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ detectorDyadicShell Y N a,
              ‖higherPrimePowerCutoffCoefficient n‖ ^ 2) ≤
        2 * ∑ a ∈ detectorActiveShells Y N,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              ((2 ^ a : ℕ) : ℝ)⁻¹) := by
    calc
      _ ≤ ∑ a ∈ detectorActiveShells Y N,
          2 * ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              ((2 ^ a : ℕ) : ℝ)⁻¹) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(T : ℝ),
          primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
            higherPrimePowerCutoffCoefficient t := hmono
    _ ≤ C * ∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ detectorDyadicShell Y N a,
              ‖higherPrimePowerCutoffCoefficient n‖ ^ 2 := by
      simpa only [C] using hmain
    _ ≤ C * (2 * ∑ a ∈ detectorActiveShells Y N,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              ((2 ^ a : ℕ) : ℝ)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hsum (by dsimp [C]; positivity)
    _ = 4 * Real.exp 2 * (1 + 16 * Real.pi) *
        ∑ a ∈ detectorActiveShells Y N,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
            Real.sqrt (2 * (2 ^ a : ℕ)) *
              ((2 ^ a : ℕ) : ℝ)⁻¹) := by
      dsimp [C]
      ring

theorem unweightedPrimitiveNegativeDirichletMass_cutoff_le_prime_add_higher
    (Q : ℕ) (s : Finset ℕ) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletMass Q s
        cutoffVonMangoldtCoefficient t ≤
      2 * unweightedPrimitiveNegativeDirichletMass Q s
          primeCutoffCoefficient t +
        2 * unweightedPrimitiveNegativeDirichletMass Q s
          higherPrimePowerCutoffCoefficient t := by
  classical
  unfold unweightedPrimitiveNegativeDirichletMass
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
        ‖∑ n ∈ s, cutoffVonMangoldtCoefficient n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) ≤
      ∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
        (2 * ‖∑ n ∈ s, primeCutoffCoefficient n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2 +
        2 * ‖∑ n ∈ s, higherPrimePowerCutoffCoefficient n * psi.1 n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro psi hpsi
      rw [cutoffPolynomial_eq_prime_add_higher]
      let x : ℂ := ∑ n ∈ s, primeCutoffCoefficient n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))
      let y : ℂ := ∑ n ∈ s, higherPrimePowerCutoffCoefficient n * psi.1 n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))
      have hnorm := norm_add_le x y
      have hx : 0 ≤ ‖x‖ := norm_nonneg x
      have hy : 0 ≤ ‖y‖ := norm_nonneg y
      have hsquare : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        calc
          ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by gcongr
          _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
            nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
      simpa only [x, y] using hsquare
    _ = 2 * (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s, primeCutoffCoefficient n * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) +
        2 * (∑ q ∈ Finset.Ioc 0 Q, ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s, higherPrimePowerCutoffCoefficient n * psi.1 n *
            Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem mul_intervalIntegral_unweightedCutoff_adaptive_le
    (Q A Y N T : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hrough : Q * A ≤ Y)
    (hroughConductor : 2 * ((T + 1) * (Q * A) ^ 2) ≤ Y)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ Y) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          cutoffVonMangoldtCoefficient t) ≤
      8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
          ∑ a ∈ detectorActiveShells Y N,
            ((a + 1 : ℕ) : ℝ) * Real.log 2 +
        8 * L * Real.exp 2 * (1 + 16 * Real.pi) *
          ∑ a ∈ detectorActiveShells Y N,
            ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
              Real.sqrt (2 * (2 ^ a : ℕ)) *
                ((2 ^ a : ℕ) : ℝ)⁻¹) := by
  let F := unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
    cutoffVonMangoldtCoefficient
  let P := unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
    primeCutoffCoefficient
  let H := unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
    higherPrimePowerCutoffCoefficient
  have hpoint : ∀ t : ℝ, F t ≤ 2 * P t + 2 * H t := by
    intro t
    exact unweightedPrimitiveNegativeDirichletMass_cutoff_le_prime_add_higher
      Q (Finset.Ioc Y N) t
  have hsplit :
      (∫ t in (0 : ℝ)..(T : ℝ), F t) ≤
        2 * (∫ t in (0 : ℝ)..(T : ℝ), P t) +
          2 * (∫ t in (0 : ℝ)..(T : ℝ), H t) := by
    have hPint : IntervalIntegrable (fun t : ℝ ↦ 2 * P t)
        MeasureTheory.volume 0 T :=
      (continuous_const.mul
        (continuous_unweightedPrimitiveNegativeDirichletMass Q
          (Finset.Ioc Y N) primeCutoffCoefficient)).intervalIntegrable _ _
    have hHint : IntervalIntegrable (fun t : ℝ ↦ 2 * H t)
        MeasureTheory.volume 0 T :=
      (continuous_const.mul
        (continuous_unweightedPrimitiveNegativeDirichletMass Q
          (Finset.Ioc Y N) higherPrimePowerCutoffCoefficient)).intervalIntegrable _ _
    calc
      _ ≤ ∫ t in (0 : ℝ)..(T : ℝ), (2 * P t + 2 * H t) := by
        apply intervalIntegral.integral_mono_on (by positivity)
        · exact (continuous_unweightedPrimitiveNegativeDirichletMass Q
            (Finset.Ioc Y N) cutoffVonMangoldtCoefficient).intervalIntegrable _ _
        · exact ((continuous_const.mul
            (continuous_unweightedPrimitiveNegativeDirichletMass Q
              (Finset.Ioc Y N) primeCutoffCoefficient)).add
            (continuous_const.mul
              (continuous_unweightedPrimitiveNegativeDirichletMass Q
                (Finset.Ioc Y N)
                  higherPrimePowerCutoffCoefficient))).intervalIntegrable _ _
        · intro t ht
          exact hpoint t
      _ = _ := by
        rw [intervalIntegral.integral_add hPint hHint,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hprime := mul_intervalIntegral_primeCutoff_adaptive_le
    Q A Y N T L hL hcoeff hY hheight hrough hroughConductor
  have hhigher := intervalIntegral_unweightedHigherPrimePower_adaptive_le
    Q Y N T hY hheight hconductor
  have hnonnegP : 0 ≤ ∫ t in (0 : ℝ)..(T : ℝ), P t :=
    intervalIntegral.integral_nonneg (by positivity) (fun t ht ↦ by
      dsimp [P, unweightedPrimitiveNegativeDirichletMass]
      positivity)
  have hnonnegH : 0 ≤ ∫ t in (0 : ℝ)..(T : ℝ), H t :=
    intervalIntegral.integral_nonneg (by positivity) (fun t ht ↦ by
      dsimp [H, unweightedPrimitiveNegativeDirichletMass]
      positivity)
  calc
    L * (∫ t in (0 : ℝ)..(T : ℝ), F t) ≤
        L * (2 * (∫ t in (0 : ℝ)..(T : ℝ), P t) +
          2 * (∫ t in (0 : ℝ)..(T : ℝ), H t)) :=
      mul_le_mul_of_nonneg_left hsplit hL
    _ = 2 * (L * (∫ t in (0 : ℝ)..(T : ℝ), P t)) +
        2 * L * (∫ t in (0 : ℝ)..(T : ℝ), H t) := by ring
    _ ≤ 2 * (4 * Real.exp 2 * (1 + 16 * Real.pi) *
          (Real.log 4 + 4) *
            ∑ a ∈ detectorActiveShells Y N,
              ((a + 1 : ℕ) : ℝ) * Real.log 2) +
        2 * L * (4 * Real.exp 2 * (1 + 16 * Real.pi) *
          ∑ a ∈ detectorActiveShells Y N,
            ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2 *
              Real.sqrt (2 * (2 ^ a : ℕ)) *
                ((2 ^ a : ℕ) : ℝ)⁻¹)) := by
      gcongr
    _ = _ := by ring

end Erdos48

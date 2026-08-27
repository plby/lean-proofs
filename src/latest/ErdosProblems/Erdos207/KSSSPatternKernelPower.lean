/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternPowerRequirements
import ErdosProblems.Erdos207.PatternRelativeCenteredMoments
import ErdosProblems.Erdos207.NeighborPowerScale

/-! # Actual power-scale kernel bounds for relative extension counts -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.pattern_relative_kernel_power
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (Q : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (req : KSSSPatternPowerRequirements q b B k Rmin (graphSupportFinset Q).card (graphEdges Q).card t coeff)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (time : ℕ) (S : GreedyStateOn V) (hS : GreedyInvariant F S)
    (hactive : KSSSPowerActive F Q₀ q b B k t a E A time S)
    (hR : (patternSurvivalSelectors Q S).Nonempty) (sigma J : ℝ) (hsigma : |sigma| = 1) (hJ : 1 ≤ J)
    (hY : ((properPatternExtensions S.available Q U).card : ℝ) ≤
      2 * ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card time)
    (hLoss : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J) :
    let target := ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card
    let envelope := relativePatternEnvelope E t (ksssPowerErrorExponent b B) B
    let obs := patternRelativeCenteredObservable Q U target envelope sigma
    let d := b * (graphSupportFinset Q).card + (graphEdges Q).card
    (∀ T ∈ patternSurvivalSelectors Q S, |obs ((time : ℝ) + 1) (greedyStep F S T) - obs time S| ≤
      (t : ℝ) ^ (d + 1) * J / U.card) ∧
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal
      (fun S' ↦ obs ((time : ℝ) + 1) S' - obs time S) ≤ 0 ∧
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal
      (fun S' ↦ (obs ((time : ℝ) + 1) S' - obs time S) ^ 2) ≤
        (t : ℝ) ^ (d + 2 * b + 1) * J / ((U.card : ℝ) * (Fintype.card V : ℝ) ^ 2) := by
  let N : ℝ := Fintype.card V
  let M : ℝ := U.card
  let h := (graphSupportFinset Q).card
  let m := (graphEdges Q).card
  let s := ksssPowerErrorExponent b B
  let d := b * h + m
  let R := ksssPowerDenominatorExponent q b B k Rmin
  let L := E * ksssEdgeDensity E time
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let e := ksssErrorEnvelope E (N / (t : ℝ) ^ s) B time
  let f := ksssPatternTrajectory (ksssOrders q) a E M h m time
  let G := ksssPatternHazardCoefficient q coeff h m
  let C : ℝ := patternHazardErrorCoefficient q h m
  let D := ksssPatternStepCoefficient q coeff h m
  have hNpos : 0 < N := by
    have hn : (1 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast P.ambient_pos
    linarith
  have hMpos : 0 < M := by dsimp only [M]; exact_mod_cast card_pos.mpr hU
  have hMN : M ≤ N := by dsimp only [M, N]; exact_mod_cast card_le_univ U
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by linarith [P.scale_large])
  have htpos : (0 : ℝ) < t := by linarith
  have hscale : (t : ℝ) ^ R ≤ N := by dsimp only [R, N]; exact_mod_cast P.power_scale
  have hscalar := P.scalar_bounds time (Nat.cast_nonneg _) hactive.2.2.2
  have hp := ksssEdgeDensity_pos P.edge_pos hscalar.clock_strict
  have hLpos : 0 < L := mul_pos P.edge_pos hp
  have hx : 0 < x := ksssPairTrajectory_pos _ _ P.edge_pos P.available_pos hscalar.clock_strict
  have he : 0 ≤ e := by dsimp only [e, ksssErrorEnvelope]; positivity
  have hb : ∀ i ∈ ksssOrders q, 0 ≤ coeff i := fun i hi ↦
    (mul_nonneg (P.coefficient_nonneg i hi) (pow_nonneg P.edge_pos.le i)).trans (P.coefficient_bound i hi)
  have hG : 0 ≤ G := ksssPatternHazardCoefficient_nonneg q coeff h m hb
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hD : 0 ≤ D := by dsimp only [D, ksssPatternStepCoefficient]; linarith only [hG]
  have hCscale : ksssPatternTaylorCoefficient q coeff h m * (t : ℝ) ^ (d + s) ≤ E :=
    (coeff_power_le_ambient_power_ratio N t (ksssPatternTaylorCoefficient q coeff h m) R 2 (d + s) b
      ht1 hNpos.le hscale req.taylor_coefficient (by
        have hh := req.taylor_exponent
        dsimp only [d, s, R, h, m]
        omega)).trans P.edge_floor
  have hdet := ksssPatternTrajectory_relative_deterministic_bounds q b B h m a coeff E A M time t
    P.edge_pos P.available_pos hMpos ht1 (Nat.cast_nonneg _) (by linarith [hscalar.unit_clock])
    P.coefficient_nonneg P.coefficient_bound P.coefficient_budget.poisson hactive.2.2.2 hCscale
    (req.target_step_coefficient.trans hscalar.clock_base)
  have hsize : (m : ℝ) * N ≤ L * e / 3 :=
    pattern_selector_size_power_budget N t L e m R s b ht1 hNpos.le hscale req.selector_coefficient
      req.selector_exponent hscalar.clock_lower hscalar.error_base
  have hden := hactive.2.1.pattern_selector_bounds hactive.1 P.edge_pos hp he hscalar.error_small Q hsize
  have hKnat : 1 ≤ t ^ (k + 1) := Nat.one_le_pow _ _ (by linarith [P.scale_large])
  have hKreal : ((t ^ (k + 1) : ℕ) : ℝ) ≤ e := by
    simpa only [Nat.cast_pow] using hscalar.overlap_error
  have hcutoff : (t : ℝ≥0) ^ k ≤ t ^ (k + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ t by linarith [P.scale_large])) (Nat.le_succ k)
  have hpairK : (dyadicCrudeThresholds V t k).pair ≤ (t ^ (k + 1) : ℕ) := by
    simpa only [dyadicCrudeThresholds, Nat.cast_pow] using hcutoff
  have hcommonK : (dyadicCrudeThresholds V t k).common ≤ (t ^ (k + 1) : ℕ) := by
    simpa only [dyadicCrudeThresholds, Nat.cast_pow] using hcutoff
  have hdrift := hactive.2.1.pattern_relative_centered_drift hactive.1 hactive.2.2.1 hS P.packing
    P.order_bound P.edge_pos P.available_pos htpos (Nat.cast_nonneg _) (by linarith [hscalar.unit_clock])
    P.coefficient_nonneg P.coefficient_bound hratio P.coefficient_budget.poisson
    (t ^ (k + 1)) hKnat hpairK hcommonK hKreal hscalar.error_small Q U hU sigma hsigma hR hsize
    hY hdet.1 req.drift_coefficient hdet.2.2
  have hf : 0 < f := ksssPatternTrajectory_pos _ _ _ _ _ _ _ hMpos hp
  have hfLower : M / (t : ℝ) ^ d ≤ f :=
    ksssPatternTrajectory_power_lower (ksssOrders q) a coeff E M time t h m b hMpos.le htpos
      (Nat.cast_nonneg _) (by linarith [hscalar.clock_strict]) P.coefficient_nonneg P.coefficient_bound
      P.coefficient_budget.poisson hactive.2.2.2
  have hfM : f ≤ M := ksssPatternTrajectory_le_size _ _ _ _ _ _ _ P.edge_pos hMpos.le
    (Nat.cast_nonneg _) hscalar.clock_strict P.coefficient_nonneg
  have hNpower : (t : ℝ) ^ (2 * b) ≤ N := (pow_le_pow_right₀ ht1 req.clock_exponent).trans hscale
  have hNL : N ≤ L := by
    apply le_trans _ hscalar.clock_lower
    apply (le_div_iff₀ (pow_pos htpos (2 * b))).mpr
    have hpN := mul_le_mul_of_nonneg_left hNpower hNpos.le
    nlinarith only [hpN]
  have hHazard : ∀ u ∈ properPatternExtensions S.available Q U,
      ((patternExtensionKillers F Q U S u).card : ℝ) ≤ (G + C) * x := by
    intro u hu
    have hlocal := hactive.2.1.pattern_hazard_error hactive.2.2.1 hS P.packing P.order_bound
      hactive.1.cover (t ^ (k + 1)) hKnat hpairK hcommonK hKreal Q U u hu
    have hH := (ksssPatternHazardTrajectory_bounds q a coeff E A time h m P.edge_pos P.available_pos
      (Nat.cast_nonneg _) hscalar.clock_strict P.coefficient_nonneg P.coefficient_bound).2
    have hupper := (abs_le.mp hlocal).2
    have heX : e ≤ x := by linarith only [hscalar.error_small, hx]
    have hCe := mul_le_mul_of_nonneg_left heX hC
    have hHupper := (le_abs_self _).trans hH
    change ((patternExtensionKillers F Q U S u).card : ℝ) -
      ksssPatternHazardTrajectory q a E A h m time ≤ C * e at hupper
    change ksssPatternHazardTrajectory q a E A h m time ≤ G * x at hHupper
    nlinarith only [hupper, hCe, hHupper]
  have hmoment := restrictedGreedyKernel_pattern_relative_centered_moments F Q U S hR
    (ksssPatternTrajectory (ksssOrders q) a E M h m) (relativePatternEnvelope E t s B)
    sigma time L x J (G + C) D 16 hsigma hf hdet.1 hY (hfM.trans (hMN.trans hNL)) hx hJ
    (add_nonneg hG hC) hD (by norm_num) hden.2 hLoss hHazard hdet.2.1
    (relativePatternEnvelope_unitStep_abs_le_clock E t time b B P.edge_pos ht1 req.density_exponent
      hscalar.unit_clock hactive.2.2.2 req.envelope_coefficient)
  have hpower := relative_pattern_clock_moments_power_bounds N M f L t J
    (ksssPatternJumpCoefficient q coeff h m) (ksssPatternVarianceCoefficient q coeff h m) d b
    hNpos hMpos htpos (by linarith only [hJ]) hfLower hscalar.clock_lower req.jump_coefficient req.variance_coefficient
  exact ⟨fun T hT ↦ (hmoment.1 T hT).trans hpower.1, hdrift, hmoment.2.trans hpower.2⟩

end

end Erdos207

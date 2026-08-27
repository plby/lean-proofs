/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSResidualGeometrySupport
import ErdosProblems.Erdos207.KSSSPowerTrajectoryFailure

/-! # Explicit deterministic input data for the coupled power-scale process -/

namespace Erdos207

open Finset

noncomputable section

structure KSSSPowerParameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (q n b B k t Rmin : ℕ) (a coeff : ℕ → ℝ) (E A : ℝ) : Prop where
  minimal : minimalForbiddenFamily F = F
  packing : ∀ D ∈ F, IsPackingOn D
  order_bound : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q
  edge_pos : 0 < E
  available_pos : 0 < A
  ambient_pos : 1 ≤ Fintype.card V
  scale_large : 32 ≤ t
  binomial_budget : 2 ^ q ≤ t
  order_budget : q ≤ t
  power_scale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V
  horizon : n ≤ Fintype.card V ^ 2
  edge_floor : (Fintype.card V : ℝ) ^ 2 / (t : ℝ) ^ b ≤ E
  ratio_lower : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E
  ratio_upper : A / E ≤ (Fintype.card V : ℝ)
  density_floor : ∀ i : ℕ, i ≤ n → 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E i
  coefficient_nonneg : ∀ d ∈ ksssOrders q, 0 ≤ a d
  coefficient_bound : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d
  coefficient_budget : KSSSPowerCoefficientBounds q coeff B t
  envelope_order : 4 * q ≤ B
  pair_budget : ksssPairDriftCoefficient q coeff + ksssPairTaylorCoefficient (ksssOrders q) coeff ≤ 3 * (B : ℝ)
  configuration_budget : ∀ i : CrudeOrderIndex q 4, ksssIndexedConfigurationDriftCoefficient q coeff i +
    ksssConfigurationTaylorCoefficient (ksssOrders q) coeff (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}

theorem KSSSPowerParameters.kernelBounds
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (sigma : ℝ) (hsigma : |sigma| = 1) :
    KSSSIndexedKernelPowerBounds q n F (KSSSPowerActive F Q₀ q b B k t a E A) Q₀ a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B sigma
      (Fintype.card V) t (ksssPowerJumpExponent b k) (ksssPowerVarianceExponent b k) :=
  ksssPowerActive_kernelBounds q n b B k t Rmin F Q₀ a coeff E A sigma P.minimal P.packing P.order_bound
    P.edge_pos P.available_pos P.ambient_pos P.scale_large P.binomial_budget P.order_budget hsigma
    P.power_scale P.edge_floor P.ratio_lower P.ratio_upper (fun i hi ↦ P.density_floor i hi.le)
    P.coefficient_nonneg P.coefficient_bound P.coefficient_budget P.envelope_order P.pair_budget
    P.configuration_budget

theorem KSSSPowerParameters.available_floor
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (i : ℕ) (S : GreedyStateOn V)
    (hactive : KSSSPowerActive F Q₀ q b B k t a E A i S) :
    dyadicMomentFloor (Fintype.card V) t (5 * b + 1) ≤ S.available.card :=
  hactive.available_floor P.edge_pos P.available_pos P.ambient_pos P.scale_large P.power_scale
    P.edge_floor P.ratio_lower P.ratio_upper P.coefficient_nonneg P.coefficient_bound P.coefficient_budget

theorem KSSSPowerParameters.trajectory_failure
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (eta : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hQ₀ : ∀ Q ∈ Q₀, Q.card = 2)
    (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (KSSSPowerActive F Q₀ q b B k t a E A) S₀).probability
      (fun w ↦ ¬ KSSSOnTrajectories F w.2 q (ksssResidualPairs Q₀ w.2) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B w.1.1) : ℝ) ≤
      2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t := by
  obtain ⟨_, hj, hH, hR, _⟩ := ksss_power_exponent_hierarchy q b B k Rmin
  have hbudget := initial_regularity_power_margin_budget (Fintype.card V) t (A / E) eta
    (ksssPowerErrorExponent b B) (Nat.cast_nonneg _) (by exact_mod_cast (show 0 < t by linarith [P.scale_large]))
    (div_nonneg P.available_pos.le P.edge_pos.le) heta P.ratio_upper hetaSmall
  exact probability_ksss_trajectory_failure_power q n F (KSSSPowerActive F Q₀ q b B k t a E A)
    S₀ Q₀ a E A eta (Fintype.card V) B t (ksssPowerDenominatorExponent q b B k Rmin)
    (ksssPowerErrorExponent b B) b (ksssPowerThetaExponent q b B k)
    (ksssPowerJumpExponent b k) (ksssPowerVarianceExponent b k)
    (by exact_mod_cast P.ambient_pos) (by linarith [P.scale_large]) (by exact_mod_cast P.power_scale)
    (by exact_mod_cast P.horizon) P.ratio_lower hj hH hR hInv₀ hchosen₀ hQ₀ hregular hfamily
    P.edge_pos P.available_pos.le heta hbudget (P.kernelBounds Q₀ 1 (by norm_num))
    (P.kernelBounds Q₀ (-1) (by norm_num))

end

end Erdos207

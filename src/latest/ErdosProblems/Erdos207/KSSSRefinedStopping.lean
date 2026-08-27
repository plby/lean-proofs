/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerCrudeFailure

/-! # Coupled estimates remain valid with additional auxiliary stopping conditions -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSIndexedKernelPowerBounds.mono_active
    {V : Type*} [Fintype V] [DecidableEq V] {q n : ℕ}
    {F : ForbiddenFamilyOn V} {active refined : ℕ → GreedyStateOn V → Prop}
    {Q₀ : Finset (Finset V)} {a : ℕ → ℝ} {E A scale sigma N : ℝ} {B t j v : ℕ}
    (h : KSSSIndexedKernelPowerBounds q n F active Q₀ a E A scale B sigma N t j v)
    (hrefined : ∀ i S, refined i S → active i S) :
    KSSSIndexedKernelPowerBounds q n F refined Q₀ a E A scale B sigma N t j v := by
  exact ⟨fun i hi S hS ha ↦ h.available i hi S hS (hrefined i S ha),
    fun i hi S hS ha ↦ h.jump i hi S hS (hrefined i S ha),
    fun i hi S hS ha ↦ h.drift i hi S hS (hrefined i S ha),
    fun i hi S hS ha ↦ h.second i hi S hS (hrefined i S ha)⟩

theorem KSSSPowerParameters.trajectory_failure_of_active_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (eta : ℝ)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hQ₀ : ∀ Q ∈ Q₀, Q.card = 2)
    (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ¬ KSSSOnTrajectories F w.2 q (ksssResidualPairs Q₀ w.2) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B w.1.1) : ℝ) ≤
      2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t := by
  obtain ⟨_, hj, hH, hR, _⟩ := ksss_power_exponent_hierarchy q b B k Rmin
  have hbudget := initial_regularity_power_margin_budget (Fintype.card V) t (A / E) eta
    (ksssPowerErrorExponent b B) (Nat.cast_nonneg _)
    (by exact_mod_cast (show 0 < t by linarith [P.scale_large]))
    (div_nonneg P.available_pos.le P.edge_pos.le) heta P.ratio_upper hetaSmall
  exact probability_ksss_trajectory_failure_power q n F active
    S₀ Q₀ a E A eta (Fintype.card V) B t (ksssPowerDenominatorExponent q b B k Rmin)
    (ksssPowerErrorExponent b B) b (ksssPowerThetaExponent q b B k)
    (ksssPowerJumpExponent b k) (ksssPowerVarianceExponent b k)
    (by exact_mod_cast P.ambient_pos) (by linarith [P.scale_large]) (by exact_mod_cast P.power_scale)
    (by exact_mod_cast P.horizon) P.ratio_lower hj hH hR hInv₀ hchosen₀ hQ₀ hregular hfamily
    P.edge_pos P.available_pos.le heta hbudget
    ((P.kernelBounds Q₀ 1 (by norm_num)).mono_active hactive)
    ((P.kernelBounds Q₀ (-1) (by norm_num)).mono_active hactive)

theorem KSSSPowerParameters.crude_failure_of_active_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (bank : TripleSystemOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (c bankPower aPower : ℕ) (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hbank : bank.card + 1 ≤ c * t ^ bankPower)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : bankPower * (2 * q) + 1 ≤ aPower)
    (hk : k = dyadicCrudeExponent q aPower (5 * b + 2)) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ¬ CrudeStateBounds F w.2 q (dyadicCrudeThresholds V t k)) : ℝ) ≤
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ t := by
  obtain ⟨_, _, _, _, _, _, _, hfloorGap, _, _⟩ := ksss_power_exponent_hierarchy q b B k Rmin
  have hsize := momentFloor_size_of_power_scale (Fintype.card V) t
    (ksssPowerDenominatorExponent q b B k Rmin) (5 * b + 1)
    (by linarith [P.scale_large]) P.power_scale (by omega)
  have hraw := timedStoppedAbsorber_power_bank_crude_tail n F active S₀ bank q t c bankPower aPower (5 * b + 1)
    hF hInv₀ hchosen₀ P.ambient_pos P.scale_large P.horizon hsize
    (fun i S ha ↦ P.available_floor Q₀ i S (hactive i S ha)) hconst hbank hcoeff hgap
  have hexp : 5 * b + 1 + 1 = 5 * b + 2 := by omega
  rw [hexp, ← hk] at hraw
  exact_mod_cast hraw

end

end Erdos207

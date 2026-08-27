/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerParameters
import ErdosProblems.Erdos207.PowerAbsorberCrudeCoefficients

/-! # The actual crude failure bound for the coupled active event -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSPowerParameters.crude_failure
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (bank : TripleSystemOn V)
    (c bankPower aPower : ℕ) (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hbank : bank.card + 1 ≤ c * t ^ bankPower)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : bankPower * (2 * q) + 1 ≤ aPower)
    (hk : k = dyadicCrudeExponent q aPower (5 * b + 2)) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (KSSSPowerActive F Q₀ q b B k t a E A) S₀).probability
      (fun w ↦ ¬ CrudeStateBounds F w.2 q (dyadicCrudeThresholds V t k)) : ℝ) ≤
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ t := by
  obtain ⟨_, _, _, _, _, _, _, hfloorGap, _, _⟩ := ksss_power_exponent_hierarchy q b B k Rmin
  have hsize := momentFloor_size_of_power_scale (Fintype.card V) t
    (ksssPowerDenominatorExponent q b B k Rmin) (5 * b + 1)
    (by linarith [P.scale_large]) P.power_scale (by omega)
  have hraw := timedStoppedAbsorber_power_bank_crude_tail n F
    (KSSSPowerActive F Q₀ q b B k t a E A) S₀ bank q t c bankPower aPower (5 * b + 1)
    hF hInv₀ hchosen₀ P.ambient_pos P.scale_large P.horizon hsize
    (fun i S hactive ↦ P.available_floor Q₀ i S hactive) hconst hbank hcoeff hgap
  have hexp : 5 * b + 1 + 1 = 5 * b + 2 := by omega
  rw [hexp, ← hk] at hraw
  exact_mod_cast hraw

end

end Erdos207

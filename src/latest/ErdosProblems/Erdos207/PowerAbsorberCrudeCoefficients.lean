/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCrudeCoefficientPolynomial
import ErdosProblems.Erdos207.PowerBankSubsetAbsorption
import ErdosProblems.Erdos207.DyadicStoppedCrudeTail

/-! # Discharging the four crude coefficient budgets from a power-sized bank -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem absorber_crude_coefficients_le_power
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (bank : TripleSystemOn V) (t c b a : ℕ)
    (ht : 1 ≤ t) (hbank : bank.card + 1 ≤ c * t ^ b)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : b * (2 * q) + 1 ≤ a) :
    (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q bank ≤ (t : ℝ≥0) ^ a ∧
      (pairTwoAwayThreatExtensionCoefficient q bank : ℝ≥0) ≤ (t : ℝ≥0) ^ a ∧
      absorberCommonThreatWeightBound q bank ≤ (t : ℝ≥0) ^ a ∧
      absorberGainDefectWeightBound q bank ≤ (t : ℝ≥0) ^ a := by
  have hnat : absorberCrudeBankCoefficient q * (bank.card + 1) ^ (2 * q) ≤ t ^ a := by
    calc
      _ ≤ absorberCrudeBankCoefficient q * (c * t ^ b) ^ (2 * q) := by gcongr
      _ = (absorberCrudeBankCoefficient q * c ^ (2 * q)) * t ^ (b * (2 * q)) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ _ := coeff_mul_pow_le_pow ht hcoeff hgap
  have hbound : (absorberCrudeBankCoefficient q : ℝ≥0) * (bank.card + 1 : ℝ≥0) ^ (2 * q) ≤
      (t : ℝ≥0) ^ a := by exact_mod_cast hnat
  obtain ⟨hr, hp, hc, hg⟩ := absorber_crude_coefficients_le_bank_polynomial q bank
  exact ⟨hr.trans hbound, hp.trans hbound, hc.trans hbound, hg.trans hbound⟩

def powerAbsorberCrudeCoefficient (q : ℕ) : ℕ :=
  absorberCrudeBankCoefficient q * (powerAbsorberCoefficient q ^ 3 + 1) ^ (2 * q)

def powerAbsorberCrudeExponent (q rootPower : ℕ) : ℕ :=
  (3 * (156 * rootPower)) * (2 * q) + 1

theorem InitialPowerVortexPackage.bank_card_add_one_le_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) :
    P.B.card + 1 ≤ (powerAbsorberCoefficient q ^ 3 + 1) * t ^ (3 * (156 * rootPower)) := by
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have hbank : P.B.card ≤ (c * t ^ b) ^ 3 := by
    simpa only [c, b, highGirthAbsorber_power_normalize] using P.bankCard
  have hpow : 1 ≤ t ^ (3 * b) := Nat.one_le_pow _ _ P.base_ge_one
  calc
    P.B.card + 1 ≤ (c * t ^ b) ^ 3 + 1 := Nat.add_le_add_right hbank 1
    _ = c ^ 3 * t ^ (3 * b) + 1 := by rw [mul_pow, ← pow_mul]; simp only [Nat.mul_comm b 3]
    _ ≤ c ^ 3 * t ^ (3 * b) + t ^ (3 * b) := Nat.add_le_add_left hpow _
    _ = _ := by dsimp only [c, b]; ring

theorem InitialPowerVortexPackage.crude_coefficients_le_power
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hcoeff : powerAbsorberCrudeCoefficient q ≤ t) :
    (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q P.B ≤
        (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower ∧
      (pairTwoAwayThreatExtensionCoefficient q P.B : ℝ≥0) ≤
        (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower ∧
      absorberCommonThreatWeightBound q P.B ≤
        (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower ∧
      absorberGainDefectWeightBound q P.B ≤
        (t : ℝ≥0) ^ powerAbsorberCrudeExponent q rootPower := by
  exact absorber_crude_coefficients_le_power q P.B t (powerAbsorberCoefficient q ^ 3 + 1)
    (3 * (156 * rootPower)) (powerAbsorberCrudeExponent q rootPower)
    P.base_ge_one P.bank_card_add_one_le_power hcoeff le_rfl

theorem eventually_powerAbsorberCrudeCoefficient_le_scale (q R : ℕ) (hR : 0 < R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → powerAbsorberCrudeCoefficient q ≤ dyadicPowerScale R n :=
  eventually_le_dyadicPowerScale hR (powerAbsorberCrudeCoefficient q)

theorem timedStoppedAbsorber_power_bank_crude_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (steps : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (bank : TripleSystemOn V) (q t c b a floorPower : ℕ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hN : 1 ≤ Fintype.card V) (ht : 32 ≤ t) (hsteps : steps ≤ Fintype.card V ^ 2)
    (hsize : 8 * t ^ floorPower ≤ Fintype.card V ^ 3)
    (hfloor : ∀ i S, active i S → dyadicMomentFloor (Fintype.card V) t floorPower ≤ S.available.card)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hbank : bank.card + 1 ≤ c * t ^ b)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : b * (2 * q) + 1 ≤ a) :
    (FiniteLaw.timedStoppedProcessLaw steps (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ CrudeStateBounds F z.2 q
        (dyadicCrudeThresholds V t (dyadicCrudeExponent q a (floorPower + 1)))) ≤
      4 * (q + 1 : ℝ≥0) ^ 2 * (Fintype.card V + 1 : ℝ≥0) ^ 6 * (1 / 2 : ℝ≥0) ^ t := by
  obtain ⟨hr, hp, hc, hg⟩ := absorber_crude_coefficients_le_power q bank t c b a
    (by omega) hbank hcoeff hgap
  exact timedStoppedAbsorber_dyadic_crude_tail steps F active S₀ bank q t a floorPower
    hF hInv₀ hchosen₀ hN ht hsteps hsize hfloor hconst hr hp hc hg

end

end Erdos207

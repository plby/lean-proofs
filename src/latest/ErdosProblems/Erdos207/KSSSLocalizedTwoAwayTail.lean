/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayStateBounds
import ErdosProblems.Erdos207.KSSSRefinedStopping

/-! # Localized cutoffs on the actual refined KSSS stopped law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.localized_twoAway_failure
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (H : SimpleGraph V) (bank : TripleSystemOn V) (X : Finset V) (sets : I → Finset V) (r : ℕ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hsep : ∀ i, AbsorberSeparatedLevel H X bank (sets i))
    (hrootLocal : HasPaddedAbsorberRootLocalization q X bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅) (hU : ∀ i, (sets i).Nonempty)
    (hsize : ∀ i, (45 * (q + 1) + 28 : ℕ) * (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1) ≤ ((sets i).card : ℝ≥0))
    (hbank : pairExactBankExtensionCoefficient q bank * (t : ℝ≥0) ^ (r + q * (5 * b + 3) + 1) ≤
      (Fintype.card V + 1 : ℝ≥0))
    (hconst : (4 * (q + 1) ^ (q + 2) : ℕ) ≤ t) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ AllLocalizedTwoAwayBounds F sets
        (fun i ↦ ((sets i).card : ℝ≥0) / (t : ℝ≥0) ^ r) z.2) : ℝ) ≤
      (Fintype.card I : ℝ) * (Fintype.card V : ℝ) ^ 5 * (1 / 2 : ℝ) ^ t := by
  obtain ⟨_, _, _, _, _, _, _, hfloorGap, _, _⟩ := ksss_power_exponent_hierarchy q b B k Rmin
  have hfloorSize := momentFloor_size_of_power_scale (Fintype.card V) t
    (ksssPowerDenominatorExponent q b B k Rmin) (5 * b + 1)
    (by linarith [P.scale_large]) P.power_scale (by omega)
  have htpos : 0 < t := by linarith [P.scale_large]
  have hw : (1 : ℝ≥0) ≤ (t : ℝ≥0) ^ (5 * b + 2) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ t by omega))
  have hratio := dyadicMomentFloor_joint_ratio (Fintype.card V) t (5 * b + 1) n
    P.ambient_pos P.scale_large P.horizon hfloorSize
  have h := timedStoppedAbsorber_allLocalizedTwoAway_relative_power_tail n F active
    (dyadicMomentFloor (Fintype.card V) t (5 * b + 1)) S₀ q t r (5 * b + 2) H bank X sets
    ((t : ℝ≥0) ^ (5 * b + 2)) hF hsep hrootLocal hInv₀ hchosen₀
    (dyadicMomentFloor_pos _ _ _ htpos hfloorSize) hw (by omega) hU
    (fun i S ha ↦ P.available_floor Q₀ i S (hactive i S ha))
    (by convert hratio using 1 <;> congr 2 <;> omega) le_rfl
    (by simpa only [show 5 * b + 2 + 1 = 5 * b + 3 by omega] using hsize)
    (by simpa only [show 5 * b + 2 + 1 = 5 * b + 3 by omega] using hbank) hconst
  exact_mod_cast h

end

end Erdos207

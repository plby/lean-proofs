/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerCrudeFailure
import ErdosProblems.Erdos207.TimedStoppedTwoEventSuccess

/-! # Reaching the horizon from explicit regular initial data

This theorem combines the two bounds for the same frozen law. The initial
regularity and absorber-family hypotheses remain explicit mathematical inputs.
-/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSPowerParameters.exists_good_horizon
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (bank : TripleSystemOn V)
    (c bankPower aPower : ℕ) (eta : ℝ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hEcard : (Q₀.card : ℝ) = E) (hQ₀ : ∀ Q ∈ Q₀, Q.card = 2)
    (hcover : ∀ T ∈ S₀.available, ∀ Q : Finset V, Q.card = 2 → Q ⊆ T.1 → Q ∈ Q₀)
    (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hbank : bank.card + 1 ≤ c * t ^ bankPower)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : bankPower * (2 * q) + 1 ≤ aPower)
    (hk : k = dyadicCrudeExponent q aPower (5 * b + 2))
    (hsmall : (2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) +
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6) * (1 / 2 : ℝ) ^ t < 1) :
    ∃ S : GreedyStateOn V, GreedyInvariant F S ∧ GreedyContainedIn S₀.available S ∧
      S.chosen.card = n ∧
      KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B n ∧
      CrudeStateBounds F S q (dyadicCrudeThresholds V t k) := by
  let active := KSSSPowerActive F Q₀ q b B k t a E A
  let band := fun i : ℕ ↦ fun S : GreedyStateOn V ↦
    KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B i
  let crude := fun _ : ℕ ↦ fun S : GreedyStateOn V ↦ CrudeStateBounds F S q (dyadicCrudeThresholds V t k)
  have havailable := (P.kernelBounds Q₀ 1 (by norm_num)).available
  have hgeometry := timedStoppedGreedy_supported_residualGeometry n F active S₀ Q₀ E
    hInv₀ hchosen₀ P.edge_pos hEcard hQ₀ hcover havailable
  have hcounter := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv₀ hchosen₀ havailable
  have hband := P.trajectory_failure Q₀ S₀ eta hInv₀ hchosen₀ hQ₀ hregular hfamily heta hetaSmall
  have hcrude := P.crude_failure Q₀ S₀ bank c bankPower aPower hF hInv₀ hchosen₀
    hconst hbank hcoeff hgap hk
  obtain ⟨w, hw, htime, hbands, hcrudes⟩ :=
    FiniteLaw.exists_timedStopped_horizon_of_two_failure_bounds n (fun _ ↦ greedyKernel F)
      active band crude S₀ _ _ hband hcrude (by simpa only [add_mul] using hsmall)
      (fun w hw hband hcrude ↦ ⟨hgeometry w hw, hband, hcrude,
        P.density_floor w.1.1 (Nat.le_of_lt_succ w.1.isLt)⟩)
  have hs := hcounter w hw
  refine ⟨w.2, hs.1.1, hs.1.2, hs.2.trans htime, ?_, hcrudes⟩
  simpa only [band, htime] using hbands

end

end Erdos207

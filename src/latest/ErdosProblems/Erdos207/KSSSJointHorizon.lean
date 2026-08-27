/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointStoppedStateSuccess
import ErdosProblems.Erdos207.KSSSDensityHorizon

/-! # Ordinary coupled horizon success with a retrospective joint crude bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.restrict_horizon
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n m b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A) (hm : m ≤ n) :
    KSSSPowerParameters F q m b B k t Rmin a coeff E A :=
  { P with horizon := hm.trans P.horizon
           density_floor := fun i hi ↦ P.density_floor i (hi.trans hm) }

theorem ksssDensityHorizon_antitone_density
    (E delta epsilon : ℝ) (hE : 0 ≤ E) (hde : delta ≤ epsilon) :
    ksssDensityHorizon E epsilon ≤ ksssDensityHorizon E delta := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hde 1) hE) (by norm_num)

theorem ksssDensityHorizon_power_mono_exponent
    (E t : ℝ) (c b : ℕ) (hE : 0 ≤ E) (ht : 1 ≤ t) (hcb : c ≤ b) :
    ksssDensityHorizon E (1 / t ^ c) ≤ ksssDensityHorizon E (1 / t ^ b) := by
  apply ksssDensityHorizon_antitone_density E _ _ hE
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ ht hcb)

theorem KSSSPowerParameters.earlier_density_horizon
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q b B k t Rmin c : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q (ksssDensityHorizon E (1 / (t : ℝ) ^ b)) b B k t Rmin a coeff E A)
    (hcb : c ≤ b) :
    KSSSPowerParameters F q (ksssDensityHorizon E (1 / (t : ℝ) ^ c)) b B k t Rmin a coeff E A ∧
      (∀ i : ℕ, i ≤ ksssDensityHorizon E (1 / (t : ℝ) ^ c) → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) := by
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by linarith [P.scale_large])
  have hpow : 1 ≤ (t : ℝ) ^ c := one_le_pow₀ ht
  have hpos : (0 : ℝ) < (t : ℝ) ^ c := zero_lt_one.trans_le hpow
  exact ⟨P.restrict_horizon (ksssDensityHorizon_power_mono_exponent E t c b P.edge_pos.le ht hcb),
    (ksssDensityHorizon_bounds E (1 / (t : ℝ) ^ c) P.edge_pos (by positivity)
      ((div_le_one hpos).mpr hpow)).2.1⟩

theorem ksss_joint_state_horizon_failure_le
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (L : FiniteLaw D) (horizon : D → ℕ) (F : D → ForbiddenFamilyOn V)
    (Q₀ : D → Finset (Finset V)) (q b B k t Rmin : ℕ)
    (a coeff : D → ℕ → ℝ) (E A eta : D → ℝ) (S₀ : D → GreedyStateOn V)
    (Good : D → Prop)
    (P : ∀ d, Good d → KSSSPowerParameters (F d) q (horizon d) b B k t Rmin (a d) (coeff d) (E d) (A d))
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hEcard : ∀ d, Good d → ((Q₀ d).card : ℝ) = E d)
    (hQ₀ : ∀ d, Good d → ∀ Q ∈ Q₀ d, Q.card = 2)
    (hcover : ∀ d, Good d → ∀ T ∈ (S₀ d).available, ∀ Q : Finset V, Q.card = 2 → Q ⊆ T.1 → Q ∈ Q₀ d)
    (hregular : ∀ d, Good d → KSSSInitialRegularity (F d) (S₀ d) q (Q₀ d) (a d) (E d) (A d) (eta d))
    (hfamily : ∀ d, Good d → ∀ C ∈ F d, C ⊆ (S₀ d).available)
    (heta : ∀ d, Good d → 0 ≤ eta d)
    (hetaSmall : ∀ d, Good d → eta d ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    (badInput bandError crudeError : ℝ≥0)
    (hinput : L.probability (fun d ↦ ¬ Good d) ≤ badInput)
    (hbandError : 2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) *
      (1 / 2 : ℝ) ^ t ≤ bandError)
    (hcrude : (L.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d)
      (fun i S ↦ Good d ∧ KSSSPowerActive (F d) (Q₀ d) q b B k t (a d) (E d) (A d) i S) (S₀ d))).probability
        (fun u ↦ ¬ CrudeStateBounds (F u.1) u.2 q (dyadicCrudeThresholds V t k)) ≤ crudeError) :
    (L.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d)
      (fun i S ↦ Good d ∧ KSSSPowerActive (F d) (Q₀ d) q b B k t (a d) (E d) (A d) i S) (S₀ d))).probability
      (fun u ↦ ¬ (Good u.1 ∧ u.2.chosen.card = horizon u.1 ∧
        KSSSOnTrajectories (F u.1) u.2 q (ksssResidualPairs (Q₀ u.1) u.2) (a u.1) (E u.1) (A u.1)
          ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B u.2.chosen.card ∧
        CrudeStateBounds (F u.1) u.2 q (dyadicCrudeThresholds V t k))) ≤ badInput + bandError + crudeError := by
  let active := fun d i S ↦ Good d ∧ KSSSPowerActive (F d) (Q₀ d) q b B k t (a d) (E d) (A d) i S
  apply joint_stopped_state_horizon_failure_le L horizon F active S₀ Good
    (fun d S ↦ KSSSOnTrajectories (F d) S q (ksssResidualPairs (Q₀ d) S) (a d) (E d) (A d)
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B S.chosen.card)
    (fun d S ↦ CrudeStateBounds (F d) S q (dyadicCrudeThresholds V t k)) hInv hchosen
    (fun d i hi S hS ha ↦ ((P d ha.1).kernelBounds (Q₀ d) 1 (by norm_num)).available i hi S hS ha.2)
    ?_ badInput bandError crudeError hinput ?_ hcrude
  · intro d hd S hS hcontained htime hband hcrude
    exact ⟨hd, ksssResidualGeometry_of_contained (S₀ d).available (Q₀ d) (E d) S.chosen.card
      hS hcontained rfl (P d hd).edge_pos (hEcard d hd) (hQ₀ d hd) (hcover d hd),
      hband, hcrude, (P d hd).density_floor _ htime⟩
  · intro d hd
    rw [← NNReal.coe_le_coe]
    exact ((P d hd).state_trajectory_failure_of_active_le (Q₀ d) (S₀ d) (eta d) (active d)
      (fun _ _ h ↦ h.2) (hInv d) (hchosen d) (hQ₀ d hd) (hregular d hd) (hfamily d hd)
      (heta d hd) (hetaSmall d hd)).trans hbandError

end

end Erdos207

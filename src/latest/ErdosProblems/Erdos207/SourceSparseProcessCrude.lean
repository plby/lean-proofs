/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CurrentVariableSourceCrudeTail
import ErdosProblems.Erdos207.SourceCrudeCurrentPowerBudget
import ErdosProblems.Erdos207.KSSSPowerParameters
import ErdosProblems.Erdos207.ResidualGraphDistribution

/-! # Actual source-crude bounds for the ordinary sparse process -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem source_sparse_floor_budgets
    (n q b B k t Rmin : ℕ) (ht : 32 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n) :
    0 < dyadicMomentFloor n t (5 * b + 1) ∧
      (t : ℝ≥0) ^ (5 * b + 2) / (n + 1) ≤ 1 ∧
      (∀ H : ℕ, H ≤ n ^ 2 → (H : ℝ≥0) * (dyadicMomentFloor n t (5 * b + 1) : ℝ≥0)⁻¹ ≤
        (t : ℝ≥0) ^ (5 * b + 2) / (n + 1)) ∧
      1 ≤ 2 + ((t : ℝ≥0) ^ (5 * b + 2) / (n + 1)) * n ∧
      2 + ((t : ℝ≥0) ^ (5 * b + 2) / (n + 1)) * n ≤ (t : ℝ≥0) ^ (5 * b + 3) := by
  have ht1 : 1 ≤ t := by omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have hgap : 5 * b + 2 ≤ ksssPowerDenominatorExponent q b B k Rmin := by
    dsimp only [ksssPowerDenominatorExponent, ksssPowerThetaExponent,
      ksssPowerJumpExponent, ksssPowerVarianceExponent, ksssPowerMarginExponent,
      ksssPowerErrorExponent, ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
    omega
  have htn : t ^ (5 * b + 2) ≤ n := (Nat.pow_le_pow_right ht1 hgap).trans hscale
  have hn : 1 ≤ n := (Nat.one_le_pow _ _ ht1).trans htn
  have hn' : (t : ℝ≥0) ^ (5 * b + 2) ≤ n := by exact_mod_cast htn
  have hsize := momentFloor_size_of_power_scale n t
    (ksssPowerDenominatorExponent q b B k Rmin) (5 * b + 1) (by omega) hscale (by omega)
  refine ⟨dyadicMomentFloor_pos n t (5 * b + 1) (by omega) hsize, ?_, ?_, ?_, ?_⟩
  · exact (div_le_one (by positivity)).mpr (hn'.trans (le_add_of_nonneg_right zero_le))
  · intro H hH
    simpa only [show 5 * b + 1 + 1 = 5 * b + 2 by omega, div_eq_mul_inv] using
      dyadicMomentFloor_joint_ratio n t (5 * b + 1) H hn ht hH hsize
  · exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_add_of_nonneg_right zero_le)
  · have hquot : (n : ℝ≥0) / (n + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_right zero_le)
    have hprod : ((t : ℝ≥0) ^ (5 * b + 2) / (n + 1)) * n ≤ (t : ℝ≥0) ^ (5 * b + 2) := by
      calc
        _ = (t : ℝ≥0) ^ (5 * b + 2) * ((n : ℝ≥0) / (n + 1)) := by ring
        _ ≤ (t : ℝ≥0) ^ (5 * b + 2) * 1 := mul_le_mul_of_nonneg_left hquot zero_le
        _ = _ := mul_one _
    have hp : (1 : ℝ≥0) ≤ (t : ℝ≥0) ^ (5 * b + 2) := one_le_pow₀ htNN
    have ht3 : (3 : ℝ≥0) ≤ t := by exact_mod_cast (show 3 ≤ t by omega)
    calc
      _ ≤ 2 + (t : ℝ≥0) ^ (5 * b + 2) := add_le_add le_rfl hprod
      _ ≤ 3 * (t : ℝ≥0) ^ (5 * b + 2) := by nlinarith only [hp]
      _ ≤ (t : ℝ≥0) * (t : ℝ≥0) ^ (5 * b + 2) := mul_le_mul_of_nonneg_right ht3 zero_le
      _ = _ := by rw [show 5 * b + 3 = (5 * b + 2) + 1 by omega, pow_succ]; ring

def sourceSparseCrudeFailure (q s familyCount t decay : ℕ) (C priorCoefficient : ℝ≥0) : ℝ≥0 :=
  (256 * (q + 1 : ℝ≥0) ^ 2) * (4 * C) ^ (s * (2 * q)) *
    ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) ^ s +
      priorCoefficient * (sourceCrudeUniformWitnessFactor q familyCount * (2 : ℝ≥0) ^ (6 * q)) ^ s) /
    (t : ℝ≥0) ^ decay

theorem IsResidualGraphStronglyWellDistributed.source_sparse_crude_failure_le
    {D V I : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype I]
    {ell : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {current : Fin (ell + 1)}
    {baseGraph : SimpleGraph V} {initial later : D → TripleSystemOn V} {p C beta : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed P W current baseGraph initial later p C beta)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (q b B k t Rmin s R decay errorExponent zExponent : ℕ)
    (horizon : D → ℕ) (J : D → ForbiddenFamilyOn (W.U current))
    (G : D → SimpleGraph (W.U current)) (a coeff : D → ℕ → ℝ) (E A : D → ℝ)
    (S₀ : D → GreedyStateOn (W.U current)) (Good : D → Prop)
    (hparams : ∀ d, Good d → KSSSPowerParameters (J d) q (horizon d) b B k t Rmin
      (a d) (coeff d) (E d) (A d))
    (ht : 32 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ (W.U current).card)
    (htime : ∀ d, horizon d ≤ (W.U current).card ^ 2)
    (hInv : ∀ d, GreedyInvariant (J d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (F : I → ForbiddenFamilyOn V) (order : I → ℕ) (y z : I → ℝ≥0)
    (hF : ∀ i, SourceVortexWellSpread (W.prefix current) (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (hprior : P.SupportedOn (fun d ↦
      Disjoint (mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ d).available)
        (initial d ∪ later d) ∧
      ∀ D ∈ mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (J d),
        D ⊆ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U current)) (S₀ d).available ∧
        ∃ i H, H ∈ F i ∧ D ⊆ H ∧ H \ D ⊆ initial d ∪ later d))
    (Z priorCoefficient : ℝ≥0) (hZ : 1 ≤ Z) (hz : ∀ i, z i ≤ Z)
    (hZpower : Z ≤ (t : ℝ≥0) ^ zExponent)
    (hconstant : sourceCrudeUniformCoefficient current.val q (Fintype.card I) 1 1 ≤ t)
    (hk : 2 * zExponent + 2 * q * (5 * b + 3) + 2 ≤ k)
    (hambient : Fintype.card V ≤ t ^ R) (hs : 6 * R + decay ≤ s)
    (herrorExponent : 6 * R + (6 * q * R) * s + decay ≤ errorExponent)
    (hbeta : beta ≤ priorCoefficient / (t : ℝ≥0) ^ errorExponent) :
    (P.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (J d)
      (fun i S ↦ Good d ∧ KSSSPowerActive (J d) (graphPairFamily (G d)) q b B k t
        (a d) (E d) (A d) i S) (S₀ d))).probability
      (fun u ↦ ¬ CrudeStateBounds (J u.1) u.2 q (dyadicCrudeThresholds (W.U current) t k)) ≤
      sourceSparseCrudeFailure q s (Fintype.card I) t decay C priorCoefficient := by
  classical
  let n := (W.U current).card
  let delta : ℝ≥0 := (t : ℝ≥0) ^ (5 * b + 2) / (n + 1)
  let w : ℝ≥0 := 2 + delta * n
  have hb := source_sparse_floor_budgets n q b B k t Rmin ht hscale
  have ht1 : 1 ≤ t := by omega
  have hcut := sourceCrudeUniformCoefficient_power_cutoff current.val q (Fintype.card I)
    (5 * b + 3) zExponent k t w Z (by exact_mod_cast ht1) hb.2.2.2.1 hZ
    hb.2.2.2.2 hZpower hconstant hk
  have hraw := hstrong.toGraphStrongEmpty.current_variable_source_crude_failure_le_sum
    (q := q) (s := s) hp hC hnonempty horizon (fun _ ↦ dyadicMomentFloor n t (5 * b + 1)) J
    (fun d i S ↦ Good d ∧ KSSSPowerActive (J d) (graphPairFamily (G d)) q b B k t
      (a d) (E d) (A d) i S) S₀ delta hb.2.1 (fun _ ↦ hb.1)
    (fun d ↦ hb.2.2.1 (horizon d) (htime d))
    (fun d i S h ↦ by simpa only [Fintype.card_coe] using
      (hparams d h.1).available_floor (graphPairFamily (G d)) i S h.2)
    hInv hchosen F order y z hF horder hidentical hprior (dyadicCrudeThresholds (W.U current) t k)
    (fun i ↦ zero_lt_one.trans_le (dyadicCrudeThresholds_one_le V (W.U current) q t k ht1 i))
  have hpower := sourceCrudeTailBound_sum_current_power_prior_error_budget
    (W.prefix current) order z s R decay t k errorExponent w Z ((4 * C) ^ (s * (2 * q)))
    (((4 * C) ^ (s * (2 * q))) * beta) priorCoefficient horder hz ht1 hb.2.2.2.1
    hambient hs herrorExponent hcut
    (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbeta
        (show 0 ≤ (4 * C) ^ (s * (2 * q)) from zero_le))
  have hterminal : (W.prefix current).terminalSize = n := rfl
  have hcutoffs : dyadicCrudeThresholds (Fin (W.prefix current).terminalSize) t k =
      dyadicCrudeThresholds (W.U current) t k := by
    simp only [dyadicCrudeThresholds, Fintype.card_fin, hterminal, Fintype.card_coe, n]
  rw [hcutoffs] at hpower
  exact hraw.trans hpower

end

end Erdos207

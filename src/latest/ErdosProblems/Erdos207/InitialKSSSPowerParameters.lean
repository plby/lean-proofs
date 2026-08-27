/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialDensityBounds
import ErdosProblems.Erdos207.InitialErdosCoefficientBound
import ErdosProblems.Erdos207.InitialRestrictedDynamics
import ErdosProblems.Erdos207.KSSSDensityHorizon
import ErdosProblems.Erdos207.KSSSPowerParameters

/-! # Constructing the numeric KSSS parameters from the actual initial state -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

def initialErdosCoefficientBound (q d : ℕ) : ℝ := (fullErdosDegreeCoefficient q : ℝ) * 6 ^ d

theorem initial_absorber_ksss_power_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (q C b B k t Rmin : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (bank : TripleSystemOn V)
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) (hb : 1 ≤ b) (ht : 32 ≤ t)
    (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hcoeff : KSSSPowerCoefficientBounds q (initialErdosCoefficientBound q) B t)
    (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q (initialErdosCoefficientBound q) +
      ksssPairTaylorCoefficient (ksssOrders q) (initialErdosCoefficientBound q) ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (initialErdosCoefficientBound q) i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) (initialErdosCoefficientBound q)
        (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2) :
    let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
    let F := initialRestrictedAbsorberFamily q bank S.available
    let E : ℝ := (initialResidualPairs H).card
    let A : ℝ := S.available.card
    KSSSPowerParameters F q (ksssDensityHorizon E (1 / (t : ℝ) ^ b)) b B k t Rmin
      (initialErdosTrajectoryCoefficient V A) (initialErdosCoefficientBound q) E A := by
  dsimp only
  let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let F := initialRestrictedAbsorberFamily q bank S.available
  let N : ℝ := Fintype.card V
  let E : ℝ := (initialResidualPairs H).card
  let A : ℝ := S.available.card
  have hN1 : 1 ≤ Fintype.card V := by omega
  have hNpos : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdensity : N ^ 2 / 16 ≤ E := initialResidualPairs_density_lower (q := q) hdegree hsupport hlarge
  have hE : 0 < E := (by positivity : 0 < N ^ 2 / 16).trans_le hdensity
  have hcube : N ^ 3 ≤ 48 * A := by
    dsimp only [N, A, S]
    exact_mod_cast initial_globalAvailability_cube_le (q := q) hdegree hsupport hlarge
  have hA : 0 < A := by have hpos := pow_pos hNpos 3; nlinarith only [hpos, hcube]
  have hratio := initial_pair_relative_degree_interval (q := q) hdegree hsupport hlarge
  change N / 6 ≤ A / E ∧ A / E ≤ N / 3 ∧ _ at hratio
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htp : (32 : ℝ) ≤ (t : ℝ) ^ b := by
    have hpow : (t : ℝ) ≤ (t : ℝ) ^ b := by simpa using pow_le_pow_right₀ ht1 hb
    have htt : (32 : ℝ) ≤ t := by exact_mod_cast ht
    exact htt.trans hpow
  have hEupper : E ≤ N ^ 2 := by dsimp only [E, N]; exact_mod_cast initialResidualPairs_card_le H
  have htime := ksssDensityHorizon_power_bounds E t b (Fintype.card V) hE hEupper ht1
  have hfamily := initialRestrictedAbsorberFamily_data q bank S.available
  have hAcard : (0 : ℝ) < S.available.card := hA
  obtain ⟨T, _hT⟩ : S.available.Nonempty := card_pos.mp (by exact_mod_cast hAcard)
  refine ⟨hfamily.1, hfamily.2.2.2.1, fun D hD _ ↦ hfamily.2.2.2.2 D hD,
    hE, hA, hN1, ht, hbinomial, horder, hscale, htime.1, ?_, ?_, ?_, htime.2.1,
    ?_, ?_, hcoeff, henvelope, hpair, hconfiguration⟩
  · exact (div_le_div_of_nonneg_left (sq_nonneg N) (by norm_num) (by linarith : 16 ≤ (t : ℝ) ^ b)).trans hdensity
  · exact (div_le_div_of_nonneg_left hNpos.le (by norm_num) (by linarith : 6 ≤ (t : ℝ) ^ b)).trans hratio.1
  · have hdiv : N / 3 ≤ N := by linarith only [hNpos]
    exact hratio.2.1.trans hdiv
  · intro d _
    exact initialErdosTrajectoryCoefficient_nonneg V A hA.le d
  · intro d hd
    have hd' : d + 3 ≤ q := by
      have hmem := mem_Icc.mp hd
      change 1 ≤ d ∧ d ≤ q - 3 at hmem
      omega
    exact initialErdosTrajectoryCoefficient_fixed_bound q d T E A 6 hd'
      (by exact_mod_cast hN1) hE hA (by norm_num) hratio.1

end

end Erdos207

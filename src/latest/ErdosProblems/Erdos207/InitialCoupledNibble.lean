/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPowerCoupledRegularity
import ErdosProblems.Erdos207.InitialKSSSPowerParameters
import ErdosProblems.Erdos207.KSSSPowerHorizon

/-! # The actual initial coupled nibble, with all regularity and kernel inputs proved -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

def IsInitialCoupledOutcome
    {V : Type*} [Fintype V] [DecidableEq V]
    (q b B k t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) (S : GreedyStateOn V) : Prop :=
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let F := initialRestrictedAbsorberFamily q bank S₀.available
  let Q := initialResidualPairs H
  let E : ℝ := Q.card
  let A : ℝ := S₀.available.card
  let m := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  GreedyInvariant (absorberErdosForbiddenConfigurationsOn q bank) S ∧
    GreedyContainedIn S₀.available S ∧ S.chosen.card = m ∧
    KSSSOnTrajectories F S q (ksssResidualPairs Q S)
      (initialErdosTrajectoryCoefficient V A) E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B m ∧
    CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧
    ((ksssResidualPairs Q S).card : ℝ) < E / (t : ℝ) ^ b + 3

theorem InitialPowerVortexPackage.exists_initial_coupled_nibble
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (b B k Rmin : ℕ) (hb : 1 ≤ b) (ht : 32 ≤ t)
    (hc : powerAbsorberCoefficient q ≤ t)
    (hcrude : powerAbsorberCrudeCoefficient q ≤ t)
    (hempty : pairBankPolynomialCoefficient q ≤ t)
    (hvertex : 2 ^ (q ^ 3) * (q + 1) ≤ t) (hbinomial : 2 ^ q ≤ t) (horder : q ≤ t)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n)
    (hrootGap : initialRegularityCoefficientPower q rootPower + 2 +
      (ksssPowerErrorExponent b B + 1) + b * q ≤ ksssPowerDenominatorExponent q b B k Rmin)
    (hpairGap : initialSupportPower rootPower + (ksssPowerErrorExponent b B + 1) + 2 ≤
      ksssPowerDenominatorExponent q b B k Rmin)
    (hcoeff : KSSSPowerCoefficientBounds q (initialErdosCoefficientBound q) B t)
    (henvelope : 4 * q ≤ B)
    (hpair : ksssPairDriftCoefficient q (initialErdosCoefficientBound q) +
      ksssPairTaylorCoefficient (ksssOrders q) (initialErdosCoefficientBound q) ≤ 3 * (B : ℝ))
    (hconfiguration : ∀ i : CrudeOrderIndex q 4,
      ksssIndexedConfigurationDriftCoefficient q (initialErdosCoefficientBound q) i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) (initialErdosCoefficientBound q)
        (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2)
    (hk : k = dyadicCrudeExponent q (powerAbsorberCrudeExponent q rootPower) (5 * b + 2))
    (hsmall : (2 * ((n : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (n : ℝ) ^ 3) +
      4 * (q + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ 6) * (1 / 2 : ℝ) ^ t < 1) :
    ∃ S, IsInitialCoupledOutcome q b B k t P.H P.B S := by
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B) (outsideAvailableTriangles P.H P.B)
  let F := initialRestrictedAbsorberFamily q P.B S₀.available
  let Q := initialResidualPairs P.H
  let E : ℝ := Q.card
  let A : ℝ := S₀.available.card
  let s := ksssPowerErrorExponent b B
  let R := ksssPowerDenominatorExponent q b B k Rmin
  let eta : ℝ := 1 / (t : ℝ) ^ (s + 1)
  let m := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  have htR : (32 : ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  obtain ⟨hdegree, _hgraph, hbank⟩ := P.support_power_bounds hc
  have hlarge : 6 * t ^ initialSupportPower rootPower + 4 ≤ Fintype.card (Fin n) := by
    have hp : (t : ℝ) ^ (initialSupportPower rootPower + 1) ≤ (t : ℝ) ^ R :=
      pow_le_pow_right₀ ht1 (by dsimp only [R]; omega)
    have hscaleR : (t : ℝ) ^ R ≤ n := by exact_mod_cast hscale
    have hx := (initial_support_density_power (t : ℝ) (initialSupportPower rootPower) (by linarith)).trans
      (hp.trans hscaleR)
    simpa using (show 6 * t ^ initialSupportPower rootPower + 4 ≤ n by exact_mod_cast hx)
  have D := initial_absorber_ksss_power_parameters q (t ^ initialSupportPower rootPower) b B k t Rmin
    P.H P.B hdegree hbank hlarge hb ht hbinomial horder (by simpa using hscale)
    hcoeff henvelope hpair hconfiguration
  have hregular := P.initial_coupled_regularity R (s + 1) b (by omega) hb hc hcrude hempty hvertex
    hbinomial hscale hrootGap hpairGap
  have hFdata := initialRestrictedAbsorberFamily_data q P.B S₀.available
  have hInv₀ := initialRestrictedAbsorberFamily_initial_invariant q P.H P.B
  have hQ : ∀ Q' ∈ Q, Q'.card = 2 := fun Q' hQ' ↦ ((mem_initialResidualPairs P.H Q').mp hQ').1
  have hcover : ∀ T ∈ S₀.available, ∀ Q' : Finset (Fin n), Q'.card = 2 → Q' ⊆ T.1 → Q' ∈ Q :=
    fun _ hT _ hQ' hQT ↦ initialResidualPairs_cover_all_triangle_pairs q P.H P.B hT hQ' hQT
  have heta : eta ≤ 1 / (6 * (t : ℝ) ^ s) := by
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    rw [pow_succ]
    nlinarith only [mul_nonneg (show 0 ≤ (t : ℝ) - 6 by linarith) (pow_nonneg htpos.le s)]
  obtain ⟨S, hS, hcontained, hchosen, hband, hcrudeState⟩ := D.exists_good_horizon Q S₀ P.B
    (powerAbsorberCoefficient q ^ 3 + 1) (3 * (156 * rootPower))
    (powerAbsorberCrudeExponent q rootPower) eta hFdata.2.1 hInv₀ rfl rfl hQ hcover hregular
    hFdata.2.2.1 (by dsimp only [eta]; positivity) heta hconst P.bank_card_add_one_le_power
    hcrude le_rfl hk (by simpa only [Fintype.card_fin] using hsmall)
  have hgeometry := ksssResidualGeometry_of_contained S₀.available Q E m hS hcontained hchosen
    D.edge_pos rfl hQ hcover
  have htime := ksssDensityHorizon_power_bounds E t b n D.edge_pos
    (by
      dsimp only [E, Q]
      have hn : (initialResidualPairs P.H).card ≤ n ^ 2 := by
        simpa only [Fintype.card_fin] using initialResidualPairs_card_le P.H
      exact_mod_cast hn) ht1
  have hresidual : ((ksssResidualPairs Q S).card : ℝ) = E - 3 * (m : ℝ) := by
    rw [hgeometry.count]
    unfold ksssEdgeDensity
    have hE : E ≠ 0 := D.edge_pos.ne'
    field_simp
  refine ⟨S, initialRestrictedAbsorberFamily_restore_invariant q P.B S₀.available S hS hcontained,
    hcontained, hchosen, hband, hcrudeState, ?_⟩
  rw [hresidual]
  exact htime.2.2

end

end Erdos207

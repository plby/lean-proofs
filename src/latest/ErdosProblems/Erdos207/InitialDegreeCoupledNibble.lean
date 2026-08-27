/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialCoupledNibble
import ErdosProblems.Erdos207.InitialNeighborMargins
import ErdosProblems.Erdos207.KSSSDegreeHorizon

/-! # The constructed absorber gives a coupled nibble with all vortex degree bands -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem InitialPowerVortexPackage.exists_initial_degree_coupled_nibble
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
    (hdegreeCoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t)
    (hrootSize : 2 * ksssPowerErrorExponent b B + 2 * b + 3 ≤ rootPower)
    (hsmall : (2 * ((n : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (n : ℝ) ^ 3) +
      2 * (ell + 1 : ℝ) * n + 4 * (q + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ 6) * (1 / 2 : ℝ) ^ t < 1) :
    ∃ S, IsInitialCoupledOutcome q b B k t P.H P.B S ∧
      AllUncoveredNeighborBands P.W.U (initialResidualPairs P.H) (initialResidualPairs P.H).card t
        (ksssPowerErrorExponent b B) B
        (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b)) S := by
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B) (outsideAvailableTriangles P.H P.B)
  let Q := initialResidualPairs P.H
  let E : ℝ := Q.card
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
  have hinitial := P.initial_neighbor_margins s R (by omega) hc
    (by dsimp only [s]; omega) hscale (by dsimp only [R, s]; omega)
  have hsize : ∀ i, (t : ℝ) ^ (2 * s + 2 * b + 3) ≤ ((P.W.U i).card : ℝ) := by
    intro i
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < t) hrootSize).trans (P.level_card_lower i)
  have hratio := (initial_pair_relative_degree_interval (q := q) hdegree hbank hlarge).1
  obtain ⟨S, hS, hcontained, hchosen, hband, hcrudeState, hdegrees⟩ := D.exists_good_horizon_with_neighbor_bands
    P.W.U Q S₀ P.B (powerAbsorberCoefficient q ^ 3 + 1) (3 * (156 * rootPower))
    (powerAbsorberCrudeExponent q rootPower) eta hFdata.2.1 hInv₀ rfl rfl hQ hcover hregular
    hFdata.2.2.1 (by dsimp only [eta]; positivity) heta hconst P.bank_card_add_one_le_power
    hcrude le_rfl hk hratio hdegreeCoefficient hsize hinitial
    (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hsmall)
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
  refine ⟨S, ⟨initialRestrictedAbsorberFamily_restore_invariant q P.B S₀.available S hS hcontained,
    hcontained, hchosen, hband, hcrudeState, ?_⟩, hdegrees⟩
  rw [hresidual]
  exact htime.2.2

end

end Erdos207

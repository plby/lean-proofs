/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternOutcomeTypicality
import ErdosProblems.Erdos207.KSSSConditionedPatternLaw

/-! # A constructed initial law with exact typicality and graph-restricted distribution -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def initialPatternGraphError (q h ell n t : ℕ) : ℝ≥0 :=
  (8 * (q + 1 : ℝ≥0) ^ 2 + 5 * (ell + 1 : ℝ≥0) + 2 * (ell + 1 : ℝ≥0) * h ^ 2) *
    (n + 1 : ℝ≥0) ^ (6 + 2 * h ^ 2) * (1 / 2 : ℝ≥0) ^ t

def IsInitialTypicalPatternLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h b B k t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) (W : Vortex V ell)
    (law : FiniteLaw (GreedyStateOn V)) : Prop :=
  law.SupportedOn (IsInitialTypicalPatternOutcome q h b B k t H bank W) ∧
    IsInitialGraphProductBound law (fun S ↦ S.chosen)
      (graphDifference (SimpleGraph.completeGraph V) H)
      (Real.toNNReal (ksssEdgeDensity (initialResidualPairs H).card
        (ksssDensityHorizon (initialResidualPairs H).card (1 / (t : ℝ) ^ b))))
      (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
      (initialPatternGraphError q h ell (Fintype.card V) t)

theorem InitialPowerVortexPackage.exists_initial_typical_pattern_law
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (b B k Rmin r : ℕ) (hb : 1 ≤ b) (ht : 32 ≤ t)
    (hc : powerAbsorberCoefficient q ≤ t) (hcrude : powerAbsorberCrudeCoefficient q ≤ t)
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
    (hr : r = 2 * ksssPowerErrorExponent b B + b * h + h ^ 2 + 2 * b + 1)
    (hrootSize : r + q * (5 * b + 3) + 4 ≤ rootPower)
    (houterGap : r + k + 1 ≤ ksssPowerDenominatorExponent q b B k Rmin)
    (hlocalGap : powerAbsorberCrudeExponent q rootPower + ((r + 2) + q * (5 * b + 3) + 1) ≤
      ksssPowerDenominatorExponent q b B k Rmin)
    (hpatternCoeff : 2 * h + 36 * h ^ 2 ≤ t) (hedgeCoeff : 3 + h ^ 2 ≤ t)
    (hlocalRootCoeff : 45 * (q + 1) + 28 ≤ t) (hlocalConst : 4 * (q + 1) ^ (q + 2) ≤ t)
    (hreq : ∀ h' m', h' ≤ h → m' ≤ h ^ 2 →
      KSSSPatternPowerRequirements q b B k Rmin h' m' t (initialErdosCoefficientBound q))
    (hsmall : (8 * (q + 1 : ℝ) ^ 2 + 5 * (ell + 1 : ℝ) + 2 * (ell + 1 : ℝ) * h ^ 2) *
      (n + 1 : ℝ) ^ (6 + 2 * h ^ 2) * (1 / 2 : ℝ) ^ t < 1 / 2) :
    ∃ law : FiniteLaw (GreedyStateOn (Fin n)), IsInitialTypicalPatternLaw q h b B k t P.H P.B P.W law := by
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B) (outsideAvailableTriangles P.H P.B)
  let Q₀ := initialResidualPairs P.H
  let E : ℝ := Q₀.card
  let s := ksssPowerErrorExponent b B
  let R := ksssPowerDenominatorExponent q b B k Rmin
  let eta : ℝ := 1 / (t : ℝ) ^ (s + 1)
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  let G₀ := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let patterns := fun Q : WorkingGraphPattern G₀ h ↦ Q.1.1
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
  have hQ : ∀ Q' ∈ Q₀, Q'.card = 2 := fun Q' hQ' ↦ ((mem_initialResidualPairs P.H Q').mp hQ').1
  have hcover : ∀ T ∈ S₀.available, ∀ Q' : Finset (Fin n), Q'.card = 2 → Q' ⊆ T.1 → Q' ∈ Q₀ :=
    fun _ hT _ hQ' hQT ↦ initialResidualPairs_cover_all_triangle_pairs q P.H P.B hT hQ' hQT
  have heta : eta ≤ 1 / (6 * (t : ℝ) ^ s) := by
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    rw [pow_succ]
    nlinarith only [mul_nonneg (show 0 ≤ (t : ℝ) - 6 by linarith) (pow_nonneg htpos.le s)]
  have hdegreeInitial := P.initial_neighbor_margins s R (by omega) hc
    (by dsimp only [s]; omega) hscale (by dsimp only [R, s]; omega)
  have hpatternInitial := P.initial_pattern_margins s R (by omega) hc hpatternCoeff
    (by dsimp only [s]; omega) hscale (by dsimp only [R, s]; omega)
  have hlevelPower : ∀ i, (t : ℝ) ^ rootPower ≤ ((P.W.U i).card : ℝ) := by
    intro i
    exact_mod_cast P.level_card_lower i
  have hdegreeSize : ∀ i, (t : ℝ) ^ (2 * s + 2 * b + 3) ≤ ((P.W.U i).card : ℝ) :=
    fun i ↦ (pow_le_pow_right₀ ht1 (by dsimp only [s]; omega)).trans (hlevelPower i)
  have hpatternSize : ∀ i, (t : ℝ) ^ (r + 2) ≤ ((P.W.U i).card : ℝ) :=
    fun i ↦ (pow_le_pow_right₀ ht1 (by omega)).trans (hlevelPower i)
  have houterBudget : (t : ℝ) ^ (r + k + 1) ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using
      (show (t : ℝ) ^ (r + k + 1) ≤ n by exact_mod_cast
        (Nat.pow_le_pow_right (by omega : 0 < t) houterGap).trans hscale)
  have hpatternEdges : ∀ Q : WorkingGraphPattern G₀ h, (graphEdges Q.1.1).card ≤ h ^ 2 := fun Q ↦
    (card_graphEdges_le_graphSupportFinset_sq Q.1.1).trans (Nat.pow_le_pow_left Q.1.2 2)
  have hpatternExponent : ∀ j, 2 * s + (b * (graphSupportFinset (patterns j)).card +
      (graphEdges (patterns j)).card) + 2 * b + 1 ≤ r := by
    intro j
    have hbSupport := Nat.mul_le_mul_left b j.1.2
    have he := hpatternEdges j
    dsimp only [patterns, s]
    omega
  have hpatternCoefficient : ∀ j, 3 + ((graphEdges (patterns j)).card : ℝ) ≤ t := by
    intro j
    exact_mod_cast (show 3 + (graphEdges (patterns j)).card ≤ t by
      have he := hpatternEdges j
      dsimp only [patterns]
      omega)
  have hpattern₀ : ∀ j, PatternUncovered (patterns j) S₀ := by
    intro j e _
    change e ∉ (coveredGraph (∅ : TripleSystemOn (Fin n))).edgeSet
    simp only [coveredGraph_empty, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  have hlocalBudgets := P.localized_pattern_budgets b (r + 2) R hcrude hlocalRootCoeff
    (by omega) hlocalGap hscale
  have hpoly := pattern_coupled_failure_coefficient_le q h (ell + 1)
    (Fintype.card (WorkingGraphPattern G₀ h)) (Fintype.card {i : Fin (ell + 1) // i ≠ 0}) n
    (by simpa only [Fintype.card_fin] using card_workingGraphPattern_le_polynomial G₀ h)
    (by simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin (ell + 1) ↦ i ≠ 0))
  have hsmallActual : (2 * ((Fintype.card (Fin n) : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 3) +
      2 * (Fintype.card (Fin (ell + 1)) : ℝ) * Fintype.card (Fin n) +
      2 * (Fintype.card (Fin (ell + 1)) : ℝ) * Fintype.card (WorkingGraphPattern G₀ h) +
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card (Fin n) + 1 : ℝ) ^ 6 +
      (Fintype.card {i : Fin (ell + 1) // i ≠ 0} : ℝ) * (Fintype.card (Fin n) : ℝ) ^ 5) * (1 / 2 : ℝ) ^ t < 1 / 2 := by
    apply lt_of_le_of_lt _ hsmall
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp only [Fintype.card_fin]
    exact_mod_cast hpoly
  have hratio := (initial_pair_relative_degree_interval (q := q) hdegree hbank hlarge).1
  obtain ⟨Ldata⟩ := D.exists_pattern_stopped_law
    P.W.U patterns 0 P.W.root Q₀ S₀ P.H P.B P.X (powerAbsorberCoefficient q ^ 3 + 1)
    (3 * (156 * rootPower)) (powerAbsorberCrudeExponent q rootPower) r eta hFdata.2.1
    (fun i hi ↦ P.inner_separated i hi) P.rootLocalization hInv₀ rfl rfl hQ hcover hregular
    hFdata.2.2.1 (by dsimp only [eta]; positivity) heta hconst P.bank_card_add_one_le_power
    hcrude le_rfl hk hratio hdegreeCoefficient hdegreeSize hdegreeInitial P.nonempty hpattern₀
    (fun Q ↦ hreq _ _ Q.1.2 (hpatternEdges Q)) hpatternExponent hpatternSize hpatternInitial
    hpatternCoefficient houterBudget (fun i _ ↦ hlocalBudgets.1 i)
    (by simpa only [Fintype.card_fin] using hlocalBudgets.2) hlocalConst
  have hEupper : E ≤ (Fintype.card (Fin n) : ℝ) ^ 2 := by
    dsimp only [E, Q₀]
    exact_mod_cast initialResidualPairs_card_le P.H
  have hEquadratic : (Fintype.card (Fin n) : ℝ) ^ 2 ≤ 16 * E := by
    have h := initialResidualPairs_density_lower (q := q) hdegree hbank hlarge
    change (Fintype.card (Fin n) : ℝ) ^ 2 / 16 ≤ E at h
    linarith only [h]
  obtain ⟨law, hsupport, hgraph⟩ := KSSSPatternStoppedLawData.exists_conditioned_graph_law
    D P.H S₀ P.W.U patterns 0 Ldata hInv₀ rfl
    (fun T hT ↦ initialAvailable_edges_in_workingGraph q P.H P.B hT)
    hratio hEupper hEquadratic (by simpa only [ksssPatternFailureCoefficient] using hsmallActual)
  have htime := ksssDensityHorizon_power_bounds E t b n D.edge_pos
    (by simpa only [Fintype.card_fin] using hEupper) ht1
  refine ⟨law, ?_, ?_⟩
  · intro S hmass
    obtain ⟨hS, hcontained, hchosen, hband, hcrudeState, hdegrees, hpatterns⟩ := hsupport S hmass
    have hgeometry := ksssResidualGeometry_of_contained S₀.available Q₀ E time hS hcontained hchosen
      D.edge_pos rfl hQ hcover
    have hresidual : ((ksssResidualPairs Q₀ S).card : ℝ) = E - 3 * (time : ℝ) := by
      rw [hgeometry.count]
      unfold ksssEdgeDensity
      have hE : E ≠ 0 := D.edge_pos.ne'
      field_simp
    have hgood : IsInitialPatternOutcome q h b B k t P.H P.B P.W S := by
      refine ⟨⟨initialRestrictedAbsorberFamily_restore_invariant q P.B S₀.available S hS hcontained,
        hcontained, hchosen, hband, hcrudeState, ?_⟩, hdegrees, hpatterns⟩
      rw [hresidual]
      exact htime.2.2
    exact P.initial_pattern_outcome_typical b B k S hgood hb (by omega) (by omega) hc
      (by simpa only [Fintype.card_fin] using hlarge) (by omega) hcoeff.poisson
  · apply hgraph.mono_error
    let c := ksssPatternFailureCoefficient q n (ell + 1) (Fintype.card (WorkingGraphPattern G₀ h))
      (Fintype.card {i : Fin (ell + 1) // i ≠ 0})
    have hc0 : 0 ≤ c := by dsimp only [c, ksssPatternFailureCoefficient]; positivity
    have hpolyR : c ≤ (8 * (q + 1 : ℝ) ^ 2 + 5 * (ell + 1 : ℝ) + 2 * (ell + 1 : ℝ) * h ^ 2) *
        (n + 1 : ℝ) ^ (6 + 2 * h ^ 2) := by
      dsimp only [c, ksssPatternFailureCoefficient]
      exact_mod_cast hpoly
    rw [← NNReal.coe_le_coe]
    simp only [Fintype.card_fin, initialPatternGraphError, NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_one]
    change (Real.toNNReal c : ℝ) * (1 / 2 : ℝ) ^ t ≤ _
    rw [Real.coe_toNNReal _ hc0]
    exact mul_le_mul_of_nonneg_right hpolyR (by positivity)

end

end Erdos207

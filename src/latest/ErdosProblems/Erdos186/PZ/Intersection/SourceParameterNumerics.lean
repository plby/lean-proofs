/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic
import ErdosProblems.Erdos186.Parameters
import ErdosProblems.Erdos186.PZ.Intersection.Main
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeRanks

/-!
# Eventual source-parameter inequalities for the PZ intersection

This file converts the three scale inequalities in `Theorem4Parameters`
into the polynomial room needed after the two dense side sets have been
selected.  The important point is uniformity: the threshold depends only on
the fixed exponents, the bounded CFP context, the rank ceiling, and the
requested constant, not on the finite set or on the admissible values of
`delta`, `gamma`, and `mu`.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-- Multiplication by a fixed constant does not affect strict polynomial
growth.  This small wrapper is convenient for extracting natural thresholds
below. -/
theorem eventually_const_mul_nat_rpow_lt_nat_rpow
    (K : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      K * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have hgrowth := (nat_rpow_tendsto_atTop (sub_pos.mpr hab)).eventually_gt_atTop K
  filter_upwards [hgrowth, eventually_ge_atTop (1 : ℕ)] with n hn hnone
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
  calc
    K * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hn hpowpos
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- The logarithmic lower bound in `Theorem4Parameters` is eventually
stronger than every prescribed inverse power of the population. -/
theorem eventually_source_gamma_inverse_power_lower
    (C' : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, ∀ gamma : ℝ,
      (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
      (N : ℝ) ^ (-q) ≤ gamma := by
  filter_upwards [eventually_nat_rpow_neg_le_log_rpow_neg (1 / C') hq]
    with N hN
  intro gamma hgamma
  exact hN.trans hgamma

/-- Pull an arbitrary inverse-power lower bound through
`gamma ≤ delta^C`. -/
theorem eventually_source_delta_inverse_power_lower
    (C C' : ℝ) (hC : 0 < C) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, ∀ delta gamma : ℝ,
      0 < delta →
      (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
      gamma ≤ delta ^ C →
      (N : ℝ) ^ (-q) ≤ delta := by
  have hqC : 0 < q * C := mul_pos hq hC
  filter_upwards [eventually_source_gamma_inverse_power_lower C' hqC,
    eventually_ge_atTop (1 : ℕ)] with N hgammaLower hNone
  intro delta gamma hdelta hlog hgammaDelta
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg hnpos.le (-q)) hdelta.le hC).mp
  calc
    ((N : ℝ) ^ (-q)) ^ C = (N : ℝ) ^ ((-q) * C) := by
      rw [Real.rpow_mul hnpos.le]
    _ = (N : ℝ) ^ (-(q * C)) := by ring_nf
    _ ≤ gamma := hgammaLower gamma hlog
    _ ≤ delta ^ C := hgammaDelta

/-- Pulling once more through `delta ≤ mu^C` gives the same useful
inverse-power lower bound for `mu`. -/
theorem eventually_source_mu_inverse_power_lower
    (C C' : ℝ) (hC : 0 < C) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, ∀ delta gamma mu : ℝ,
      0 < delta → 0 < mu →
      (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
      gamma ≤ delta ^ C → delta ≤ mu ^ C →
      (N : ℝ) ^ (-q) ≤ mu := by
  have hqC : 0 < q * C := mul_pos hq hC
  filter_upwards [eventually_source_delta_inverse_power_lower C C' hC hqC,
    eventually_ge_atTop (1 : ℕ)] with N hdeltaLower hNone
  intro delta gamma mu hdelta hmu hlog hgammaDelta hdeltaMu
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg hnpos.le (-q)) hmu.le hC).mp
  calc
    ((N : ℝ) ^ (-q)) ^ C = (N : ℝ) ^ ((-q) * C) := by
      rw [Real.rpow_mul hnpos.le]
    _ = (N : ℝ) ^ (-(q * C)) := by ring_nf
    _ ≤ delta := hdeltaLower delta gamma hdelta hlog hgammaDelta
    _ ≤ mu ^ C := hdeltaMu

/-- A dense selected input inherits a polynomial lower bound for its CFP
dilation times `gamma`.  The denominator is made uniform over all ambient
dimensions up to `rankCeiling` by `scaleDenSum`. -/
theorem selectedCFP_dilation_mul_gamma_polynomial_lower
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    {rankCeiling r N : ℕ} {X : Finset (LatticePoint r)}
    (I : Reduction.EligibleInput context X)
    {delta gamma u v : ℝ}
    (hN : 0 < N) (heta : 0 ≤ eta) (hrank : r ≤ rankCeiling)
    (_hdelta : 0 < delta) (_hgamma : 0 < gamma)
    (hdeltaLower : (N : ℝ) ^ (-u) ≤ delta)
    (hgammaLower : (N : ℝ) ^ (-v) ≤ gamma)
    (hdense : delta * (N : ℝ) ≤ (X.card : ℝ)) :
    (N : ℝ) ^ (eta * (1 - u) - v) ≤
      (Reduction.scaleDenSum context rankCeiling : ℝ) *
        (I.selectedCFP.dilation : ℝ) * gamma := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hpopulation : (N : ℝ) ^ (1 - u) ≤ (X.card : ℝ) := by
    calc
      (N : ℝ) ^ (1 - u) =
          (N : ℝ) ^ (-u) * (N : ℝ) := by
        calc
          (N : ℝ) ^ (1 - u) = (N : ℝ) ^ (-u + 1) := by ring_nf
          _ = (N : ℝ) ^ (-u) * (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_add hNreal _ _
          _ = (N : ℝ) ^ (-u) * (N : ℝ) := by rw [Real.rpow_one]
      _ ≤ delta * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hdeltaLower (by positivity)
      _ ≤ (X.card : ℝ) := hdense
  have hpopulationPow :
      (N : ℝ) ^ (eta * (1 - u)) ≤ (X.card : ℝ) ^ eta := by
    rw [show eta * (1 - u) = (1 - u) * eta by ring,
      Real.rpow_mul hNreal.le]
    exact Real.rpow_le_rpow
      (Real.rpow_nonneg hNreal.le _) hpopulation heta
  have hscaleDilation : (I.scale : ℝ) ≤
      (Reduction.scaleDenSum context rankCeiling : ℝ) *
        (I.selectedCFP.dilation : ℝ) := by
    have hscaleNat := I.selectedCFP.witness.scale_lower
    have hscaleNum : I.selectedCFP.witness.scaleNum = context.scaleNum r :=
      I.selectedCFP_scaleNum
    have hscaleDen : I.selectedCFP.witness.scaleDen = context.scaleDen r :=
      I.selectedCFP_scaleDen
    have hnum : 1 ≤ context.scaleNum r := context.scaleNum_pos r
    have hscaleNat' : I.scale ≤
        context.scaleDen r * I.selectedCFP.dilation := by
      calc
        I.scale = 1 * I.scale := by simp
        _ ≤ context.scaleNum r * I.scale := Nat.mul_le_mul_right _ hnum
        _ ≤ context.scaleDen r * I.selectedCFP.dilation := by
          rw [hscaleNum, hscaleDen] at hscaleNat
          exact hscaleNat
    have hden := Reduction.scaleDen_le_scaleDenSum context hrank
    exact_mod_cast hscaleNat'.trans
      (Nat.mul_le_mul_right I.selectedCFP.dilation hden)
  have hpowerScale : (N : ℝ) ^ (eta * (1 - u)) ≤
      (Reduction.scaleDenSum context rankCeiling : ℝ) *
        (I.selectedCFP.dilation : ℝ) :=
    hpopulationPow.trans (I.scale_lower.trans hscaleDilation)
  calc
    (N : ℝ) ^ (eta * (1 - u) - v) =
        (N : ℝ) ^ (eta * (1 - u)) * (N : ℝ) ^ (-v) := by
      rw [← Real.rpow_add hNreal]
      congr 1
    _ ≤ ((Reduction.scaleDenSum context rankCeiling : ℝ) *
          (I.selectedCFP.dilation : ℝ)) * gamma :=
      mul_le_mul hpowerScale hgammaLower
        (Real.rpow_nonneg hNreal.le _) (by positivity)
    _ = (Reduction.scaleDenSum context rankCeiling : ℝ) *
        (I.selectedCFP.dilation : ℝ) * gamma := by ring

/-- Uniform eventual full-rank hierarchy.  Once a selected side has at
least `delta * |A|` points, its actual CFP dilation times `gamma` dominates
any fixed real constant.  This is the form consumed by the controlled-box
determinant criteria. -/
theorem exists_cardThreshold_selectedCFP_dilation_mul_gamma_gt
    {beta eta C C' : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta) (hC : 0 < C) (K : ℝ) :
    ∃ M : ℕ, ∀ {d : ℕ} (A : Finset (LatticePoint d))
      (delta gamma mu : ℝ),
      Theorem4Parameters A beta C C' M delta gamma mu →
      ∀ {r : ℕ} {X : Finset (LatticePoint r)}
        (I : Reduction.EligibleInput context X),
        r ≤ rankCeiling →
        delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        K < (I.selectedCFP.dilation : ℝ) * gamma := by
  let p : ℝ := eta / 2
  let u : ℝ := (eta - p) / (eta + 1)
  have hp : 0 < p := by dsimp [p]; linarith
  have hpeta : p < eta := by dsimp [p]; linarith
  have hetaOne : 0 < eta + 1 := by linarith
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (sub_pos.mpr hpeta) hetaOne
  have hexponent : eta * (1 - u) - u = p := by
    dsimp [u]
    field_simp [ne_of_gt hetaOne]
    ring
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  have hD : 0 < D := Reduction.scaleDenSum_pos context rankCeiling
  have Hgamma := eventually_source_gamma_inverse_power_lower C' hu
  have Hdelta := eventually_source_delta_inverse_power_lower C C' hC hu
  have Hgrowth := eventually_const_mul_nat_rpow_lt_nat_rpow
    (K * (D : ℝ)) (a := 0) (b := p) hp
  have Hall : ∀ᶠ N : ℕ in atTop,
      (1 ≤ N) ∧
      (∀ gamma : ℝ,
        (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
          (N : ℝ) ^ (-u) ≤ gamma) ∧
      (∀ delta gamma : ℝ, 0 < delta →
        (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
        gamma ≤ delta ^ C → (N : ℝ) ^ (-u) ≤ delta) ∧
      K * (D : ℝ) * (N : ℝ) ^ (0 : ℝ) < (N : ℝ) ^ p := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), Hgamma, Hdelta, Hgrowth]
      with N hN hgammaN hdeltaN hgrowthN
    exact ⟨hN, hgammaN, hdeltaN, hgrowthN⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp Hall
  refine ⟨M, ?_⟩
  intro d A delta gamma mu hparams r X I hrank hdense
  have hlarge := hM A.card hparams.card_large
  have hN : 0 < A.card := by omega
  have hgammaLower : (A.card : ℝ) ^ (-u) ≤ gamma :=
    hlarge.2.1 gamma hparams.gamma_log_lower
  have hdeltaLower : (A.card : ℝ) ^ (-u) ≤ delta :=
    hlarge.2.2.1 delta gamma hparams.delta_pos
      hparams.gamma_log_lower hparams.gamma_le_delta
  have hpoly := selectedCFP_dilation_mul_gamma_polynomial_lower
    context I hN heta.le hrank hparams.delta_pos hparams.gamma_pos
      hdeltaLower hgammaLower hdense
  rw [hexponent] at hpoly
  have hconstant : K * (D : ℝ) < (A.card : ℝ) ^ p := by
    simpa using hlarge.2.2.2
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hscaled : (D : ℝ) * K <
      (D : ℝ) * ((I.selectedCFP.dilation : ℝ) * gamma) := by
    calc
      (D : ℝ) * K = K * (D : ℝ) := by ring
      _ < (A.card : ℝ) ^ p := hconstant
      _ ≤ (D : ℝ) * (I.selectedCFP.dilation : ℝ) * gamma := by
        simpa only [D] using hpoly
      _ = (D : ℝ) *
          ((I.selectedCFP.dilation : ℝ) * gamma) := by ring
  exact (mul_lt_mul_iff_of_pos_left hDreal).mp hscaled

/-- Uniform anisotropic hierarchy.  If the CFP scale exponent is larger
than `1/2`, then the selected dilation times `gamma` dominates a fixed
constant times the square-root rounding loss of every subcore of the
original population. -/
theorem exists_cardThreshold_sqrt_card_mul_le_selectedCFP_dilation_mul_gamma
    {beta eta C C' : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : (1 : ℝ) / 2 < eta)
    (hC : 0 < C) (K : ℝ) (hK : 0 ≤ K) :
    ∃ M : ℕ, ∀ {d : ℕ} (A : Finset (LatticePoint d))
      (delta gamma mu : ℝ),
      Theorem4Parameters A beta C C' M delta gamma mu →
      ∀ {r : ℕ} {X Y : Finset (LatticePoint r)}
        (I : Reduction.EligibleInput context X),
        r ≤ rankCeiling → Y.card ≤ A.card →
        delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        Real.sqrt (((r * Y.card : ℕ) : ℝ)) * K ≤
          (I.selectedCFP.dilation : ℝ) * gamma := by
  let p : ℝ := (eta + (1 : ℝ) / 2) / 2
  let u : ℝ := (eta - p) / (eta + 1)
  have heta0 : 0 < eta := by linarith
  have hpHalf : (1 : ℝ) / 2 < p := by dsimp [p]; linarith
  have hpeta : p < eta := by dsimp [p]; linarith
  have hetaOne : 0 < eta + 1 := by linarith
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (sub_pos.mpr hpeta) hetaOne
  have hexponent : eta * (1 - u) - u = p := by
    dsimp [u]
    field_simp [ne_of_gt hetaOne]
    ring
  let D : ℕ := Reduction.scaleDenSum context rankCeiling
  have hD : 0 < D := Reduction.scaleDenSum_pos context rankCeiling
  let L : ℝ := (D : ℝ) * K * Real.sqrt (rankCeiling : ℝ)
  have Hgamma := eventually_source_gamma_inverse_power_lower C' hu
  have Hdelta := eventually_source_delta_inverse_power_lower C C' hC hu
  have Hgrowth := eventually_const_mul_nat_rpow_lt_nat_rpow
    L (a := (1 : ℝ) / 2) (b := p) hpHalf
  have Hall : ∀ᶠ N : ℕ in atTop,
      (1 ≤ N) ∧
      (∀ gamma : ℝ,
        (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
          (N : ℝ) ^ (-u) ≤ gamma) ∧
      (∀ delta gamma : ℝ, 0 < delta →
        (Real.log (N : ℝ)) ^ (-(1 / C')) ≤ gamma →
        gamma ≤ delta ^ C → (N : ℝ) ^ (-u) ≤ delta) ∧
      L * (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) ^ p := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), Hgamma, Hdelta, Hgrowth]
      with N hN hgammaN hdeltaN hgrowthN
    exact ⟨hN, hgammaN, hdeltaN, hgrowthN⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp Hall
  refine ⟨M, ?_⟩
  intro d A delta gamma mu hparams r X Y I hrank hYcard hdense
  have hlarge := hM A.card hparams.card_large
  have hN : 0 < A.card := by omega
  have hgammaLower : (A.card : ℝ) ^ (-u) ≤ gamma :=
    hlarge.2.1 gamma hparams.gamma_log_lower
  have hdeltaLower : (A.card : ℝ) ^ (-u) ≤ delta :=
    hlarge.2.2.1 delta gamma hparams.delta_pos
      hparams.gamma_log_lower hparams.gamma_le_delta
  have hpoly := selectedCFP_dilation_mul_gamma_polynomial_lower
    context I hN heta0.le hrank hparams.delta_pos hparams.gamma_pos
      hdeltaLower hgammaLower hdense
  rw [hexponent] at hpoly
  have hcardNat : r * Y.card ≤ rankCeiling * A.card :=
    Nat.mul_le_mul hrank hYcard
  have hrho : Real.sqrt (((r * Y.card : ℕ) : ℝ)) ≤
      Real.sqrt (rankCeiling : ℝ) *
        (A.card : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      Real.sqrt (((r * Y.card : ℕ) : ℝ)) ≤
          Real.sqrt (((rankCeiling * A.card : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hcardNat)
      _ = Real.sqrt (rankCeiling : ℝ) *
          Real.sqrt (A.card : ℝ) := by
        push_cast
        rw [Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (rankCeiling : ℝ) *
          (A.card : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow (A.card : ℝ)]
  have hroundScaled : (D : ℝ) *
      (Real.sqrt (((r * Y.card : ℕ) : ℝ)) * K) ≤
      L * (A.card : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      (D : ℝ) *
          (Real.sqrt (((r * Y.card : ℕ) : ℝ)) * K) =
          ((D : ℝ) * K) *
            Real.sqrt (((r * Y.card : ℕ) : ℝ)) := by ring
      _ ≤ ((D : ℝ) * K) *
          (Real.sqrt (rankCeiling : ℝ) *
            (A.card : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hrho (mul_nonneg (by positivity) hK)
      _ = L * (A.card : ℝ) ^ ((1 : ℝ) / 2) := by
        simp only [L]
        ring
  have hscaled : (D : ℝ) *
      (Real.sqrt (((r * Y.card : ℕ) : ℝ)) * K) <
      (D : ℝ) * ((I.selectedCFP.dilation : ℝ) * gamma) := by
    calc
      (D : ℝ) *
          (Real.sqrt (((r * Y.card : ℕ) : ℝ)) * K) ≤
          L * (A.card : ℝ) ^ ((1 : ℝ) / 2) := hroundScaled
      _ < (A.card : ℝ) ^ p := hlarge.2.2.2
      _ ≤ (D : ℝ) * (I.selectedCFP.dilation : ℝ) * gamma := by
        simpa only [D] using hpoly
      _ = (D : ℝ) *
          ((I.selectedCFP.dilation : ℝ) * gamma) := by ring
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  exact ((mul_lt_mul_iff_of_pos_left hDreal).mp hscaled).le

/-! ## Elementary coefficient-budget helpers -/

/-- The inverse-cardinality cutoff used for the two high-coefficient pools. -/
def sourceCoefficientThreshold (N : ℕ) : ℝ :=
  ((16 : ℝ) * N)⁻¹

theorem sourceCoefficientThreshold_pos {N : ℕ} (hN : 0 < N) :
    0 < sourceCoefficientThreshold N := by
  unfold sourceCoefficientThreshold
  positivity

theorem card_mul_sourceCoefficientThreshold {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * sourceCoefficientThreshold N = (1 : ℝ) / 16 := by
  unfold sourceCoefficientThreshold
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Positivity of the convex coefficient cap follows from the source
parameter signs and nonemptiness of the retained core. -/
theorem inv_mu_mul_card_pos {alpha : Type*} {mu : ℝ} {S : Finset alpha}
    (hmu : 0 < mu) (hS : S.Nonempty) :
    0 < (mu * S.card)⁻¹ := by
  positivity

/-- The terminal core-retention inequality already makes the coefficient
cap positive; no separate core-nonemptiness hypothesis is needed. -/
theorem inv_mu_mul_coreCard_pos_of_coreRetention
    {N coreCard : ℕ} {delta mu : ℝ}
    (hN : 0 < N) (hdelta : 0 < delta) (hmu : 0 < mu)
    (hretention : delta * (N : ℝ) ≤
      ((((coreCard - 2) / 2 : ℕ) : ℝ))) :
    0 < (mu * coreCard)⁻¹ := by
  have hrightReal : (0 : ℝ) < (((coreCard - 2) / 2 : ℕ) : ℝ) :=
    (mul_pos hdelta (by exact_mod_cast hN)).trans_le hretention
  have hrightNat : 0 < (coreCard - 2) / 2 := by exact_mod_cast hrightReal
  have hcore : 0 < coreCard := by omega
  positivity

/-- A convenient sufficient condition for the exact mass budget used by
`exists_highCoefficient_side_selections_with_sourceControlBox`.  The two
small-cap premises are deliberately explicit: they do not follow uniformly
from `Theorem4Parameters` alone. -/
theorem sourceCoefficient_massBudget
    {N coreCard : ℕ} {delta mu : ℝ}
    (hN : 0 < N) (hcap : 0 < (mu * coreCard)⁻¹)
    (hcapSmall : (mu * coreCard)⁻¹ ≤ (1 : ℝ) / 16)
    (hscaledCap : delta * (N : ℝ) * (mu * coreCard)⁻¹ ≤
      (1 : ℝ) / 16) :
    (N : ℝ) * sourceCoefficientThreshold N +
        delta * (N : ℝ) * (mu * coreCard)⁻¹ <
      (1 - 2 * (mu * coreCard)⁻¹) / 2 := by
  rw [card_mul_sourceCoefficientThreshold hN]
  linarith

/-- An eligible CFP scale is a positive natural number, independently of
the value of its real exponent. -/
theorem eligibleInput_scale_pos
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    {d : ℕ} {X : Finset (LatticePoint d)}
    (I : Reduction.EligibleInput context X) : 0 < I.scale := by
  have hcard : (0 : ℝ) < X.card := by exact_mod_cast I.nonempty.card_pos
  have hpow : 0 < (X.card : ℝ) ^ eta := Real.rpow_pos_of_pos hcard _
  have hscaleReal : (0 : ℝ) < I.scale := hpow.trans_le I.scale_lower
  exact_mod_cast hscaleReal

/-! ## Exact rank-uniform source constants -/

def sourceControlDilation
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  2 * context.scaleDen r

def sourceControlBoxFactor
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  (sourceControlDilation context r + 1) ^ r * 2 ^ r

/-- Exact constant in the controlled-box full-rank criterion. -/
def sourceFullRankConstant
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  2 ^ r * (2 * r + 1) ^ (r - 1) * sourceControlBoxFactor context r

/-- Exact fixed factor multiplying the square-root rounding radius in the
source-control-box anisotropic adjugate criterion. -/
def sourceAnisotropicConstant
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  r.factorial * (2 * sourceControlDilation context r) ^ (r - 1) * 3 ^ r

def sourceFullRankConstantBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (rankCeiling + 1), sourceFullRankConstant context r

def sourceAnisotropicConstantBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (rankCeiling + 1), sourceAnisotropicConstant context r

theorem sourceFullRankConstant_le_bound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hr : r ≤ rankCeiling) :
    sourceFullRankConstant context r ≤
      sourceFullRankConstantBound context rankCeiling := by
  unfold sourceFullRankConstantBound
  exact Finset.single_le_sum (fun i _hi ↦ Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hr))

theorem sourceAnisotropicConstant_le_bound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hr : r ≤ rankCeiling) :
    sourceAnisotropicConstant context r ≤
      sourceAnisotropicConstantBound context rankCeiling := by
  unfold sourceAnisotropicConstantBound
  exact Finset.single_le_sum (fun i _hi ↦ Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hr))

/-- A single population threshold supplies both exact scalar hierarchies
needed for a selected side: full rank and anisotropic rounding. -/
theorem exists_cardThreshold_source_selectedSide_hierarchies
    {beta eta C C' : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : (1 : ℝ) / 2 < eta)
    (hC : 0 < C) :
    ∃ M : ℕ, ∀ {d : ℕ} (A : Finset (LatticePoint d))
      (delta gamma mu : ℝ),
      Theorem4Parameters A beta C C' M delta gamma mu →
      ∀ {r : ℕ} {X Y : Finset (LatticePoint r)}
        (I : Reduction.EligibleInput context X),
        r ≤ rankCeiling → Y.card ≤ A.card →
        delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        ((sourceFullRankConstant context r : ℕ) : ℝ) <
            (I.selectedCFP.dilation : ℝ) * gamma ∧
          Real.sqrt (((r * Y.card : ℕ) : ℝ)) *
              ((sourceAnisotropicConstant context r : ℕ) : ℝ) ≤
            (I.selectedCFP.dilation : ℝ) * gamma := by
  have heta0 : 0 < eta := by linarith
  obtain ⟨M₁, hM₁⟩ := exists_cardThreshold_selectedCFP_dilation_mul_gamma_gt
    context rankCeiling heta0 hC
      (sourceFullRankConstantBound context rankCeiling : ℝ)
  obtain ⟨M₂, hM₂⟩ :=
    exists_cardThreshold_sqrt_card_mul_le_selectedCFP_dilation_mul_gamma
      context rankCeiling heta hC
        (sourceAnisotropicConstantBound context rankCeiling : ℝ) (by positivity)
  let M := max M₁ M₂
  refine ⟨M, ?_⟩
  intro d A delta gamma mu hparams r X Y I hrank hYcard hdense
  have hparams₁ : Theorem4Parameters A beta C C' M₁ delta gamma mu := {
    hparams with
    card_large := (le_max_left M₁ M₂).trans hparams.card_large }
  have hparams₂ : Theorem4Parameters A beta C C' M₂ delta gamma mu := {
    hparams with
    card_large := (le_max_right M₁ M₂).trans hparams.card_large }
  have hfullBound := hM₁ A delta gamma mu hparams₁ I hrank hdense
  have hanisoBound := hM₂ A delta gamma mu hparams₂ I hrank hYcard hdense
  constructor
  · have hconstant : (sourceFullRankConstant context r : ℝ) ≤
        (sourceFullRankConstantBound context rankCeiling : ℝ) := by
      exact_mod_cast sourceFullRankConstant_le_bound context hrank
    exact hconstant.trans_lt hfullBound
  · have hconstant : (sourceAnisotropicConstant context r : ℝ) ≤
        (sourceAnisotropicConstantBound context rankCeiling : ℝ) := by
      exact_mod_cast sourceAnisotropicConstant_le_bound context hrank
    exact (mul_le_mul_of_nonneg_left hconstant
      (Real.sqrt_nonneg _)).trans hanisoBound

end

end Erdos186.PZ.Intersection

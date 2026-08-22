/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointBandSelector
import ErdosProblems.Erdos1165.HLOZGapBetaNumerics

/-!
# Numerical estimate for the spatially enumerated high deficit bands

Above the Proposition 4.8 range, HLOZ enumerate the lattice points in the
spatial mesh ball.  The deliberately loose natural budget below dominates
the containing coordinate square and has logarithm of order `m ^ alpha`.
For a large-deficit beta strip the return exponent exceeds `alpha` by a
fixed positive amount, so the same geometric-return estimate absorbs this
budget and any fixed multiple of `log m ^ 2`.
-/

open Filter Real
open scoped ENNReal

namespace Erdos1165.HLOZHighSpatialBudgetNumerics

open HLOZGapBetaArithmetic HLOZGapBetaNumerics HLOZGapMeshEscape
open HLOZPathEvents HLOZProposition48Candidates
open HLOZTilingEndpointBandSelector ScreeningInstantiation

noncomputable section

/-- A convenient integer upper bound for the number of lattice points in a
mesh-radius coordinate square. -/
def highSpatialCandidateBudget (m : ℕ) (a : GapScale) : ℕ :=
  Nat.ceil (100 * Real.exp (2 * (m : ℝ) ^ meshExponent a))

lemma highSpatialCandidateBudget_pos (m : ℕ) (a : GapScale) :
    0 < highSpatialCandidateBudget m a := by
  unfold highSpatialCandidateBudget
  exact Nat.ceil_pos.mpr (by positivity)

/-- The logarithm of the loose spatial budget has precisely the source
order `2 * m ^ alpha`, up to one harmless absolute constant. -/
theorem log_highSpatialCandidateBudget_le
    {m : ℕ} (hm : 1 ≤ m) (a : GapScale) :
    Real.log (highSpatialCandidateBudget m a) ≤
      Real.log 200 + 2 * (m : ℝ) ^ meshExponent a := by
  let p : ℝ := (m : ℝ) ^ meshExponent a
  let A : ℝ := 100 * Real.exp (2 * p)
  have hp : 1 ≤ p := by
    apply Real.one_le_rpow
    · exact_mod_cast hm
    · unfold meshExponent
      exact mul_nonneg (by positivity) (by norm_num [meshDelta])
  have hA : 1 ≤ A := by
    dsimp only [A]
    have : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
    nlinarith
  have hceil : (Nat.ceil A : ℝ) ≤ 2 * A := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ A by positivity)
    linarith
  have hbudgetPos : (0 : ℝ) < highSpatialCandidateBudget m a := by
    exact_mod_cast highSpatialCandidateBudget_pos m a
  have hupperPos : (0 : ℝ) < 2 * A := by positivity
  calc
    Real.log (highSpatialCandidateBudget m a) =
        Real.log (Nat.ceil A) := by
      rfl
    _ ≤ Real.log (2 * A) := Real.log_le_log hbudgetPos hceil
    _ = Real.log 200 + 2 * (m : ℝ) ^ meshExponent a := by
      dsimp only [A, p]
      rw [show 2 * (100 * Real.exp
          (2 * (m : ℝ) ^ meshExponent a)) =
          200 * Real.exp (2 * (m : ℝ) ^ meshExponent a) by ring]
      rw [Real.log_mul (by norm_num : (200 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), Real.log_exp]

/-- In every large-deficit strip the return exponent has a uniform power
advantage over the spatial lattice-point exponent. -/
theorem meshExponent_add_one_sixtyfourth_lt_returnExponent
    {a : GapScale} (ha : a ∈ lowGapMesh) {j : ℕ}
    (hlarge : (7 / 10 : ℝ) <
      deficitExponent48 (meshExponent a) (j + 1)) :
    meshExponent a + (1 / 64 : ℝ) <
      deficitExponent48 (meshExponent a) j - meshExponent a := by
  have halpha : meshExponent a ≤ kappaTwo :=
    (mem_lowGapMesh_iff.mp ha).2
  have hidentity := deficitExponent48_succ_sub_kappaOne
    (meshExponent a) j
  norm_num [kappaOne, kappaTwo, meshDelta] at hlarge halpha hidentity
  norm_num [kappaOne, kappaTwo, meshDelta]
  linarith

/-- The real logarithmic domination for one spatially enumerated high beta
strip. -/
theorem eventually_log_highSpatialBudget_add_log_sq_le_escape_returns
    (a : GapScale) (j : ℕ) (targetCoefficient : ℝ)
    (ha : a ∈ lowGapMesh)
    (hlarge : (7 / 10 : ℝ) <
      deficitExponent48 (meshExponent a) (j + 1)) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (highSpatialCandidateBudget m a) +
          targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
        meshPointEscapeChance m a *
          requiredReturns48 m
            (deficitExponent48 (meshExponent a) j) := by
  let betaPrev := deficitExponent48 (meshExponent a) j
  let epsilon : ℝ := 1 / 64
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgap : meshExponent a + epsilon < betaPrev - meshExponent a := by
    exact meshExponent_add_one_sixtyfourth_lt_returnExponent ha hlarge
  have halphaPos : 0 < meshExponent a := by
    unfold meshExponent
    exact mul_pos (by positivity) (by norm_num [meshDelta])
  have hpowAbsorb :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      400000 (meshExponent a) (betaPrev - meshExponent a)
      (by linarith)
  have hlogAbsorb := eventually_const_mul_log_sq_le_nat_rpow
    (1600 * targetCoefficient) epsilon hepsilon
  have hreturnExponent : 0 < betaPrev := by linarith
  have hreturnPower :=
    (tendsto_nat_rpow_atTop hreturnExponent).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hpowAbsorb, hlogAbsorb, hreturnPower,
      eventually_ge_atTop 2] with m hpowM hlogM hreturnM hm
  have hmOne : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmOne
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hlogTwoHundred : Real.log (200 : ℝ) ≤ 199 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 200)
    norm_num at h ⊢
    exact h
  have hbudget := log_highSpatialCandidateBudget_le hmOne a
  have hbudgetCoarse :
      Real.log (highSpatialCandidateBudget m a) ≤
        201 * (m : ℝ) ^ meshExponent a := by
    have hpowOne : 1 ≤ (m : ℝ) ^ meshExponent a := by
      apply Real.one_le_rpow hmR
      unfold meshExponent
      exact mul_nonneg (by positivity) (by norm_num [meshDelta])
    nlinarith
  have hbudgetPart :
      Real.log (highSpatialCandidateBudget m a) ≤
        (1 / 1600 : ℝ) * (m : ℝ) ^ (betaPrev - meshExponent a) := by
    have hpowAlphaNonneg : 0 ≤ (m : ℝ) ^ meshExponent a :=
      Real.rpow_nonneg (by positivity) _
    calc
      Real.log (highSpatialCandidateBudget m a) ≤
          201 * (m : ℝ) ^ meshExponent a := hbudgetCoarse
      _ ≤ (1 / 1600 : ℝ) *
          (m : ℝ) ^ (betaPrev - meshExponent a) := by
        nlinarith
  have hepsilonPow : (m : ℝ) ^ epsilon ≤
      (m : ℝ) ^ (betaPrev - meshExponent a) := by
    exact Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
  have hlogPart :
      targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
        (1 / 1600 : ℝ) *
          (m : ℝ) ^ (betaPrev - meshExponent a) := by
    have hscaled : 1600 *
        (targetCoefficient * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (betaPrev - meshExponent a) := by
      calc
        1600 * (targetCoefficient * Real.log (m : ℝ) ^ 2) =
            (1600 * targetCoefficient) * Real.log (m : ℝ) ^ 2 := by ring
        _ ≤ (m : ℝ) ^ epsilon := hlogM
        _ ≤ (m : ℝ) ^ (betaPrev - meshExponent a) := hepsilonPow
    nlinarith
  have hlower :=
    one_div_four_hundred_nat_rpow_sub_le_escape_mul_requiredReturns48
      hmOne a hreturnM
  dsimp only [betaPrev] at hlower ⊢
  exact (add_le_add hbudgetPart hlogPart).trans (by
    have hpowNonneg : 0 ≤
        (m : ℝ) ^
          (deficitExponent48 (meshExponent a) j - meshExponent a) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith)

/-- ENNReal form for one high strip. -/
theorem eventually_highSpatialBudget_mul_meshGeometricReturnCost_le_exp_neg
    (a : GapScale) (j : ℕ) (targetCoefficient : ℝ)
    (ha : a ∈ lowGapMesh)
    (hlarge : (7 / 10 : ℝ) <
      deficitExponent48 (meshExponent a) (j + 1)) :
    ∀ᶠ m : ℕ in atTop,
      (highSpatialCandidateBudget m a : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m a)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent a) j)) ≤
        ENNReal.ofReal
          (Real.exp (-targetCoefficient * Real.log (m : ℝ) ^ 2)) := by
  have hdomination :=
    eventually_log_highSpatialBudget_add_log_sq_le_escape_returns
      a j targetCoefficient ha hlarge
  filter_upwards [hdomination] with m hdominationM
  calc
    (highSpatialCandidateBudget m a : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m a)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent a) j)) ≤
        (highSpatialCandidateBudget m a : ℝ≥0∞) *
          Gap.exponentialReturnCost (meshPointEscapeChance m a)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent a) j)) := by
      gcongr
      exact Gap.geometricReturnCost_le_exponentialReturnCost
        (meshPointEscapeChance_pos m a).le
        (meshPointEscapeChance_le_one m a) _
    _ ≤ ENNReal.ofReal
          (Real.exp (-targetCoefficient * Real.log (m : ℝ) ^ 2)) :=
      by
        simpa only [Gap.exponentialReturnCost, neg_mul] using
          (Gap.ennreal_nat_mul_exp_neg_le_exp_neg
            (highSpatialCandidateBudget_pos m a) hdominationM)

/-- Uniform finite-template version used by the full high-band screen.  The
concrete bands may depend on the level; only their scale/index projections
and a fixed cardinal bound are retained. -/
theorem eventually_sum_dynamic_highSpatial_geometric_cost_le
    {Band : Type*}
    (bands : ℕ → Finset Band) (scale : Band → GapScale)
    (index : Band → ℕ) (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates, p.1 ∈ lowGapMesh)
    (hlarge : ∀ p ∈ templates,
      (7 / 10 : ℝ) < deficitExponent48 (meshExponent p.1) (p.2 + 1))
    (hprojects : ∀ m band, band ∈ bands m →
      (scale band, index band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        (highSpatialCandidateBudget m (scale band) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band))
                (index band))) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have heach : ∀ p ∈ templates, ∀ᶠ m : ℕ in atTop,
      (highSpatialCandidateBudget m p.1 : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m p.1)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent p.1) p.2)) ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro p hp
    exact eventually_highSpatialBudget_mul_meshGeometricReturnCost_le_exp_neg
      p.1 p.2 (2 * c) (hscale p hp) (hlarge p hp)
  have hall := (Finset.eventually_all templates).2 heach
  have habsorb :=
    eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg B hc
  filter_upwards [hall, habsorb] with m hallM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  have hterm : ∀ band ∈ bands m,
      (highSpatialCandidateBudget m (scale band) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band))
                (index band))) ≤ q := by
    intro band hband
    exact hallM (scale band, index band) (hprojects m band hband)
  calc
    ∑ band ∈ bands m,
        (highSpatialCandidateBudget m (scale band) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band))
                (index band))) ≤
        ∑ _band ∈ bands m, q := Finset.sum_le_sum hterm
    _ = ((bands m).card : ℝ≥0∞) * q := by simp
    _ ≤ (B : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast hcard m
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

end

end Erdos1165.HLOZHighSpatialBudgetNumerics

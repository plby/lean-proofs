/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerHierarchyArithmetic

/-!
# The eventual dyadic hierarchy for the separated initial stage

This file verifies the first genuinely asymptotic package: a polynomial
absorber and the full initial typicality loss are dominated by the ambient
order, while the sharp positive-level losses are dominated by the root size.
-/

namespace Erdos207

open scoped Classical NNReal

noncomputable section

def powerAbsorberCoefficient (q : ℕ) : ℕ :=
  highGirthAbsorberCardCoefficient (q + 2) * 2 ^ 156

lemma highGirthAbsorber_power_normalize (q t r : ℕ) :
    highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ r) ^ 156 =
      powerAbsorberCoefficient q * t ^ (156 * r) := by
  simp only [powerAbsorberCoefficient, mul_pow, ← pow_mul]
  ring

lemma powerAbsorberCoefficient_pos (q : ℕ) :
    0 < powerAbsorberCoefficient q := by
  unfold powerAbsorberCoefficient highGirthAbsorberCardCoefficient
    cycleCoverCardConstant
  positivity

/-- All six scalar hypotheses of the power-scheduled initial absorber package
follow from transparent comparisons of fixed coefficients with the base. -/
theorem initial_power_hierarchy_scalars
    {q h t rootPower step ell E n : ℕ}
    (ht : 1 ≤ t) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * ell + 1 ≤ E)
    (hcapacityBase : 1 + 2 * powerAbsorberCoefficient q ≤ t)
    (hdegreeBase : 1 + powerAbsorberCoefficient q ≤ t)
    (hextensionBase :
      (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤ t)
    (hrootDegreeBase : 15 ≤ t)
    (hrootExtensionBase : h + h ^ 2 * 36 ≤ t)
    (hn : t ^ E ≤ n) :
    highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156 ≤ n ∧
      t ^ (step * ell) + 2 *
        (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156) ≤ n ∧
      (t : ℝ≥0)⁻¹ ≤ 1 ∧
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156 + 1 : ℕ) : ℝ≥0) ≤
        (t : ℝ≥0)⁻¹ * (n : ℝ≥0) ∧
      (15 : ℝ≥0) ≤
        (t : ℝ≥0)⁻¹ * ((t ^ rootPower : ℕ) : ℝ≥0) ∧
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156)) : ℕ) : ℝ≥0) ≤
        (t : ℝ≥0)⁻¹ * (n : ℝ≥0) ∧
      (h + h ^ 2 * 36 : ℝ≥0) ≤
        (t : ℝ≥0)⁻¹ * ((t ^ rootPower : ℕ) : ℝ≥0) := by
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have hAbs : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156 = c * t ^ b := by
    exact highGirthAbsorber_power_normalize q t rootPower
  have hb1 : b + 1 ≤ E := by
    dsimp only [b]
    omega
  have hb2 : b + 2 ≤ E := by
    simpa only [b] using habsorberExp
  have hc : c ≤ t := by
    dsimp only [c] at ⊢
    omega
  have hc2 : 1 + 2 * c ≤ t := by
    simpa only [c] using hcapacityBase
  have hc1 : 1 + c ≤ t := by
    simpa only [c] using hdegreeBase
  have htpos : 0 < t := Nat.zero_lt_one.trans_le ht
  have hAbsPow : c * t ^ b ≤ t ^ E :=
    coeff_mul_pow_le_pow ht hc hb1
  have habs : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156 ≤ n := by
    rw [hAbs]
    exact hAbsPow.trans hn
  refine ⟨habs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAbs]
    simpa only [Nat.mul_assoc] using
      (pow_add_coeff_mul_pow_le_pow ht hc2 hfreeExp hb1).trans hn
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast ht)
  · apply cast_le_inv_mul_of_mul_le htpos
    rw [hAbs]
    have hpow : t ^ 1 + c * t ^ (b + 1) ≤ t ^ E :=
      pow_add_coeff_mul_pow_le_pow ht hc1 (by omega) hb2
    calc
      t * (c * t ^ b + 1) = t ^ 1 + c * t ^ (b + 1) := by
        rw [pow_one, pow_succ]
        ring
      _ ≤ t ^ E := hpow
      _ ≤ n := hn
  · rw [inv_mul_cast_pow_eq_cast_pow_pred htpos (by omega)]
    exact_mod_cast fixed_le_pow_of_fixed_le_base hrootDegreeBase (by omega)
  · apply cast_le_inv_mul_of_mul_le htpos
    rw [hAbs]
    let d := h + 3 * h ^ 2
    have hdc : d * c ≤ t := by
      simpa only [d, c] using hextensionBase
    have hAbsOne : 1 ≤ c * t ^ b := by
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
        (powerAbsorberCoefficient_pos q).ne' (pow_ne_zero _ htpos.ne'))
    have hinside : h + h ^ 2 * (3 * (c * t ^ b)) ≤
        d * (c * t ^ b) := by
      dsimp only [d]
      nlinarith
    calc
      t * (h + h ^ 2 * (3 * (c * t ^ b))) ≤
          t * (d * (c * t ^ b)) := Nat.mul_le_mul_left t hinside
      _ = (d * c) * t ^ (b + 1) := by
        rw [pow_succ]
        ring
      _ ≤ t ^ E := coeff_mul_pow_le_pow ht hdc hb2
      _ ≤ n := hn
  · rw [inv_mul_cast_pow_eq_cast_pow_pred htpos (by omega)]
    exact_mod_cast fixed_le_pow_of_fixed_le_base hrootExtensionBase (by omega)

/-- For fixed exponents satisfying the two strict gaps, the entire initial
absorber/vortex package exists at every sufficiently large ambient order. -/
theorem eventually_exists_paddedAbsorber_with_initial_power_typicality
    (q h rootPower step ell E : ℕ)
    (hell : 0 < ell) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * ell + 1 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
        ∃ B : TripleSystemOn (Fin n), ∃ W : Vortex (Fin n) ell,
          X.card = (dyadicPowerScale E n) ^ rootPower ∧
          W = separatedCardinalVortex H X B
            (powerFreeSize (dyadicPowerScale E n) step ell)
            (powerFreeSize_antitone (dyadicPowerScale E n) step ell
              (one_le_dyadicPowerScale E n)) ∧
          W.U (Fin.last ell) = X ∧
          (∀ i, i ≠ 0 →
            (W.U i).card = (dyadicPowerScale E n) ^ rootPower +
              powerFreeSize (dyadicPowerScale E n) step ell i) ∧
          (∀ i, (W.U i).Nonempty) ∧
          HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          (verticesOn B).card ≤
            highGirthAbsorberCardCoefficient (q + 2) *
              (2 * (dyadicPowerScale E n) ^ rootPower) ^ 156 ∧
          (graphSupportFinset H).card ≤
            highGirthAbsorberCardCoefficient (q + 2) *
              (2 * (dyadicPowerScale E n) ^ rootPower) ^ 156 ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) *
              (2 * (dyadicPowerScale E n) ^ rootPower) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * (dyadicPowerScale E n) ^ rootPower) ^ 156) ^ 3 ∧
          HasPaddedAbsorberRootBounds q H X B ∧
          HasPaddedAbsorberRootLocalization q X B ∧
          IsIterationTypical W 0
            (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
            (absorberGreedyInitialState
              (absorberErdosForbiddenConfigurationsOn q B)
              (outsideAvailableTriangles H B)).available
            1 1 (dyadicPowerScale E n : ℝ≥0)⁻¹ h := by
  let K := max (1 + 2 * powerAbsorberCoefficient q)
    (max (1 + powerAbsorberCoefficient q)
      (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
        (max 15 (h + h ^ 2 * 36))))
  have hE : 0 < E := by omega
  obtain ⟨N₁, hN₁⟩ := eventually_le_dyadicPowerScale hE K
  let N₀ := max N₁ 1
  refine ⟨N₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hscale := hN₁ n (le_trans (le_max_left _ _) hn)
  let t := dyadicPowerScale E n
  have ht : 1 ≤ t := one_le_dyadicPowerScale E n
  have hcap : 1 + 2 * powerAbsorberCoefficient q ≤ t := by
    exact (le_max_left _ _).trans hscale
  have hdeg : 1 + powerAbsorberCoefficient q ≤ t := by
    calc
      1 + powerAbsorberCoefficient q ≤
          max (1 + powerAbsorberCoefficient q)
            (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
              (max 15 (h + h ^ 2 * 36))) := le_max_left _ _
      _ ≤ K := le_max_right _ _
      _ ≤ t := hscale
  have hext : (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤ t := by
    calc
      (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤
          max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
            (max 15 (h + h ^ 2 * 36)) := le_max_left _ _
      _ ≤ max (1 + powerAbsorberCoefficient q)
          (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
            (max 15 (h + h ^ 2 * 36))) := le_max_right _ _
      _ ≤ K := le_max_right _ _
      _ ≤ t := hscale
  have hrootDeg : 15 ≤ t := by
    calc
      15 ≤ max 15 (h + h ^ 2 * 36) := le_max_left _ _
      _ ≤ max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
          (max 15 (h + h ^ 2 * 36)) := le_max_right _ _
      _ ≤ max (1 + powerAbsorberCoefficient q)
          (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
            (max 15 (h + h ^ 2 * 36))) := le_max_right _ _
      _ ≤ K := le_max_right _ _
      _ ≤ t := hscale
  have hrootExt : h + h ^ 2 * 36 ≤ t := by
    calc
      h + h ^ 2 * 36 ≤ max 15 (h + h ^ 2 * 36) := le_max_right _ _
      _ ≤ max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
          (max 15 (h + h ^ 2 * 36)) := le_max_right _ _
      _ ≤ max (1 + powerAbsorberCoefficient q)
          (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
            (max 15 (h + h ^ 2 * 36))) := le_max_right _ _
      _ ≤ K := le_max_right _ _
      _ ≤ t := hscale
  have htn : t ^ E ≤ n := dyadicPowerScale_pow_le (by omega)
  have hs := initial_power_hierarchy_scalars ht hroot habsorberExp
    hfreeExp hcap hdeg hext hrootDeg hrootExt htn
  exact exists_paddedAbsorber_with_initial_power_typicality hell ht hs.1
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1
    hs.2.2.2.2.2.2

end

end Erdos207

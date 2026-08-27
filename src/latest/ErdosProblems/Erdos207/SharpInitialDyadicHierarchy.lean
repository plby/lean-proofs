/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPowerVortexPackage

/-!
# Sharp first-level dyadic hierarchy

The level-zero value of `powerFreeSize` is never used by the separated
vortex.  Budgeting only positive levels permits the first genuine vortex
level to have exponent `E - 1`, which is the scale required by the long
initial sparsification.
-/

namespace Erdos207

open scoped Classical NNReal

noncomputable section

/-- The old scalar package, applied to `ell - 1`, gives exactly the sharper
positive-level capacity estimate. -/
theorem initial_power_hierarchy_scalars_sharp
    {q h t rootPower step ell E n : ℕ}
    (ht : 1 ≤ t) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * (ell - 1) + 1 ≤ E)
    (hcapacityBase : 1 + 2 * powerAbsorberCoefficient q ≤ t)
    (hdegreeBase : 1 + powerAbsorberCoefficient q ≤ t)
    (hextensionBase :
      (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤ t)
    (hrootDegreeBase : 15 ≤ t)
    (hrootExtensionBase : h + h ^ 2 * 36 ≤ t)
    (hn : t ^ E ≤ n) :
    highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156 ≤ n ∧
      t ^ (step * (ell - 1)) + 2 *
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
  exact initial_power_hierarchy_scalars (ell := ell - 1) ht hroot
    habsorberExp hfreeExp hcapacityBase hdegreeBase hextensionBase
    hrootDegreeBase hrootExtensionBase hn

/-- At every sufficiently large order, the packaged vortex exists with the
first positive free level allowed to reach exponent `step * (ell - 1)`. -/
theorem eventually_exists_initialPowerVortexPackage_sharp
    (q h rootPower step ell E : ℕ)
    (hell : 0 < ell) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * (ell - 1) + 1 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Nonempty (InitialPowerVortexPackage q h n ell
        (dyadicPowerScale E n) rootPower step) := by
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
  have hcap : 1 + 2 * powerAbsorberCoefficient q ≤ t :=
    (le_max_left _ _).trans hscale
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
  have hs := initial_power_hierarchy_scalars_sharp ht hroot habsorberExp
    hfreeExp hcap hdeg hext hrootDeg hrootExt htn
  obtain ⟨H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
      hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
      hrootLocalization, htyp⟩ :=
    exists_paddedAbsorber_with_initial_power_typicality_sharp hell ht hs.1
      hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1
      hs.2.2.2.2.2.2
  exact ⟨⟨ht, H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
    hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
    hrootLocalization, htyp⟩⟩

end

end Erdos207

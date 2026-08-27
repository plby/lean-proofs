/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpInitialDyadicHierarchy

/-!
# Fine-error initial power vortices

The long initial removal phase needs an initial additive degree error far
below the error amplified by the coupled upper/lower trajectories.  We
therefore construct the same power vortex with error `t⁻²⁰⁰`.  Its
monotonicity image at error `t⁻¹` is
retained in the inherited package for compatibility with existing APIs.
-/

namespace Erdos207

open scoped Classical NNReal

noncomputable section

def fineInitialExponent : ℕ := 200

def fineInitialError (t : ℕ) : ℝ≥0 :=
  (t : ℝ≥0)⁻¹ ^ fineInitialExponent

lemma fineInitialError_le_inv {t : ℕ} (ht : 1 ≤ t) :
    fineInitialError t ≤ (t : ℝ≥0)⁻¹ := by
  have hx : (t : ℝ≥0)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast ht)
  unfold fineInitialError
  rw [show fineInitialExponent = 199 + 1 by rfl, pow_add, pow_one]
  calc
    (t : ℝ≥0)⁻¹ ^ 199 * (t : ℝ≥0)⁻¹ ≤
        1 * (t : ℝ≥0)⁻¹ := by
      gcongr
      exact pow_le_one₀ (by positivity) hx
    _ = (t : ℝ≥0)⁻¹ := one_mul _

structure FineInitialPowerVortexPackage
    (q h n ell t rootPower step : ℕ)
    extends InitialPowerVortexPackage q h n ell t rootPower step where
  typicalFine : IsIterationTypical W 0
    (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
    (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available
    1 1 (fineInitialError t) h

/-- All initial construction inequalities with the finer error
`t⁻fineInitialExponent`. -/
theorem fine_initial_power_hierarchy_scalars
    {q h t rootPower step ell E n : ℕ}
    (ht : 1 ≤ t) (hroot : fineInitialExponent + 1 ≤ rootPower)
    (habsorberExp : 156 * rootPower + fineInitialExponent + 1 ≤ E)
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
      fineInitialError t ≤ 1 ∧
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156 + 1 : ℕ) : ℝ≥0) ≤
        fineInitialError t * (n : ℝ≥0) ∧
      (15 : ℝ≥0) ≤
        fineInitialError t * ((t ^ rootPower : ℕ) : ℝ≥0) ∧
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156)) : ℕ) : ℝ≥0) ≤
        fineInitialError t * (n : ℝ≥0) ∧
      (h + h ^ 2 * 36 : ℝ≥0) ≤
        fineInitialError t * ((t ^ rootPower : ℕ) : ℝ≥0) := by
  norm_num [fineInitialExponent] at hroot habsorberExp
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have htpos : 0 < t := Nat.zero_lt_one.trans_le ht
  have hb2 : b + 2 ≤ E := by dsimp only [b]; omega
  have hbFine : b + fineInitialExponent + 1 ≤ E := by
    dsimp only [b, fineInitialExponent]
    omega
  have hs := initial_power_hierarchy_scalars_sharp ht
    (show 2 ≤ rootPower by omega) hb2 hfreeExp hcapacityBase hdegreeBase
    hextensionBase hrootDegreeBase hrootExtensionBase hn
  refine ⟨hs.1, hs.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : (t : ℝ≥0)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast ht)
    exact pow_le_one₀ (by positivity) hx
  · apply cast_le_inv_pow_mul_of_pow_mul_le htpos
    rw [highGirthAbsorber_power_normalize]
    have hpow : t ^ fineInitialExponent +
        c * t ^ (b + fineInitialExponent) ≤ t ^ E :=
      pow_add_coeff_mul_pow_le_pow ht (by simpa only [c] using hdegreeBase)
        (by omega) hbFine
    calc
      t ^ fineInitialExponent * (c * t ^ b + 1) =
          t ^ fineInitialExponent + c * t ^ (b + fineInitialExponent) := by
        rw [pow_add]
        ring
      _ ≤ t ^ E := hpow
      _ ≤ n := hn
  · apply cast_le_inv_pow_mul_of_pow_mul_le htpos
    exact (by
      simpa [Nat.mul_comm] using
        coeff_mul_pow_le_pow ht hrootDegreeBase
          (show fineInitialExponent + 1 ≤ rootPower by
            simpa only [fineInitialExponent] using hroot))
  · apply cast_le_inv_pow_mul_of_pow_mul_le htpos
    rw [highGirthAbsorber_power_normalize]
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
      t ^ fineInitialExponent * (h + h ^ 2 * (3 * (c * t ^ b))) ≤
          t ^ fineInitialExponent * (d * (c * t ^ b)) :=
        Nat.mul_le_mul_left _ hinside
      _ = (d * c) * t ^ (b + fineInitialExponent) := by rw [pow_add]; ring
      _ ≤ t ^ E := coeff_mul_pow_le_pow ht hdc hbFine
      _ ≤ n := hn
  · have hraw : ((h + h ^ 2 * 36 : ℕ) : ℝ≥0) ≤
        fineInitialError t * ((t ^ rootPower : ℕ) : ℝ≥0) := by
      unfold fineInitialError
      apply cast_le_inv_pow_mul_of_pow_mul_le
        (k := fineInitialExponent) htpos
      exact (by
        simpa [Nat.mul_comm] using
          coeff_mul_pow_le_pow ht hrootExtensionBase
            (show fineInitialExponent + 1 ≤ rootPower by
              simpa only [fineInitialExponent] using hroot))
    norm_num at hraw ⊢
    exact hraw

/-- Eventual existence of the fine-error package. -/
theorem eventually_exists_fineInitialPowerVortexPackage
    (q h rootPower step ell E : ℕ)
    (hell : 0 < ell) (hroot : fineInitialExponent + 1 ≤ rootPower)
    (habsorberExp :
      156 * rootPower + fineInitialExponent + 1 ≤ E)
    (hfreeExp : step * (ell - 1) + 1 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Nonempty (FineInitialPowerVortexPackage q h n ell
        (dyadicPowerScale E n) rootPower step) := by
  norm_num [fineInitialExponent] at hroot habsorberExp
  let K := max (1 + 2 * powerAbsorberCoefficient q)
    (max (1 + powerAbsorberCoefficient q)
      (max ((h + 3 * h ^ 2) * powerAbsorberCoefficient q)
        (max 15 (h + h ^ 2 * 36))))
  obtain ⟨N₁, hN₁⟩ := eventually_le_dyadicPowerScale
    (show 0 < E by omega) K
  refine ⟨max N₁ 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right N₁ 1).trans hn
  have hscale := hN₁ n ((le_max_left N₁ 1).trans hn)
  let t := dyadicPowerScale E n
  have ht : 1 ≤ t := one_le_dyadicPowerScale E n
  have hcap : 1 + 2 * powerAbsorberCoefficient q ≤ t :=
    (le_max_left _ _).trans hscale
  have hdeg : 1 + powerAbsorberCoefficient q ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have hext : (h + 3 * h ^ 2) * powerAbsorberCoefficient q ≤ t :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hscale))
  have hrootDeg : 15 ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hscale)))
  have hrootExt : h + h ^ 2 * 36 ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hscale)))
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
  have htn : t ^ E ≤ n := dyadicPowerScale_pow_le hnpos.ne'
  have hs := fine_initial_power_hierarchy_scalars ht hroot habsorberExp
    hfreeExp hcap hdeg hext hrootDeg hrootExt htn
  obtain ⟨H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
      hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
      hrootLocalization, htypFine⟩ :=
    exists_paddedAbsorber_with_initial_power_typicality_sharp hell ht hs.1
      hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1
      hs.2.2.2.2.2.2
  have htyp := htypFine.mono_error (fineInitialError_le_inv ht)
  exact ⟨⟨⟨ht, H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
    hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
    hrootLocalization, htyp⟩, htypFine⟩⟩

end

end Erdos207

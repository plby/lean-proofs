/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroRectangle

/-!
# Separated detected zero ordinates

At fixed conductor and scale, choose a maximal separated family of ordinates
from the finite high-zero rectangle.  Each selected ordinate carries a
specific zero and hence a detector order in the common finite range.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

/-- A finite ordinate set has a separated subfamily which covers it. -/
theorem exists_separated_highZeroOrdinates
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (eta T r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Finset ℝ,
      S ⊆ highZeroOrdinates hq chi hchi eta T ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r < dist x y) ∧
        ∀ x ∈ highZeroOrdinates hq chi hchi eta T,
          ∃ y ∈ S, dist x y ≤ r := by
  let A : Set ℝ := highZeroOrdinates hq chi hchi eta T
  have hA : A.Finite := (highZeroOrdinates hq chi hchi eta T).finite_toSet
  obtain ⟨S, hSsub, hSfinite, hsep, hcover⟩ :=
    exists_finite_separated_cover A hA r hr
  refine ⟨hSfinite.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have hxS : x ∈ S := hSfinite.mem_toFinset.mp hx
    exact hSsub hxS
  · intro x hx y hy hxy
    exact hsep x (hSfinite.mem_toFinset.mp hx)
      y (hSfinite.mem_toFinset.mp hy) hxy
  · intro x hx
    obtain ⟨y, hyS, hxy⟩ := hcover x hx
    exact ⟨y, hSfinite.mem_toFinset.mpr hyS, hxy⟩

private theorem highZero_dist_detector_center_le
    {rho : ℂ} {t eta : ℝ}
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (hrhoim : rho.im = t) (heta : 0 < eta) :
    dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta := by
  rw [Complex.dist_eq]
  have heq :
      rho - (((1 + eta : ℝ) : ℂ) + t * I) =
        ((rho.re - (1 + eta) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hrhoim]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  linarith

theorem log_height_mono
    {q : ℕ} [NeZero q] {t T : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤
      Real.log ((q : ℝ) * (T + 2)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hleft : 0 < (q : ℝ) * (|t| + 2) := by positivity
  have hright : 0 < (q : ℝ) * (T + 2) := by
    have : 0 ≤ T := ht0.trans htT
    positivity
  apply Real.strictMonoOn_log.monotoneOn hleft hright
  rw [abs_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left (by linarith) hq.le

/-- Uniform separated selection carrying both detector orders and propagated
lower bounds.  The global logarithmic-height hypothesis implies the detector
hypothesis at every selected ordinate. -/
theorem exists_uniform_detected_zero_selection :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∀ (eta T : ℝ), 0 < eta → eta ≤ 1 / 8 → 0 ≤ T →
              eta * Real.log ((q : ℝ) * (T + 2)) ≤ lambda →
                ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
                  S ⊆ highZeroOrdinates hq chi hchi eta T ∧
                  (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
                    2 * delta * eta < dist x y) ∧
                  (∀ x ∈ highZeroOrdinates hq chi hchi eta T,
                    ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
                  ∀ t ∈ S,
                    L ≤ order t ∧ order t ≤ J ∧
                      ∀ u : ℝ, |u - t| ≤ delta * eta →
                        (order t - 1).factorial * (1 / 48 : ℝ) *
                            (2 * eta)⁻¹ ^ order t <
                          ‖finiteZeroDetectorPolynomial chi eta (order t - 1)
                            (zeroDetectorCutoff R eta) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, delta,
      hlambda, hR, hdelta, hdelta1, hdetector⟩ :=
    exists_uniform_propagated_finite_series_detector
  refine ⟨L, J, hL2, hLJ, lambda, R, delta,
    hlambda, hR, hdelta, hdelta1, ?_⟩
  intro q _ hq chi hchi eta T heta heta8 hT hglobal
  obtain ⟨S, hSsub, hsep, hcover⟩ :=
    exists_separated_highZeroOrdinates hq chi hchi eta T
      (2 * delta * eta) (by positivity)
  have hdet : ∀ t ∈ S, ∃ j : ℕ,
      L ≤ j ∧ j ≤ J ∧
        ∀ u : ℝ, |u - t| ≤ delta * eta →
          (j - 1).factorial * (1 / 48 : ℝ) *
              (2 * eta)⁻¹ ^ j <
            ‖finiteZeroDetectorPolynomial chi eta (j - 1)
              (zeroDetectorCutoff R eta) u‖ := by
    intro t ht
    have htOrd := hSsub ht
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht0, htT⟩ :=
      (mem_highZeroOrdinates_iff hq chi hchi (by linarith) hT t).mp htOrd
    have hlog :
        eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda := by
      exact (mul_le_mul_of_nonneg_left
        (log_height_mono ht0 htT) heta.le).trans hglobal
    exact hdetector q hq chi hchi t eta heta heta8 hlog rho hzero
      (highZero_dist_detector_center_le hrelo hrehi hrhoim heta)
  let order : ℝ → ℕ := fun t ↦
    if ht : t ∈ S then Classical.choose (hdet t ht) else L
  have horder : ∀ t ∈ S,
      L ≤ order t ∧ order t ≤ J ∧
        ∀ u : ℝ, |u - t| ≤ delta * eta →
          (order t - 1).factorial * (1 / 48 : ℝ) *
              (2 * eta)⁻¹ ^ order t <
            ‖finiteZeroDetectorPolynomial chi eta (order t - 1)
              (zeroDetectorCutoff R eta) u‖ := by
    intro t ht
    rw [show order t = Classical.choose (hdet t ht) by simp [order, ht]]
    exact Classical.choose_spec (hdet t ht)
  exact ⟨S, order, hSsub, hsep, hcover, horder⟩

end

end Erdos48

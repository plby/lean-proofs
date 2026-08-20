/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroDetectorParameters

/-!
# A uniform finite-order pointwise zero detector

The scale-sensitive local zero count and the numerical error-budget lemma
make the range of derivative orders in the pointwise detector independent of
the character, conductor, height, and zero.  This is the finite-order form
needed before truncating the logarithmic-derivative Dirichlet series.
-/

namespace Erdos48

open Complex Metric
open BoundedGaps.Maynard

noncomputable section

/-- There are fixed orders `L <= J` and a fixed positive width `lambda` such
that every primitive Dirichlet `L`-function zero in the indicated log-free
region forces one of the derivatives of orders `L-1,...,J-1` to be large. -/
theorem exists_uniform_pointwise_zero_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
              eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda →
                ∀ rho₀ : ℂ,
                  DirichletCharacter.LFunction chi rho₀ = 0 →
                  dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                    ∃ j : ℕ,
                      L ≤ j ∧ j ≤ J ∧
                        (j - 1).factorial * (1 / 12 : ℝ) *
                            (2 * eta)⁻¹ ^ j <
                          ‖iteratedDeriv (j - 1)
                            (fun w ↦ -logDeriv
                              (DirichletCharacter.LFunction chi) w)
                            (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, hdetector⟩ :=
    exists_pointwise_zero_detector_of_error_budget
  obtain ⟨L, hL2, lambda, hlambda, hparameters⟩ :=
    exists_pointwiseZeroDetector_parameters Al Af Ad
  obtain ⟨Am', hAm', hmass⟩ := exists_smallDiskZeroMultiplicity_bound
  let C : ℝ := Real.log 4 + 4
  let M0 : ℝ := 18 * C + (256 * (Am' : ℝ) / 3) * lambda
  let M : ℕ := Nat.ceil M0
  let J : ℕ := L * M
  have hC : 0 < C := by dsimp [C]; positivity
  have hM0 : 0 < M0 := by
    dsimp [M0]
    positivity
  have hMpos : 0 < M := Nat.ceil_pos.mpr hM0
  have hLJ : L ≤ J := by
    dsimp [J]
    exact Nat.le_mul_of_pos_right L hMpos
  refine ⟨L, J, hL2, hLJ, lambda, hlambda, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 hetalog rho₀ hzero hrho
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  have hB4 : 4 ≤ (q : ℝ) * (|t| + 2) := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hmass' := hmass q hq chi hchi t eta heta0 (by linarith : eta ≤ 1)
  have hfirst :
      16 * C * (1 + eta) ≤ 18 * C := by
    nlinarith
  have hsecond :
      (256 * (Am' : ℝ) / 3) * eta *
          Real.log ((q : ℝ) * (|t| + 2)) ≤
        (256 * (Am' : ℝ) / 3) * lambda := by
    calc
      (256 * (Am' : ℝ) / 3) * eta *
          Real.log ((q : ℝ) * (|t| + 2)) =
          (256 * (Am' : ℝ) / 3) *
            (eta * Real.log ((q : ℝ) * (|t| + 2))) := by ring
      _ ≤ (256 * (Am' : ℝ) / 3) * lambda :=
        mul_le_mul_of_nonneg_left hetalog (by positivity)
  have hmassM0 : Z.sum (fun _ m ↦ (m : ℝ)) ≤ M0 := by
    calc
      Z.sum (fun _ m ↦ (m : ℝ)) ≤
          16 * C * (1 + eta) +
            (256 * (Am' : ℝ) / 3) * eta *
              Real.log ((q : ℝ) * (|t| + 2)) := by
        simpa only [Z, C] using hmass'
      _ ≤ 18 * C + (256 * (Am' : ℝ) / 3) * lambda :=
        add_le_add hfirst hsecond
      _ = M0 := rfl
  have hmassM : Z.sum (fun _ m ↦ m) ≤ M := by
    have hcast :
        ((Z.sum (fun _ m ↦ m) : ℕ) : ℝ) ≤ (M : ℝ) := by
      rw [Nat.cast_finsupp_sum]
      exact hmassM0.trans (Nat.le_ceil M0)
    exact_mod_cast hcast
  have hbudget :
      ∀ j : ℕ, L ≤ j → j ≤ L * Z.sum (fun _ m ↦ m) →
        pointwiseZeroDetectorError Al Af Ad q t eta j ≤
          (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
    intro j hjL hjupper
    exact hparameters q t eta j hB4 heta0 heta8 hetalog hjL
  obtain ⟨j, hjL, hjZ, hjlarge⟩ :=
    hdetector q hq chi hchi t eta heta0 heta8 rho₀ hzero hrho
      L hL2 hbudget
  refine ⟨j, hjL, ?_, hjlarge⟩
  exact hjZ.trans (Nat.mul_le_mul_left L hmassM)

end

end Erdos48

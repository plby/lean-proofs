import ErdosProblems.Erdos67.MRFiniteHalaszFixedBand
import ErdosProblems.Erdos67.MRFiniteHalaszSmoothing

/-!
# Mellin smoothing of one complete finite-Halasz factor

The selected prime band must remain a complete Euler factor in order to use
nonpretentious Euler suppression.  This file extends the finite smoothing
identity to an absolutely convergent L-series.  The interchange is justified
directly by summability of the L-series terms and integrability of the
Schwartz kernel.  Compact support of the inverse transform means the final
coefficient sum is nevertheless finite on every bounded logarithmic window;
there is no comparison between a complete series and a truncated tail.
-/

open scoped BigOperators LSeries.notation
open Complex Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.MRFiniteHalaszSmoothing

/-- Exact countable smoothing identity for an absolutely convergent
L-series.  The vertical frequency is `t0 - 2πξ`, matching the sign in the
finite logarithmic-polynomial convention. -/
theorem integral_LSeries_mul_logTrapezoidKernel
    (a : ℕ → ℂ) (sigma : ℝ)
    (hsum : LSeriesSummable a (sigma : ℂ))
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        LSeries a
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∑' n : ℕ,
        LSeries.term a (sigma : ℂ) n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  let s0 : ℂ := (sigma : ℂ)
  let sAt : ℝ → ℂ := fun xi ↦
    (sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)
  let K : ℝ → ℂ := logTrapezoidKernel delta A B hdelta
  let F : ℕ → ℝ → ℂ := fun n xi ↦ LSeries.term a (sAt xi) n * K xi
  have hK : Integrable K := integrable_logTrapezoidKernel delta A B hdelta
  have hnormTerm (n : ℕ) (xi : ℝ) :
      ‖LSeries.term a (sAt xi) n‖ = ‖LSeries.term a s0 n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    simp [sAt, s0]
  have htermPhase (n : ℕ) (xi : ℝ) :
      LSeries.term a (sAt xi) n =
        LSeries.term a s0 n *
          logarithmicPhase n (-t0 + 2 * Real.pi * xi) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      dsimp [sAt, s0]
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        div_eq_mul_inv, div_eq_mul_inv, ← Complex.cpow_neg,
        ← Complex.cpow_neg]
      rw [← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg
        hnpos sigma (t0 - 2 * Real.pi * xi)]
      have hreal : (n : ℂ) ^ (-((sigma : ℝ) : ℂ)) =
          Complex.ofReal ((n : ℝ) ^ (-sigma)) := by
        simpa using
          (Complex.ofReal_cpow (show (0 : ℝ) ≤ n by positivity) (-sigma)).symm
      rw [hreal]
      have hphase :
          logarithmicPhase n (-(t0 - 2 * Real.pi * xi)) =
            logarithmicPhase n (-t0 + 2 * Real.pi * xi) := by
        unfold logarithmicPhase
        congr 1
        push_cast
        ring
      rw [hphase]
      ring
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    have hmajor : Integrable (fun xi : ℝ ↦ ‖LSeries.term a s0 n‖ * ‖K xi‖) :=
      hK.norm.const_mul _
    refine hmajor.mono' ?_ ?_
    · have htermMeas : AEStronglyMeasurable (fun xi : ℝ ↦
          LSeries.term a (sAt xi) n) := by
        rw [show (fun xi : ℝ ↦ LSeries.term a (sAt xi) n) =
              fun xi ↦ LSeries.term a s0 n *
                logarithmicPhase n (-t0 + 2 * Real.pi * xi) by
          funext xi
          exact htermPhase n xi]
        have hc : Continuous (fun xi : ℝ ↦
            LSeries.term a s0 n *
              logarithmicPhase n (-t0 + 2 * Real.pi * xi)) := by
          unfold logarithmicPhase
          fun_prop
        exact hc.aestronglyMeasurable
      exact htermMeas.mul hK.aestronglyMeasurable
    · filter_upwards with xi
      rw [norm_mul, hnormTerm]
  have hintNorm (n : ℕ) :
      (∫ xi : ℝ, ‖F n xi‖) =
        ‖LSeries.term a s0 n‖ * logTrapezoidKernelMass delta A B hdelta := by
    simp_rw [F, norm_mul, hnormTerm]
    rw [integral_const_mul]
    rfl
  have hsumInt : Summable (fun n : ℕ ↦ ∫ xi : ℝ, ‖F n xi‖) := by
    rw [show (fun n : ℕ ↦ ∫ xi : ℝ, ‖F n xi‖) =
        fun n ↦ ‖LSeries.term a s0 n‖ *
          logTrapezoidKernelMass delta A B hdelta by
      funext n
      exact hintNorm n]
    exact Summable.mul_right _ hsum.norm
  have hinterchange :
      (∑' n : ℕ, ∫ xi : ℝ, F n xi) =
        ∫ xi : ℝ, ∑' n : ℕ, F n xi :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumInt
  have hterm (n : ℕ) :
      (∫ xi : ℝ, F n xi) =
        LSeries.term a s0 n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
    by_cases hn : n = 0
    · subst n
      simp [F, sAt, s0]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsingle :=
        integral_logarithmicDirichletPolynomial_mul_kernel
          ({n} : Finset ℕ) (fun _ ↦ LSeries.term a s0 n)
          delta A B hdelta t0
      simpa only [F, K, htermPhase, logarithmicDirichletPolynomial,
        Finset.sum_singleton] using hsingle
  calc
    (∫ xi : ℝ,
        LSeries a
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∫ xi : ℝ, ∑' n : ℕ, F n xi := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [show (∑' n : ℕ, F n xi) = LSeries a (sAt xi) * K xi by
          simp only [F, LSeries, tsum_mul_right]]
    _ = ∑' n : ℕ, ∫ xi : ℝ, F n xi := hinterchange.symm
    _ = ∑' n : ℕ,
        LSeries.term a (sigma : ℂ) n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
      apply tsum_congr
      intro n
      simpa only [s0] using hterm n

end

end Erdos67.MRHalaszBands

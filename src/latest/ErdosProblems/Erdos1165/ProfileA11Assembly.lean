/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianProfileReindex

/-!
# Quantitative assembly of HLOZ (A.11)

This file combines the two global estimates proved in `ProfileTaylor`:

* the accumulated local-CLT/Stirling error, and
* the summation-by-parts comparison of the parabolic energy with the
  centered Gaussian energy.

The result is the pathwise logarithmic inequality used in HLOZ (A.11).  In
particular, it keeps the genuine deterministic cost `2 * (n - 2)` separate
from the sublinear `n^(3*delta)` remainder.  This is essential: the raw
negative-binomial constrained-profile weight has leading factor `exp (-2n)`;
only the centered Gaussian constrained sum has a purely sublinear exponent.
-/

open scoped BigOperators

namespace Erdos1165.ProfileA11Assembly

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor

/-- Sum of the logarithms of the HLOZ Gaussian normalizers. -/
def gaussianNormalizerLogSum (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico 2 n,
    Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2

/-- The full explicit coefficient multiplying `n^(3*delta)` in the checked
pathwise form of HLOZ (A.11). -/
def a11ErrorCoefficient (delta A B C : ℝ) : ℝ :=
  parabolicTaylorCoefficient A C / (3 * delta) +
    (3 + 4 * B + C / 2) / delta

lemma a11ErrorCoefficient_nonneg {delta A B C : ℝ}
    (hdelta : 0 < delta) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ a11ErrorCoefficient delta A B C := by
  unfold a11ErrorCoefficient parabolicTaylorCoefficient
  positivity

/-- **Checked pathwise HLOZ (A.11), logarithmic form.**

After adding the Gaussian normalizer and centered Gaussian energy, the sum
of the exact Stirling lower exponents is bounded below by the deterministic
parabolic cost `-2*(n-2)` and one explicit `n^(3*delta)` error.  The large
linear increment term is already telescoped inside
`abs_parabolicEnergy_sub_reference_le`; no edgewise absolute-value loss is
present here. -/
theorem sum_edgeStirlingExponent_add_gaussian_ge
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ → ℕ) (Delta : ℕ → ℝ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico 2 n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico 2 n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico 2 n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico 2 n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico 2 n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico 2 n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + Delta l)
    (hDelta : ∀ l ∈ Finset.Icc 2 n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico 2 n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    -(2 * (n - 2 : ℕ) : ℝ) - gaussianEnergy n Delta -
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) ≤
      (∑ l ∈ Finset.Ico 2 n,
        edgeStirlingExponent (m l) (m (l + 1))) +
        gaussianNormalizerLogSum n := by
  have htaylor := abs_sum_edgeStirlingExponent_parabolic_le n hn m hdelta
    hdeltaThird hA hC hpos hwindow hbase hclose hmoderate hinc
  have henergy := abs_parabolicEnergy_sub_reference_le n hn Delta hdelta
    hdeltaThird hB hC hDelta hDeltaInc
  have htaylorLower := neg_le_of_abs_le htaylor
  have henergyUpper := le_of_abs_le henergy
  have href := parabolicReferenceEnergy_eq n hn Delta
  have hparaEnergy :
      parabolicEnergy n Delta =
        ∑ l ∈ Finset.Ico 2 n,
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2) := by
    unfold parabolicEnergy parabolicTransitionIncrement
    apply Finset.sum_congr rfl
    intro l hl
    rw [hparabolic (l + 1), hparabolic l]
  rw [hparaEnergy] at henergyUpper
  rw [href] at henergyUpper
  unfold gaussianNormalizerLogSum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at htaylorLower
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have herr :
      a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) =
        parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
            (3 * delta) +
          (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
    unfold a11ErrorCoefficient
    ring
  rw [hcast, herr]
  linarith

/-- Exponentiated form of the pathwise A.11 estimate. -/
theorem exp_a11Error_mul_gaussianLogWeight_le
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ → ℕ) (Delta : ℕ → ℝ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico 2 n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico 2 n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico 2 n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico 2 n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico 2 n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico 2 n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + Delta l)
    (hDelta : ∀ l ∈ Finset.Icc 2 n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico 2 n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    Real.exp
        (-(2 * (n - 2 : ℕ) : ℝ) -
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
          gaussianEnergy n Delta - gaussianNormalizerLogSum n) ≤
      Real.exp
        (∑ l ∈ Finset.Ico 2 n,
          edgeStirlingExponent (m l) (m (l + 1))) := by
  apply Real.exp_le_exp.mpr
  have h := sum_edgeStirlingExponent_add_gaussian_ge n hn m Delta hdelta
    hdeltaThird hA hB hC hpos hwindow hbase hclose hmoderate hinc
    hparabolic hDelta hDeltaInc
  linarith

end

end Erdos1165.ProfileA11Assembly

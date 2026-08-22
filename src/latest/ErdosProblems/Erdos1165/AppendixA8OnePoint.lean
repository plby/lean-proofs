/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianProfileReindex

/-!
# Quantitative Appendix-A.8 constrained-profile lower bound

This dependency-light module packages the complete checked output of the
Gaussian lattice small-ball and finite profile-reindexing calculations.  It
does not import the Proposition 1.3 assembly, so that its results can be used
there without an import cycle.
-/

open scoped BigOperators

namespace Erdos1165.AppendixA8OnePoint

noncomputable section

open AppendixFirstMoment AppendixSmallBallAssembly GaussianProfileReindex

/-- The explicit finite error appearing in the checked A.8 bound: the first
term is the exact late-block-to-full-profile cost and the second is the exact
fixed-Gaussian-to-certified-Taylor cost. -/
def quantitativeA8FiniteError {start steps R : ℕ} (hstart : 2 ≤ start) : ℝ :=
  finiteGaussianPathToFullProfileError
      (start := start) (steps := steps) (R := R) hstart +
    blockErrorSum (finiteGaussianToCertifiedError R) start steps

lemma quantitativeA8FiniteError_nonneg {start steps R : ℕ}
    (hstart : 2 ≤ start) :
    0 ≤ quantitativeA8FiniteError (steps := steps) (R := R) hstart := by
  have hblock' : ∀ (s k : ℕ),
      0 ≤ blockErrorSum (finiteGaussianToCertifiedError R) s k := by
    intro s k
    induction k generalizing s with
    | zero => simp
    | succ k ih =>
        rw [blockErrorSum_succ]
        exact add_nonneg (finiteGaussianToCertifiedError_nonneg R s) (ih (s + 1))
  have hblock := hblock' start steps
  exact add_nonneg (finiteGaussianPathToFullProfileError_nonneg hstart) hblock

/-- Explicit positive A.8 lower bound: exact finite Taylor/reindexing error
plus the spectral strip-survival cost `1280 * steps * n^2 / R^2`. -/
def quantitativeA8OnePoint {start steps n R : ℕ} (hstart : 2 ≤ start) : ℝ :=
  Real.exp
    (-(quantitativeA8FiniteError (steps := steps) (R := R) hstart +
      1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2))

lemma quantitativeA8OnePoint_pos {start steps n R : ℕ}
    (hstart : 2 ≤ start) :
    0 < quantitativeA8OnePoint (steps := steps) (n := n) (R := R) hstart :=
  Real.exp_pos _

lemma quantitativeA8OnePoint_nonneg {start steps n R : ℕ}
    (hstart : 2 ≤ start) :
    0 ≤ quantitativeA8OnePoint (steps := steps) (n := n) (R := R) hstart :=
  (quantitativeA8OnePoint_pos (steps := steps) (n := n) (R := R) hstart).le

/-- **Checked quantitative constrained-profile lower bound (HLOZ A.8).**

There is no local-Gaussian, random-variance, prefix, or path-reindexing
hypothesis in this theorem. -/
theorem quantitativeA8OnePoint_le_constrainedTaylorGaussianWeight
    {start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {delta : ℝ}
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    quantitativeA8OnePoint (steps := steps) (n := n) (R := R) hstart ≤
      constrainedTaylorGaussianWeight (start + steps) delta := by
  simpa only [quantitativeA8OnePoint, quantitativeA8FiniteError, add_assoc] using
    exp_completeProfileError_le_constrainedTaylorGaussianWeight
      hstart hbound hscale hcenter hwidth

/-- The same explicit A.8 bound for the exact negative-binomial constrained
profile weight. -/
theorem quantitativeA8OnePoint_le_constrainedProfileWeight
    {start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {delta : ℝ} (hdelta : delta ≤ 1)
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    quantitativeA8OnePoint (steps := steps) (n := n) (R := R) hstart ≤
      constrainedProfileWeight (start + steps) delta := by
  simpa only [quantitativeA8OnePoint, quantitativeA8FiniteError, add_assoc] using
    exp_completeProfileError_le_constrainedProfileWeight
      hstart hbound hscale hdelta hcenter hwidth

end

end Erdos1165.AppendixA8OnePoint

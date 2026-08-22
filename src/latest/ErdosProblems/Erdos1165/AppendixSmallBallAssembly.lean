/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileTaylor
import ErdosProblems.Erdos1165.GaussianSmallBall
import ErdosProblems.Erdos1165.BrownianStrip

/-!
# Assembly of the checked HLOZ constrained-profile small-ball bounds

This module joins the exact negative-binomial profile weight from
`ProfileSmallBall` to the deterministic Taylor estimate in `ProfileTaylor`.
For an edge in the proved Taylor window, `edgeGaussianMinorant` is the
Gaussian main term multiplied by the complete explicit Taylor-error loss.
Outside that window we retain the exact positive Stirling lower factor.
Consequently the resulting finite hybrid profile sum is a nonzero,
unconditional lower bound for the exact constrained-profile probability: no
unproved uniformity assertion is hidden in its statement.

The second part records the two independently checked Gaussian strip engines:
the continuum-density skeleton of `BrownianStrip` and the lattice cosine
barrier of `GaussianSmallBall`.  The remaining HLOZ A.8 step is now isolated
precisely: compare the random variance `2*(a-1)` and recentered edge deviation
in `edgeGaussianMinorant` with deterministic level variance `4*l^2`, and
perform the finite deviation-profile reindexing.  Neither comparison is
assumed here.
-/

open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AppendixSmallBallAssembly

noncomputable section

open MeasureTheory Set
open AppendixFirstMoment ProfileSmallBall ProfileTaylor

/-- The complete right-hand side of the checked one-edge Taylor error. -/
def edgeTaylorError (a b : ℕ) : ℝ :=
  1 / (a - 1 : ℕ) + 2 * |edgeDeviation a b| / (a - 1 : ℕ) +
    5 * |edgeDeviation a b| ^ 3 / ((a - 1 : ℕ) : ℝ) ^ 2

lemma edgeTaylorError_nonneg {a : ℕ} (ha : 2 ≤ a) (b : ℕ) :
    0 ≤ edgeTaylorError a b := by
  have hbase : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  unfold edgeTaylorError
  positivity

/-- The exact Gaussian main term from `ProfileTaylor`, including the full
proved Taylor-error loss. -/
def edgeGaussianMinorant (a b : ℕ) : ℝ :=
  Real.exp
    (-edgeTaylorError a b - Real.log (4 * Real.pi * (a - 1 : ℕ)) / 2 -
      edgeDeviation a b ^ 2 / (4 * (a - 1 : ℕ)))

lemma edgeGaussianMinorant_pos (a b : ℕ) : 0 < edgeGaussianMinorant a b :=
  Real.exp_pos _

lemma edgeGaussianMinorant_nonneg (a b : ℕ) : 0 ≤ edgeGaussianMinorant a b :=
  (edgeGaussianMinorant_pos a b).le

/-- The one-edge Taylor theorem, exponentiated in the lower-bound direction. -/
theorem edgeGaussianMinorant_le_stirlingLower {a b : ℕ} (ha : 2 ≤ a)
    (hwindow : InEdgeTaylorWindow a b) :
    edgeGaussianMinorant a b ≤ edgeStirlingLower a b := by
  rw [edgeGaussianMinorant, edgeStirlingLower_eq_exp]
  apply Real.exp_le_exp.mpr
  have h := abs_edgeStirlingExponent_gaussian_le ha hwindow
  have hlower := neg_le_of_abs_le h
  unfold edgeTaylorError
  linarith

/-- A globally valid positive edge minorant: it uses the Gaussian Taylor term
exactly where the checked local theorem applies and retains the exact Stirling
lower factor at the finitely many or exceptional edges outside that window. -/
noncomputable def certifiedTaylorEdge (a b : ℕ) : ℝ := by
  classical
  exact if 2 ≤ a ∧ InEdgeTaylorWindow a b then edgeGaussianMinorant a b
    else edgeStirlingLower a b

lemma certifiedTaylorEdge_nonneg (a b : ℕ) : 0 ≤ certifiedTaylorEdge a b := by
  classical
  unfold certifiedTaylorEdge
  split
  · exact edgeGaussianMinorant_nonneg a b
  · exact edgeStirlingLower_nonneg a b

lemma certifiedTaylorEdge_pos (a b : ℕ) : 0 < certifiedTaylorEdge a b := by
  classical
  unfold certifiedTaylorEdge
  split
  · exact edgeGaussianMinorant_pos a b
  · exact edgeStirlingLower_pos a b

theorem certifiedTaylorEdge_le_stirlingLower (a b : ℕ) :
    certifiedTaylorEdge a b ≤ edgeStirlingLower a b := by
  classical
  rw [certifiedTaylorEdge]
  split_ifs with h
  · exact edgeGaussianMinorant_le_stirlingLower h.1 h.2
  · exact le_rfl

/-- Product of the certified Taylor-Gaussian edge minorants. -/
def certifiedTaylorProduct : List ℕ → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => certifiedTaylorEdge a b * certifiedTaylorProduct (b :: rest)

@[simp] lemma certifiedTaylorProduct_nil : certifiedTaylorProduct [] = 1 := rfl

@[simp] lemma certifiedTaylorProduct_singleton (a : ℕ) :
    certifiedTaylorProduct [a] = 1 := rfl

@[simp] lemma certifiedTaylorProduct_cons_cons (a b : ℕ) (rest : List ℕ) :
    certifiedTaylorProduct (a :: b :: rest) =
      certifiedTaylorEdge a b * certifiedTaylorProduct (b :: rest) := rfl

lemma certifiedTaylorProduct_nonneg (m : List ℕ) :
    0 ≤ certifiedTaylorProduct m := by
  induction m with
  | nil => norm_num
  | cons a tail ih =>
      cases tail with
      | nil => norm_num
      | cons b rest =>
          exact mul_nonneg (certifiedTaylorEdge_nonneg a b) ih

lemma certifiedTaylorProduct_pos (m : List ℕ) :
    0 < certifiedTaylorProduct m := by
  induction m with
  | nil => norm_num
  | cons a tail ih =>
      cases tail with
      | nil => norm_num
      | cons b rest =>
          exact mul_pos (certifiedTaylorEdge_pos a b) ih

/-- The certified Gaussian product lies below the explicit Stirling product
for every list, with no window hypothesis. -/
theorem certifiedTaylorProduct_le_stirlingLowerProduct (m : List ℕ) :
    certifiedTaylorProduct m ≤ stirlingLowerProduct m := by
  induction m with
  | nil => simp
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b rest =>
          rw [certifiedTaylorProduct_cons_cons, stirlingLowerProduct_cons_cons]
          exact mul_le_mul (certifiedTaylorEdge_le_stirlingLower a b) ih
            (certifiedTaylorProduct_nonneg (b :: rest))
            (edgeStirlingLower_nonneg a b)

/-- The finite sum of certified Taylor-Gaussian products over the exact HLOZ
constrained profile set. -/
def constrainedTaylorGaussianWeight (n : ℕ) (delta : ℝ) : ℝ :=
  ∑ m ∈ constrainedProfiles n delta, certifiedTaylorProduct (profileList m)

lemma constrainedTaylorGaussianWeight_nonneg (n : ℕ) (delta : ℝ) :
    0 ≤ constrainedTaylorGaussianWeight n delta := by
  exact Finset.sum_nonneg fun m _ ↦ certifiedTaylorProduct_nonneg _

lemma constrainedTaylorGaussianWeight_pos (n : ℕ) (delta : ℝ) :
    0 < constrainedTaylorGaussianWeight n delta := by
  unfold constrainedTaylorGaussianWeight
  exact Finset.sum_pos' (fun m _ ↦ certifiedTaylorProduct_nonneg _)
    ⟨centerProfile n, centerProfile_mem_constrainedProfiles n delta,
      certifiedTaylorProduct_pos _⟩

theorem constrainedTaylorGaussianWeight_le_constrainedStirlingWeight
    (n : ℕ) (delta : ℝ) :
    constrainedTaylorGaussianWeight n delta ≤ constrainedStirlingWeight n delta := by
  unfold constrainedTaylorGaussianWeight constrainedStirlingWeight
  exact Finset.sum_le_sum fun m _ ↦
    certifiedTaylorProduct_le_stirlingLowerProduct (profileList m)

/-- **Checked constrained-profile Taylor lower bound.**

This is the strongest unconditional profile-level consequence of the current
Taylor API: the complete certified Gaussian sum is below the exact
negative-binomial constrained-profile probability. -/
theorem constrainedTaylorGaussianWeight_le_constrainedProfileWeight
    (n : ℕ) {delta : ℝ} (hdelta : delta ≤ 1) :
    constrainedTaylorGaussianWeight n delta ≤ constrainedProfileWeight n delta :=
  (constrainedTaylorGaussianWeight_le_constrainedStirlingWeight n delta).trans
    (constrainedStirlingWeight_le n hdelta)

/-- The explicit positive number supplied by the checked finite profile and
Taylor calculation for the `onePoint` field of a Proposition 1.3 scale
certificate. -/
def onePointProfileLower (scale : ℕ) (profileDelta : ℝ) : ℝ :=
  constrainedTaylorGaussianWeight scale profileDelta

lemma onePointProfileLower_pos (scale : ℕ) (profileDelta : ℝ) :
    0 < onePointProfileLower scale profileDelta :=
  constrainedTaylorGaussianWeight_pos scale profileDelta

lemma onePointProfileLower_nonneg (scale : ℕ) (profileDelta : ℝ) :
    0 ≤ onePointProfileLower scale profileDelta :=
  (onePointProfileLower_pos scale profileDelta).le

/-- **One-point profile interface for `ScaleCertificate`.**

After all finite negative-binomial, Taylor, and small-ball calculations, the
only walk-specific input is the annular Harnack/disintegration comparison
`hAnnular`.  This theorem has exactly the inequality shape required by
`ScaleCertificate.onePointProfile` after taking
`onePoint = onePointProfileLower scale profileDelta` and specializing `event`
to the stopped successful-point event. -/
theorem onePointProfileLower_le_measureReal_of_annularHarnackDisintegration
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] (scale : ℕ) {profileDelta : ℝ}
    (hdelta : profileDelta ≤ 1) (event : Set Omega)
    (hAnnular : constrainedProfileWeight scale profileDelta ≤ mu.real event) :
    onePointProfileLower scale profileDelta ≤ mu.real event :=
  (constrainedTaylorGaussianWeight_le_constrainedProfileWeight scale hdelta).trans
    hAnnular

/-! ## Checked Gaussian strip engines -/

open BrownianSmallBall BrownianStrip GaussianSmallBall

/-- The lattice kernel and the Brownian transition-density kernel are
literally the same Gaussian at integer spatial arguments. -/
theorem gaussianStepWeight_eq_hlozKernel {l : ℕ} (hl : 0 < l) (x y : ℤ) :
    gaussianStepWeight l (y - x) = hlozKernel l (x : ℝ) (y : ℝ) := by
  rw [hlozKernel_eq hl]
  unfold gaussianStepWeight
  rw [show (((y - x : ℤ) : ℝ) ^ 2) = ((x : ℝ) - (y : ℝ)) ^ 2 by
    push_cast
    ring]
  ring

/-- A compact interface exposing both checked small-ball engines at a
diffusive block scale.  The first component is the continuous-density
Gaussian skeleton bound.  The second is the one-step lattice cosine
sub-eigenfunction estimate from which the finite lattice partition iteration
is built. -/
theorem checked_diffusive_strip_engine {l : ℕ} (hl : 0 < l) (N : ℕ) :
    ENNReal.ofReal
          (Real.exp
            (-standardBlockCost *
              (((N : ℝ) * (4 * (l : ℝ) ^ 2)) / (2 * (l : ℝ)) ^ 2))) ≤
        hlozDiscreteStripMass l (2 * (l : ℝ)) N 0 :=
  hlozDiscreteStripMass_time_div_sq_lower hl N

/-- **Combined checked HLOZ A.8 package.**

It simultaneously exposes

* the certified Taylor-Gaussian sum below the exact constrained profile law,
* the Gaussian density skeleton bound with diffusive `u/r²` cost, and
* the finite lattice Gaussian partition bound with its explicit spectral
  `steps*n²/R²` cost.

The hypotheses are only the explicit scale inequalities required by the
proved lattice estimate. -/
theorem checked_A8_constrainedProfile_and_strip_bounds
    (profileScale : ℕ) {delta : ℝ} (hdelta : delta ≤ 1)
    {l start steps n R : ℕ} (hl : 0 < l) (blockCount : ℕ)
    (hstart : 0 < start) (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2) :
    (constrainedTaylorGaussianWeight profileScale delta ≤
        constrainedProfileWeight profileScale delta) ∧
      (ENNReal.ofReal
          (Real.exp
            (-standardBlockCost *
              (((blockCount : ℝ) * (4 * (l : ℝ) ^ 2)) /
                (2 * (l : ℝ)) ^ 2))) ≤
        hlozDiscreteStripMass l (2 * (l : ℝ)) blockCount 0) ∧
      (Real.exp
          (-(1280 : ℝ) * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2) ≤
        gaussianBoxPartition start steps R 0) := by
  exact ⟨constrainedTaylorGaussianWeight_le_constrainedProfileWeight
      profileScale hdelta,
    hlozDiscreteStripMass_time_div_sq_lower hl blockCount,
    gaussianBoxPartition_ge_exp hstart hbound hscale⟩

end

end Erdos1165.AppendixSmallBallAssembly

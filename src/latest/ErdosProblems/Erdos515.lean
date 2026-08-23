/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 515.
https://www.erdosproblems.com/forum/thread/515

Informal authors:
- John Lewis
- John Rossi
- Allen Weitsman

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos515.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.PrawitzStageConcrete
import ErdosProblems.Erdos515.TopologyStage

/-!
# Erdős Problem 515

The integral below is the nonnegative arclength integral along the polygonal trace represented by
`LocallyRectifiablePath`; see `ErdosProblems.Erdos515.Path`.  Thus the conclusion is the literal
one-path-for-all-positive-exponents statement, with no cancellation from a complex line integral.
-/

namespace Erdos515

/-- The exact conclusion of Erdős Problem 515 for a complex-valued function. -/
def HasFiniteInversePowerPath (f : ℂ → ℂ) : Prop :=
  ∃ C : LocallyRectifiablePath,
    ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ⊤

/-- Bundled output of the analytic Hall--Prawitz and boundary-access arguments. -/
structure Erdos515AnalyticData (f : ℂ → ℂ) where
  base : ℂ
  shortPath : LRWShortPathPrinciple (logPosNorm f) base
  initial : LRWAdmissiblePoint shortPath.delta (logPosNorm f) base
  boundary : LRWBoundaryControl shortPath initial

/-- Once the genuine analytic data have been constructed, the finite-block recursion and LRW
summability engine give the exact conclusion. -/
theorem hasFiniteInversePowerPath_of_analyticData {f : ℂ → ℂ}
    (hf : Continuous f) (A : Erdos515AnalyticData f) :
    HasFiniteInversePowerPath f := by
  obtain ⟨C, _hvertex, hC⟩ := A.boundary.exists_path A.shortPath A.initial hf
  exact ⟨C, hC⟩

/-- The exact final assembly after the Hall--Prawitz short-path principle has been established.
The initial admissible state and the boundary-scale certificate are constructed here, so the
only remaining analytic input is the uniform short-path principle itself. -/
theorem hasFiniteInversePowerPath_of_shortPath
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (a : PositiveControlPoint (logPosNorm f))
    (S : LRWShortPathPrinciple (logPosNorm f) a.point) :
    HasFiniteInversePowerPath f := by
  let initial := S.initialAdmissible a
  let B := Classical.choice
    (LRWBoundaryControl.exists_boundaryControl_logPosNorm hf htrans S initial rfl)
  obtain ⟨C, _hvertex, hC⟩ := B.exists_path S initial hf.continuous
  exact ⟨C, hC⟩

/-- Final assembly directly from the uniform Hall--Prawitz radial statement. -/
theorem hasFiniteInversePowerPath_of_radialShortPath
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (a : PositiveControlPoint (logPosNorm f))
    (R : LRWRadialShortPathPrinciple (logPosNorm f) a.point) :
    HasFiniteInversePowerPath f := by
  exact hasFiniteInversePowerPath_of_shortPath hf htrans a
    (R.toShortPathPrinciple (continuous_logPosNorm hf.continuous))

/-- Final assembly after reducing the analytic heart of the argument to the planar
simple-connectivity and Hall--Prawitz stage estimates recorded in
`LRWLogPosShortPathInputs`. -/
theorem hasFiniteInversePowerPath_of_logPosShortPathInputs
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (a : PositiveControlPoint (logPosNorm f))
    (A : LRWLogPosShortPathInputs f a.point) :
    HasFiniteInversePowerPath f := by
  let R := Classical.choice (A.toRadialShortPathPrinciple hf htrans)
  exact hasFiniteInversePowerPath_of_radialShortPath hf htrans a R

/-- Final assembly from the separated Hall theorem, Prawitz/log-area theorem, and the planar
simple-connectivity theorem for sublevel components. -/
theorem hasFiniteInversePowerPath_of_stageTheorems
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (a : PositiveControlPoint (logPosNorm f))
    (A : LRWStageTheorems f a.point)
    (hsimplyConnected : ∀ b : LRWAdmissiblePoint A.delta (logPosNorm f) a.point,
      IsSimplyConnected (lrwDomain A.delta (logPosNorm f) a.point b.controlPoint)) :
    HasFiniteInversePowerPath f := by
  exact hasFiniteInversePowerPath_of_logPosShortPathInputs hf htrans a
    (A.toLogPosShortPathInputs hsimplyConnected)

/-- The final assembly interface with the initial positive point chosen internally.

This is the exact plug-in theorem for the three uniform ingredients left after the recursive,
boundary-access, Riemann-map, and normalization arguments: Hall's radial estimate, the
Prawitz/log-area stage estimate, and simple connectivity of the LRW sublevel components. -/
theorem hasFiniteInversePowerPath_of_hall_prawitz_topology
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hHall : ∀ (w : ℂ → ℝ) (delta : ℝ),
      SubharmonicOn w unitDisk →
      (∀ z ∈ unitDisk, 0 ≤ w z) →
      (∀ z ∈ unitDisk, w z ≤ 1) →
      w 0 = 1 - delta → 0 ≤ delta → delta ≤ 1 / 512 →
      ENNReal.ofReal Real.pi ≤ MeasureTheory.volume (goodDirections w))
    (hPrawitz : ∀ (base : ℂ)
      (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
      (F : ℂ → ℂ),
      DifferentiableOn ℂ F (Metric.ball 0 1) →
      Set.BijOn F (Metric.ball 0 1)
        (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta
        constant a F))
    (hsimplyConnected : ∀ (base : ℂ)
      (b : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base),
      IsSimplyConnected
        (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint)) :
    HasFiniteInversePowerPath f := by
  let a := Classical.choice (exists_positiveControlPoint_logPosNorm hf htrans)
  let A : LRWStageTheorems f a.point :=
    LRWStageTheorems.ofHallAndPrawitz hf constant hconstant hHall (hPrawitz a.point)
  exact hasFiniteInversePowerPath_of_stageTheorems hf htrans a A
    (fun b ↦ hsimplyConnected a.point b)

/-- Final assembly after applying the now-unconditional Hall radial theorem.  The only remaining
plug-ins are the Prawitz/log-area stage theorem and planar simple connectivity. -/
theorem hasFiniteInversePowerPath_of_prawitz_topology
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hPrawitz : ∀ (base : ℂ)
      (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
      (F : ℂ → ℂ),
      DifferentiableOn ℂ F (Metric.ball 0 1) →
      Set.BijOn F (Metric.ball 0 1)
        (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta
        constant a F))
    (hsimplyConnected : ∀ (base : ℂ)
      (b : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base),
      IsSimplyConnected
        (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint)) :
    HasFiniteInversePowerPath f :=
  hasFiniteInversePowerPath_of_hall_prawitz_topology hf htrans constant hconstant
    hall_radial_unconditional hPrawitz hsimplyConnected

/-- Final assembly with both Hall's theorem and planar simple connectivity discharged.  At this
point the only analytic ingredient is the Prawitz/log-area exceptional-set estimate for a
normalized Riemann map at each LRW stage. -/
theorem hasFiniteInversePowerPath_of_prawitz
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f)
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hPrawitz : ∀ (base : ℂ)
      (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
      (F : ℂ → ℂ),
      DifferentiableOn ℂ F (Metric.ball 0 1) →
      Set.BijOn F (Metric.ball 0 1)
        (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta
        constant a F)) :
    HasFiniteInversePowerPath f :=
  hasFiniteInversePowerPath_of_prawitz_topology hf htrans constant hconstant hPrawitz
    (isSimplyConnected_lrwDomain_logPosNorm hf)

/-- The affirmative resolution of Erdős Problem 515: every transcendental entire function
admits one locally rectifiable path tending to infinity on which every positive inverse power
has finite arclength integral. -/
theorem erdos_515 {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f) :
    ∃ C : LocallyRectifiablePath,
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ⊤ := by
  change HasFiniteInversePowerPath f
  exact hasFiniteInversePowerPath_of_prawitz hf htrans
    PrawitzStageConcrete.prawitzStageConstant
    PrawitzStageConcrete.prawitzStageConstant_nonneg
    PrawitzStageConcrete.prawitzStageData

#print axioms erdos_515

end Erdos515

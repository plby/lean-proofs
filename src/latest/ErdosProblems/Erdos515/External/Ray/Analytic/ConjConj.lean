module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.CauchyIntegral
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Multilinear

/-!
## Conjugating an analytic function with complex `conj` preserves analyticity
-/

open Classical
open Function (uncurry)
open MeasureTheory
open Metric (ball closedBall)
open Set
open scoped NNReal Real ENNReal ComplexConjugate
noncomputable section

variable {f : ℂ → ℂ} {z : ℂ} {n : ℕ} {r : ℝ≥0∞}
variable {p : FormalMultilinearSeries ℂ ℂ ℂ}

/-- Conjugate a power series -/
def FormalMultilinearSeries.conj_conj (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n ↦ (p n).conj_conj

/-- Conjugating power series conjugates the coefficients -/
@[simp] lemma FormalMultilinearSeries.coeff_conj_conj : p.conj_conj.coeff n = conj (p.coeff n) := by
  simp only [coeff, conj_conj, ContinuousMultilinearMap.conj_conj_apply, Pi.one_def, map_one]

/-- `conj_conj` preserves radius of convergence -/
@[simp] lemma FormalMultilinearSeries.radius_conj_conj (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    radius (p.conj_conj) = radius p := by simp [radius]

/-- Conjugation respects power series, ball version  -/
lemma HasFPowerSeriesOnBall.conj_conj (fa : HasFPowerSeriesOnBall f p (conj z) r) :
    HasFPowerSeriesOnBall (fun z ↦ conj (f (conj z))) p.conj_conj z r where
  r_le := by simp [fa.r_le]
  r_pos := fa.r_pos
  hasSum := by
    intro y m
    simp only [Metric.mem_eball, edist_zero_right] at m
    simpa only [FormalMultilinearSeries.conj_conj, ContinuousMultilinearMap.conj_conj_apply, map_add,
      conjCLM_apply] using conjCLM.hasSum (@fa.hasSum (conj y) (by simpa))

/-- Conjugation respects power series, point version  -/
lemma HasFPowerSeriesAt.conj_conj (fa : HasFPowerSeriesAt f p (conj z)) :
    HasFPowerSeriesAt (fun z ↦ conj (f (conj z))) p.conj_conj z := by
  obtain ⟨r, h⟩ := fa
  exact ⟨r, h.conj_conj⟩

/-- Conjugation respects analyticity -/
public lemma AnalyticAt.conj_conj (fa : AnalyticAt ℂ f (conj z)) :
    AnalyticAt ℂ (fun z ↦ conj (f (conj z))) z := by
  obtain ⟨p, h⟩ := fa
  exact ⟨_, h.conj_conj⟩

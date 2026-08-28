import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarTwoBasic

/-!
# Exact stabilization of top-degree primitives on double-annulus regions

Actual finite sums of scalar Cauchy--Green corrections adjust the
double-annulus primitives by closed forms. Consecutive smooth pairs agree
exactly on the smaller actual compact region, while preserving the
literal top-degree derivative equation.
-/

noncomputable section

open Set Metric
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo

open PeriodTorusLineBundleClassification

def closedRegion (n : ℕ) : Set (ℂ × ℂ) := DoublePuncturedDbarOne.annularClosed (radius n)

theorem closedRegion_mono {m n : ℕ} (h : m ≤ n) : closedRegion m ⊆ closedRegion n :=
  DoublePuncturedDbarOne.annularClosed_mono (radius_pos m) (PuncturedDbarTwo.radius_mono h)

def correctionSum {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := ∑ k ∈ Finset.range n, correction hw k q

theorem correctionSum_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (correctionSum hw n) :=
  ContDiff.sum fun k _ => correction_smooth hw k

theorem correctionSum_succ {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    correctionSum hw (n + 1) = fun q => correctionSum hw n q + correction hw n q := by
  funext q
  exact Finset.sum_range_succ (fun k => correction hw k q) n

def firstStage {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := dbarFirst (correctionSum hw n) q - initial hw n q

def secondStage {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ℂ × ℂ → ℂ := dbarSecond (correctionSum hw n)

theorem firstStage_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (firstStage hw n) :=
  (contDiff_dbarFirst (correctionSum_smooth hw n)).sub (initial_smooth hw n)

theorem secondStage_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (secondStage hw n) :=
  contDiff_dbarSecond (correctionSum_smooth hw n)

theorem stage_equation {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedRegion n) :
    dbarFirst (secondStage hw n) q - dbarSecond (firstStage hw n) q = w q := by
  have hs := correctionSum_smooth hw n
  change dbarFirst (dbarSecond (correctionSum hw n)) q -
    dbarSecond (fun x => dbarFirst (correctionSum hw n) x - initial hw n x) q = w q
  rw [dbarSecond_sub ((contDiff_dbarFirst hs).differentiable (by simp) q)
    ((initial_smooth hw n).differentiable (by simp) q),
    ← dbarFirst_dbarSecond hs q, dbarSecond_initial hw n q (strip_mono (Nat.le_succ n) hq.1)
      (strip_mono (Nat.le_succ n) hq.2)]
  ring

theorem firstStage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedRegion n) :
    firstStage hw (n + 1) q = firstStage hw n q := by
  unfold firstStage
  rw [correctionSum_succ, dbarFirst_add
    ((correctionSum_smooth hw n).differentiable (by simp) q)
    ((correction_smooth hw n).differentiable (by simp) q),
    dbarFirst_correction hw n q hq.1, difference]
  ring

theorem secondStage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedRegion n) :
    secondStage hw (n + 1) q = secondStage hw n q := by
  unfold secondStage
  rw [correctionSum_succ, dbarSecond_add
    ((correctionSum_smooth hw n).differentiable (by simp) q)
    ((correction_smooth hw n).differentiable (by simp) q),
    dbarSecond_correction hw n q (strip_mono (Nat.le_succ n) hq.2), add_zero]

def stage {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ × ℂ := (firstStage hw n q, secondStage hw n q)

theorem stage_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (stage hw n) :=
  (firstStage_smooth hw n).prodMk (secondStage_smooth hw n)

theorem stage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedRegion n) :
    stage hw (n + 1) q = stage hw n q :=
  Prod.ext (firstStage_succ hw n q hq) (secondStage_succ hw n q hq)

theorem stage_compatible {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    {m n : ℕ} (hmn : m ≤ n) (q : ℂ × ℂ) (hq : q ∈ closedRegion m) :
    stage hw n q = stage hw m q := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ k hmk ih =>
      exact (stage_succ hw k q (closedRegion_mono hmk hq)).trans ih

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo

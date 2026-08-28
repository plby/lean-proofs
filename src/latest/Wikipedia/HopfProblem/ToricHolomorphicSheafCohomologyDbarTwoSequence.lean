import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarTwoBasic

/-!
# Exactly stabilizing top-degree primitives on the affine plane

Finite sums of the actual first-coordinate corrections adjust the strip
primitives by closed forms. The resulting smooth pairs have the prescribed
top-degree derivative, and successive pairs agree exactly on the smaller
closed bidisc. No limiting estimate or approximation premise is used.
-/

noncomputable section

open Set Metric
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo

open PeriodTorusLineBundleClassification

/-- The closed bidiscs used for exact stabilization. -/
def closedBidisc (n : ℕ) : Set (ℂ × ℂ) :=
  closedBall 0 (radius n) ×ˢ closedBall 0 (radius n)

theorem closedBidisc_mono {m n : ℕ} (h : m ≤ n) : closedBidisc m ⊆ closedBidisc n := by
  intro q hq
  exact ⟨closedBall_subset_closedBall (radius_mono h) hq.1,
    closedBall_subset_closedBall (radius_mono h) hq.2⟩

/-- A finite sum of the already constructed scalar correction functions. -/
def correctionSum (w : ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, correction w k q

theorem correctionSum_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (correctionSum w n) :=
  ContDiff.sum fun k _ => correction_smooth hw k

theorem correctionSum_succ (w : ℂ × ℂ → ℂ) (n : ℕ) :
    correctionSum w (n + 1) = fun q => correctionSum w n q + correction w n q := by
  funext q
  exact Finset.sum_range_succ (fun k => correction w k q) n

/-- The first coefficient of the adjusted actual smooth form. -/
def firstStage (w : ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ :=
  dbarFirst (correctionSum w n) q - initial w n q

/-- The second coefficient of the adjusted actual smooth form. -/
def secondStage (w : ℂ × ℂ → ℂ) (n : ℕ) : ℂ × ℂ → ℂ :=
  dbarSecond (correctionSum w n)

theorem firstStage_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (firstStage w n) :=
  (contDiff_dbarFirst (correctionSum_smooth hw n)).sub (initial_smooth hw n)

theorem secondStage_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (secondStage w n) :=
  contDiff_dbarSecond (correctionSum_smooth hw n)

/-- The actual top-degree equation on the nth horizontal strip. -/
theorem stage_equation {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ closedBall 0 (radius n)) :
    dbarFirst (secondStage w n) q - dbarSecond (firstStage w n) q = w q := by
  have hs := correctionSum_smooth hw n
  change dbarFirst (dbarSecond (correctionSum w n)) q -
    dbarSecond (fun x => dbarFirst (correctionSum w n) x - initial w n x) q = w q
  rw [dbarSecond_sub ((contDiff_dbarFirst hs).differentiable (by simp) q)
      ((initial_smooth hw n).differentiable (by simp) q),
    ← dbarFirst_dbarSecond hs q, dbarSecond_initial hw n q, cutoff_eq_one n hq]
  ring

theorem firstStage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedBidisc n) :
    firstStage w (n + 1) q = firstStage w n q := by
  unfold firstStage
  rw [correctionSum_succ, dbarFirst_add
    ((correctionSum_smooth hw n).differentiable (by simp) q)
    ((correction_smooth hw n).differentiable (by simp) q),
    dbarFirst_correction hw n q hq.1, difference]
  ring

theorem secondStage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedBidisc n) :
    secondStage w (n + 1) q = secondStage w n q := by
  unfold secondStage
  rw [correctionSum_succ, dbarSecond_add
    ((correctionSum_smooth hw n).differentiable (by simp) q)
    ((correction_smooth hw n).differentiable (by simp) q),
    dbarSecond_correction hw n q hq.2, add_zero]

/-- The actual adjusted smooth pair. -/
def stage (w : ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (firstStage w n q, secondStage w n q)

theorem stage_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (stage w n) :=
  (firstStage_smooth hw n).prodMk (secondStage_smooth hw n)

theorem stage_succ {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ closedBidisc n) :
    stage w (n + 1) q = stage w n q :=
  Prod.ext (firstStage_succ hw n q hq) (secondStage_succ hw n q hq)

/-- Exact compatibility of every later stage on each earlier closed bidisc. -/
theorem stage_compatible {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    {m n : ℕ} (hmn : m ≤ n) (q : ℂ × ℂ) (hq : q ∈ closedBidisc m) :
    stage w n q = stage w m q := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ k hmk ih =>
      exact (stage_succ hw k q (closedBidisc_mono hmk hq)).trans ih

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo

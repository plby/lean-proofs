import Arxiv.Arxiv2411_18291.NibbleVarianceBudget
import Arxiv.Arxiv2411_18291.SimultaneousCriticalWindows

/-! # Critical-window control for the actual nibble processes -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def nibbleCriticalControl (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)
    (N : ℕ) (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N)
    (hgap : ∀ t, nibbleStepBound q G D t < nibbleCriticalWidth G a D t)
    (hinit : ∀ t ω, nibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t) :
    CriticalWindowControl Filtration.piLE (probability (r + 1) H) (NibbleTrack V r) N where
  process := nibbleTrackedProcess G H a D
  good := nibbleGood G H a D
  lower := fun t => -nibbleCriticalWidth G a D t
  upper := fun _ => 0
  step := nibbleStepBound q G D
  variance := fun t => (N : ℝ) * nibbleVarianceRate q G D t
  step_pos := nibbleStepBound_pos hqr G P.graph_pos P.degree_pos
  variance_nonneg := fun t => mul_nonneg (Nat.cast_nonneg _)
    (nibbleVarianceRate_nonneg q G P.degree_pos.le t)
  gap := by intro t; have h := hgap t; linarith only [h]
  adapted := fun t i _ => nibbleTrackedProcess_stronglyMeasurable G H a D t i
  initial := fun t => ae_of_all _ (hinit t)
  bounded := by
    intro t i hi
    have hnext : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1) :=
      hfloor.trans (removalDensity_antitone _ P.graph_pos (by omega))
    apply ae_of_all
    intro ω
    simpa only [nibbleTrackedProcess_difference] using
      nibbleTrackedIncrement_abs_bound hqr G H P Q hd t i hnext ω
  measurable_good := fun i _ => nibbleGood_measurableSet G H a D i
  trend := by
    intro t i hi
    have hnext : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1) :=
      hfloor.trans (removalDensity_antitone _ P.graph_pos (by omega))
    simpa only [nibbleTrackedProcess_difference] using
      nibbleGood_tracked_trend G H P hqr hHG Q t i hnext
  variance_budget := by
    intro t j hj
    have h := (nibbleGood_variance_budget hqr G H hHG P Q hd t N hfloor).mono
      (fun _ h => h j hj)
    simpa only [nibbleTrackedProcess_difference] using h
  failure := fun j _ ω hbad => nibbleGood_failure G H a D j ω hbad

def nibbleFailureBound (q : ℕ) (G : Hypergraph V (r + 1)) (a D : ℝ) (N : ℕ) : ℝ :=
  ∑ t : NibbleTrack V r, (N : ℝ) * Real.exp
    (-((nibbleCriticalWidth G a D t - nibbleStepBound q G D t) ^ 2 /
      (2 * ((N : ℝ) * nibbleVarianceRate q G D t +
        (nibbleCriticalWidth G a D t - nibbleStepBound q G D t) * nibbleStepBound q G D t))))

theorem nibble_failure_probability_le (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)
    (N : ℕ) (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N)
    (hgap : ∀ t, nibbleStepBound q G D t < nibbleCriticalWidth G a D t)
    (hinit : ∀ t ω, nibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t) :
    (probability (r + 1) H).real {ω | ∃ j ≤ N, ω ∉ nibbleGood G H a D j} ≤
      nibbleFailureBound q G a D N := by
  have h := (nibbleCriticalControl hqr G H hHG P Q hd N hfloor hgap hinit).failure_probability_le
  simpa only [CriticalWindowControl.failureBound, nibbleCriticalControl,
    nibbleFailureBound, sub_neg_eq_add, zero_add] using h

end Arxiv2411_18291.CliqueRemovalProcess

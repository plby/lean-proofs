import Arxiv.Arxiv2411_18291.LogNibbleFaceTrend
import Arxiv.Arxiv2411_18291.NibbleTrackedProcess

/-! # One jointly tracked family for logarithmic count, edge, and face bounds -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def logNibbleTrackedProcess (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl b => if b then
      cliqueCountProcess (r + 1) H (logNibbleCliqueUpperComparison k a G.card D) i ω
    else -cliqueCountProcess (r + 1) H (logNibbleCliqueLowerComparison k a G.card D) i ω
  | .inr (.inl (e, b)) => if e ∈ G then if b then
      frozenEdgeProcess H e (logNibbleDegreeUpperComparison k a G.card D) i ω
    else -frozenEdgeProcess H e (logNibbleDegreeLowerComparison k a G.card D) i ω
    else -2 * (a ^ 2 * D)
  | .inr (.inr f) => faceCountProcess G f
      (logNibbleFaceUpperComparison k a G.card (Fintype.card V)
        (G.filter fun e => f.val ⊆ e.val).card) i ω

def logNibbleTrackedIncrement (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl b => if b then
      cliqueCountIncrement (r + 1) H (logNibbleCliqueUpperComparison k a G.card D) i ω
    else -cliqueCountIncrement (r + 1) H (logNibbleCliqueLowerComparison k a G.card D) i ω
  | .inr (.inl (e, b)) => if e ∈ G then if b then
      edgeIncrement H e (logNibbleDegreeUpperComparison k a G.card D) i ω
    else -edgeIncrement H e (logNibbleDegreeLowerComparison k a G.card D) i ω
    else 0
  | .inr (.inr f) => faceCountIncrement G f
      (logNibbleFaceUpperComparison k a G.card (Fintype.card V)
        (G.filter fun e => f.val ⊆ e.val).card) i ω

def logNibbleGood (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (i : ℕ) : Set (ℕ → State V q) := {ω | ∀ t, logNibbleTrackedProcess G H a D t i ω < 0}

theorem logNibbleTrackedProcess_edge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∈ G) :
    logNibbleTrackedProcess G H a D (.inr (.inl (e, b))) i = fun ω =>
      if b then frozenEdgeProcess H e
        (logNibbleDegreeUpperComparison (q.choose (r + 1)) a G.card D) i ω
      else -frozenEdgeProcess H e
        (logNibbleDegreeLowerComparison (q.choose (r + 1)) a G.card D) i ω := by
  funext ω
  simp only [logNibbleTrackedProcess, he, if_true]

theorem logNibbleTrackedProcess_nonedge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∉ G) :
    logNibbleTrackedProcess G H a D (.inr (.inl (e, b))) i = fun _ => -2 * (a ^ 2 * D) := by
  funext ω
  simp only [logNibbleTrackedProcess, he, if_false]

theorem logNibbleTrackedIncrement_edge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∈ G) :
    logNibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i = fun ω =>
      if b then edgeIncrement H e (logNibbleDegreeUpperComparison (q.choose (r + 1)) a G.card D) i ω
      else -edgeIncrement H e
        (logNibbleDegreeLowerComparison (q.choose (r + 1)) a G.card D) i ω := by
  funext ω
  simp only [logNibbleTrackedIncrement, he, if_true]

theorem logNibbleTrackedIncrement_nonedge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∉ G) :
    logNibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i = 0 := by
  funext ω
  simp only [logNibbleTrackedIncrement, he, if_false, Pi.zero_apply]

theorem logNibbleTrackedProcess_stronglyMeasurable (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) i]
      (logNibbleTrackedProcess G H a D t i) := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · exact (cliqueCountProcess_stronglyMeasurable H _ i).neg
    · exact cliqueCountProcess_stronglyMeasurable H _ i
  · by_cases he : e ∈ G
    · rw [logNibbleTrackedProcess_edge G H a D e b i he]
      cases b
      · exact (frozenEdgeProcess_stronglyMeasurable H e _ i).neg
      · exact frozenEdgeProcess_stronglyMeasurable H e _ i
    · rw [logNibbleTrackedProcess_nonedge G H a D e b i he]
      exact stronglyMeasurable_const
  · exact faceCountProcess_stronglyMeasurable G f _ i

theorem logNibbleTrackedIncrement_integrable (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) :
    Integrable (logNibbleTrackedIncrement G H a D t i) (probability (r + 1) H) := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · exact (cliqueCountIncrement_integrable H _ i).neg
    · exact cliqueCountIncrement_integrable H _ i
  · by_cases he : e ∈ G
    · rw [logNibbleTrackedIncrement_edge G H a D e b i he]
      cases b
      · exact (edgeIncrement_integrable H e _ i).neg
      · exact edgeIncrement_integrable H e _ i
    · rw [logNibbleTrackedIncrement_nonedge G H a D e b i he]
      exact integrable_zero _ _ _
  · exact faceCountIncrement_integrable G H f _ i

theorem logNibbleTrackedProcess_succ (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) :
    logNibbleTrackedProcess G H a D t (i + 1) ω =
      logNibbleTrackedProcess G H a D t i ω + logNibbleTrackedIncrement G H a D t i ω := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · simp only [logNibbleTrackedProcess, logNibbleTrackedIncrement, Bool.false_eq_true, if_false]
      rw [cliqueCountProcess_succ, neg_add]
    · exact cliqueCountProcess_succ H _ i ω
  · by_cases he : e ∈ G
    · simp only [logNibbleTrackedProcess, logNibbleTrackedIncrement, he, if_true]
      cases b
      · simp only [Bool.false_eq_true, if_false, frozenEdgeProcess_succ, neg_add]
      · exact frozenEdgeProcess_succ H e _ i ω
    · simp only [logNibbleTrackedProcess, logNibbleTrackedIncrement, he, if_false, add_zero]
  · exact faceCountProcess_succ G f _ i ω

theorem logNibbleGood_measurableSet (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (i : ℕ) : MeasurableSet[Filtration.piLE i] (logNibbleGood G H a D i) := by
  simp only [logNibbleGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  exact measurableSet_lt (logNibbleTrackedProcess_stronglyMeasurable G H a D t i).measurable
    measurable_const

theorem logNibbleGood_failure (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (i : ℕ) (ω : ℕ → State V q) (hbad : ω ∉ logNibbleGood G H a D i) :
    ∃ t, 0 ≤ logNibbleTrackedProcess G H a D t i ω := by
  change ¬∀ t, logNibbleTrackedProcess G H a D t i ω < 0 at hbad
  push Not at hbad
  exact hbad

end Arxiv2411_18291.CliqueRemovalProcess

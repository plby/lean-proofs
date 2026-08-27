import Arxiv.Arxiv2411_18291.NibbleCliqueCountTrend
import Arxiv.Arxiv2411_18291.NibbleEdgeTrend
import Arxiv.Arxiv2411_18291.NibbleFaceVariance

/-! # One finite family of count, frozen-edge, and face comparison processes -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

abbrev NibbleTrack (V : Type*) (r : ℕ) := Bool ⊕ ((Block V (r + 1) × Bool) ⊕ Block V r)

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def nibbleTrackedProcess (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl b => if b then
      cliqueCountProcess (r + 1) H (nibbleCliqueUpperComparison k a G.card D) i ω
    else -cliqueCountProcess (r + 1) H (nibbleCliqueLowerComparison k a G.card D) i ω
  | .inr (.inl (e, b)) => if e ∈ G then if b then
      frozenEdgeProcess H e (nibbleDegreeUpperComparison k a G.card D) i ω
    else -frozenEdgeProcess H e (nibbleDegreeLowerComparison k a G.card D) i ω
    else -2 * (a ^ 2 * D)
  | .inr (.inr f) => faceCountProcess G f
      (nibbleFaceUpperComparison k a G.card (Fintype.card V)
        (G.filter fun e => f.val ⊆ e.val).card) i ω

def nibbleTrackedIncrement (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl b => if b then
      cliqueCountIncrement (r + 1) H (nibbleCliqueUpperComparison k a G.card D) i ω
    else -cliqueCountIncrement (r + 1) H (nibbleCliqueLowerComparison k a G.card D) i ω
  | .inr (.inl (e, b)) => if e ∈ G then if b then
      edgeIncrement H e (nibbleDegreeUpperComparison k a G.card D) i ω
    else -edgeIncrement H e (nibbleDegreeLowerComparison k a G.card D) i ω
    else 0
  | .inr (.inr f) => faceCountIncrement G f
      (nibbleFaceUpperComparison k a G.card (Fintype.card V)
        (G.filter fun e => f.val ⊆ e.val).card) i ω

def nibbleGood (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) (a D : ℝ)
    (i : ℕ) : Set (ℕ → State V q) := {ω | ∀ t, nibbleTrackedProcess G H a D t i ω < 0}

theorem nibbleTrackedProcess_edge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∈ G) :
    nibbleTrackedProcess G H a D (.inr (.inl (e, b))) i = fun ω =>
      if b then frozenEdgeProcess H e
        (nibbleDegreeUpperComparison (q.choose (r + 1)) a G.card D) i ω
      else -frozenEdgeProcess H e
        (nibbleDegreeLowerComparison (q.choose (r + 1)) a G.card D) i ω := by
  funext ω
  simp only [nibbleTrackedProcess, he, if_true]

theorem nibbleTrackedProcess_nonedge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∉ G) :
    nibbleTrackedProcess G H a D (.inr (.inl (e, b))) i = fun _ => -2 * (a ^ 2 * D) := by
  funext ω
  simp only [nibbleTrackedProcess, he, if_false]

theorem nibbleTrackedIncrement_edge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∈ G) :
    nibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i = fun ω =>
      if b then edgeIncrement H e (nibbleDegreeUpperComparison (q.choose (r + 1)) a G.card D) i ω
      else -edgeIncrement H e (nibbleDegreeLowerComparison (q.choose (r + 1)) a G.card D) i ω := by
  funext ω
  simp only [nibbleTrackedIncrement, he, if_true]

theorem nibbleTrackedIncrement_nonedge (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (e : Block V (r + 1)) (b : Bool) (i : ℕ) (he : e ∉ G) :
    nibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i = 0 := by
  funext ω
  simp only [nibbleTrackedIncrement, he, if_false, Pi.zero_apply]

theorem nibbleTrackedProcess_stronglyMeasurable (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) i]
      (nibbleTrackedProcess G H a D t i) := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · exact (cliqueCountProcess_stronglyMeasurable H _ i).neg
    · exact cliqueCountProcess_stronglyMeasurable H _ i
  · by_cases he : e ∈ G
    · rw [nibbleTrackedProcess_edge G H a D e b i he]
      cases b
      · exact (frozenEdgeProcess_stronglyMeasurable H e _ i).neg
      · exact frozenEdgeProcess_stronglyMeasurable H e _ i
    · rw [nibbleTrackedProcess_nonedge G H a D e b i he]
      exact stronglyMeasurable_const
  · exact faceCountProcess_stronglyMeasurable G f _ i

theorem nibbleTrackedIncrement_integrable (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) :
    Integrable (nibbleTrackedIncrement G H a D t i) (probability (r + 1) H) := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · exact (cliqueCountIncrement_integrable H _ i).neg
    · exact cliqueCountIncrement_integrable H _ i
  · by_cases he : e ∈ G
    · rw [nibbleTrackedIncrement_edge G H a D e b i he]
      cases b
      · exact (edgeIncrement_integrable H e _ i).neg
      · exact edgeIncrement_integrable H e _ i
    · rw [nibbleTrackedIncrement_nonedge G H a D e b i he]
      exact integrable_zero _ _ _
  · exact faceCountIncrement_integrable G H f _ i

theorem nibbleTrackedProcess_succ (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) :
    nibbleTrackedProcess G H a D t (i + 1) ω =
      nibbleTrackedProcess G H a D t i ω + nibbleTrackedIncrement G H a D t i ω := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · simp only [nibbleTrackedProcess, nibbleTrackedIncrement, Bool.false_eq_true, if_false]
      rw [cliqueCountProcess_succ, neg_add]
    · exact cliqueCountProcess_succ H _ i ω
  · by_cases he : e ∈ G
    · simp only [nibbleTrackedProcess, nibbleTrackedIncrement, he, if_true]
      cases b
      · simp only [Bool.false_eq_true, if_false, frozenEdgeProcess_succ, neg_add]
      · exact frozenEdgeProcess_succ H e _ i ω
    · simp only [nibbleTrackedProcess, nibbleTrackedIncrement, he, if_false, add_zero]
  · exact faceCountProcess_succ G f _ i ω

theorem nibbleGood_measurableSet (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (i : ℕ) : MeasurableSet[Filtration.piLE i] (nibbleGood G H a D i) := by
  simp only [nibbleGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  exact measurableSet_lt (nibbleTrackedProcess_stronglyMeasurable G H a D t i).measurable
    measurable_const

theorem nibbleGood_failure (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (i : ℕ) (ω : ℕ → State V q) (hbad : ω ∉ nibbleGood G H a D i) :
    ∃ t, 0 ≤ nibbleTrackedProcess G H a D t i ω := by
  change ¬∀ t, nibbleTrackedProcess G H a D t i ω < 0 at hbad
  push Not at hbad
  exact hbad

end Arxiv2411_18291.CliqueRemovalProcess

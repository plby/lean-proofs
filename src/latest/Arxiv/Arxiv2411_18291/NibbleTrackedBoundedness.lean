import Arxiv.Arxiv2411_18291.NibbleControlScales

/-! # Global increment bounds for every nibble track -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibbleTrackedIncrement_stronglyMeasurable (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) (i + 1)]
      (nibbleTrackedIncrement G H a D t i) := by
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · exact (cliqueCountIncrement_stronglyMeasurable H _ i).neg
    · exact cliqueCountIncrement_stronglyMeasurable H _ i
  · by_cases heG : e ∈ G
    · rw [nibbleTrackedIncrement_edge G H a D e b i heG]
      cases b
      · exact (edgeIncrement_stronglyMeasurable H e _ i).neg
      · exact edgeIncrement_stronglyMeasurable H e _ i
    · rw [nibbleTrackedIncrement_nonedge G H a D e b i heG]
      exact stronglyMeasurable_zero
  · exact faceCountIncrement_stronglyMeasurable G f _ i

theorem nibbleTrackedIncrement_abs_bound (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)
    (t : NibbleTrack V r) (i : ℕ)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) (ω : ℕ → State V q) :
    |nibbleTrackedIncrement G H a D t i ω| ≤ nibbleStepBound q G D t := by
  let k := q.choose (r + 1)
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  have hD2 : 0 ≤ 2 * D := mul_nonneg (by norm_num) P.degree_pos.le
  have hcount := Q.sequence_steps P i hi
  rcases t with b | (⟨e, b⟩ | f)
  · cases b
    · change |-cliqueCountIncrement (r + 1) H (nibbleCliqueLowerComparison k a G.card D) i ω| ≤
        nibbleCountStepBound k D
      rw [abs_neg]
      exact (cliqueCountIncrement_abs_bound H (2 * D) hD2 hd _ i ω).trans
        (add_le_add le_rfl hcount.2.2.2)
    · change |cliqueCountIncrement (r + 1) H (nibbleCliqueUpperComparison k a G.card D) i ω| ≤
        nibbleCountStepBound k D
      exact (cliqueCountIncrement_abs_bound H (2 * D) hD2 hd _ i ω).trans
        (add_le_add le_rfl hcount.2.2.1)
  · by_cases heG : e ∈ G
    · rw [nibbleTrackedIncrement_edge G H a D e b i heG]
      cases b
      · change |-edgeIncrement H e (nibbleDegreeLowerComparison k a G.card D) i ω| ≤
          nibbleEdgeStepBound k G.card D ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1))
        rw [abs_neg]
        exact nibbleEdge_increment_abs_bound G H P hqr e _ i hp (P.degree_lower_steps i hi).1 ω
      · exact nibbleEdge_increment_abs_bound G H P hqr e _ i hp (P.degree_upper_steps i hi).1 ω
    · rw [nibbleTrackedIncrement_nonedge G H a D e b i heG, Pi.zero_apply, abs_zero]
      exact (nibbleStepBound_pos hqr G P.graph_pos P.degree_pos _).le
  · exact nibbleFaceCount_increment_abs_bound G f a P.graph_pos i ω

theorem nibbleTrackedProcess_difference (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (a D : ℝ) (t : NibbleTrack V r) (i : ℕ) (ω : ℕ → State V q) :
    nibbleTrackedProcess G H a D t (i + 1) ω - nibbleTrackedProcess G H a D t i ω =
      nibbleTrackedIncrement G H a D t i ω := by
  rw [nibbleTrackedProcess_succ]
  ring

end Arxiv2411_18291.CliqueRemovalProcess

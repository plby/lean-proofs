import Arxiv.Arxiv2411_18291.NibbleGoodState

/-! # Critical drift using only the common good event -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def nibbleCriticalWidth (G : Hypergraph V (r + 1)) (a D : ℝ) (t : NibbleTrack V r) : ℝ :=
  match t with
  | .inl _ => a ^ 3 * D * G.card
  | .inr (.inl _) => a ^ 2 * D
  | .inr (.inr _) => a * Fintype.card V

variable (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) {a D p₀ : ℝ}
variable (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))

include P

theorem nibbleGood_count_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (b : Bool) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ nibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inl b) ≤ nibbleTrackedProcess G H a D (.inl b) i ω →
      (probability (r + 1) H)[nibbleTrackedIncrement G H a D (.inl b) i |
        Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let cl := nibbleCliqueLowerComparison k a (G.card : ℝ) D
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  filter_upwards [nibbleCliqueCount_critical_trends hqr G H hHG P Q i hi,
    trajectory_support_ae (r := r + 1) H,
    condExp_neg (μ := probability (r + 1) H) (cliqueCountIncrement (r + 1) H cl i)
      (Filtration.piLE i)] with ω htrend hsupp hneg
  intro hgood hcrit
  have hd := nibbleGood_remaining_degree_bounds P hp hgood hsupp
  have hdev : ∀ e ∈ G \ cliqueSupport (r + 1) (trajectoryCliques ω i),
      |(((remainingCliques (r + 1) H (trajectoryCliques ω i)).filter
        fun Q => e.val ⊆ Q.val).card : ℝ) - nibbleDegreeMain k D p| ≤
          nibbleDegreeError k a D p := by
    intro e he
    have he' := hd e he
    exact abs_le.mpr ⟨by linarith only [he'.1], by linarith only [he'.2]⟩
  have ht := htrend (nibbleGood_clique_deviation hgood) hdev
  cases b
  · change -(a ^ 3 * D * G.card) ≤ -cliqueCountProcess (r + 1) H cl i ω at hcrit
    have hl := ht.2 (by linarith only [hcrit])
    change (probability (r + 1) H)[fun ω => -cliqueCountIncrement (r + 1) H cl i ω |
      Filtration.piLE i] ω =
        -(probability (r + 1) H)[cliqueCountIncrement (r + 1) H cl i | Filtration.piLE i] ω at hneg
    change (probability (r + 1) H)[fun ω => -cliqueCountIncrement (r + 1) H cl i ω |
      Filtration.piLE i] ω ≤ 0
    rw [hneg]
    exact neg_nonpos.mpr hl
  · apply ht.1
    change -(a ^ 3 * D * G.card) ≤ cliqueCountProcess (r + 1) H
      (nibbleCliqueUpperComparison k a G.card D) i ω at hcrit
    linarith only [hcrit]

theorem nibbleGood_edge_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (e : Block V (r + 1))
    (b : Bool) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ nibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inr (.inl (e, b))) ≤
        nibbleTrackedProcess G H a D (.inr (.inl (e, b))) i ω →
      (probability (r + 1) H)[nibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i |
        Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let cl := nibbleDegreeLowerComparison k a (G.card : ℝ) D
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  by_cases heG : e ∈ G
  case neg =>
    rw [nibbleTrackedIncrement_nonedge G H a D e b i heG, condExp_zero]
    exact ae_of_all _ fun _ _ _ => le_rfl
  rw [nibbleTrackedIncrement_edge G H a D e b i heG]
  filter_upwards [nibbleEdge_critical_trends hqr H e P i hi,
    trajectory_support_ae (r := r + 1) H,
    condExp_neg (μ := probability (r + 1) H) (edgeIncrement H e cl i)
      (Filtration.piLE i)] with ω htrend hsupp hneg
  intro hgood hcrit
  have ht := htrend (nibbleGood_remaining_nonempty P hp hgood)
    (nibbleGood_covered_degree_bounds P hHG hp hgood hsupp) (nibbleGood_clique_deviation hgood)
  have hcurrent := hgood (.inr (.inl (e, b)))
  rw [nibbleTrackedProcess_edge G H a D e b i heG] at hcurrent hcrit
  cases b
  · change -(a ^ 2 * D) ≤ -frozenEdgeProcess H e cl i ω at hcrit
    change -frozenEdgeProcess H e cl i ω < 0 at hcurrent
    have hl := ht.2 ⟨by linarith only [hcurrent], by linarith only [hcrit]⟩
    change (probability (r + 1) H)[fun ω => -edgeIncrement H e cl i ω | Filtration.piLE i] ω =
      -(probability (r + 1) H)[edgeIncrement H e cl i | Filtration.piLE i] ω at hneg
    change (probability (r + 1) H)[fun ω => -edgeIncrement H e cl i ω | Filtration.piLE i] ω ≤ 0
    rw [hneg]
    exact neg_nonpos.mpr hl
  · change -(a ^ 2 * D) ≤ frozenEdgeProcess H e
      (nibbleDegreeUpperComparison k a G.card D) i ω at hcrit
    change frozenEdgeProcess H e (nibbleDegreeUpperComparison k a G.card D) i ω < 0 at hcurrent
    exact ht.1 ⟨by linarith only [hcrit], hcurrent.le⟩

theorem nibbleGood_face_trend (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (f : Block V r) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ nibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inr (.inr f)) ≤
        nibbleTrackedProcess G H a D (.inr (.inr f)) i ω →
      (probability (r + 1) H)[nibbleTrackedIncrement G H a D (.inr (.inr f)) i |
        Filtration.piLE i] ω ≤ 0 := by
  filter_upwards [nibbleFaceCount_upper_trend G H hHG f P i hi,
    trajectory_support_ae (r := r + 1) H] with ω htrend hsupp
  intro hgood hcrit
  apply htrend (nibbleGood_clique_deviation hgood)
    (nibbleGood_remaining_degree_bounds P hi hgood hsupp)
  change -(a * Fintype.card V) ≤ faceCountProcess G f
    (nibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card) i ω at hcrit
  linarith only [hcrit]

theorem nibbleGood_tracked_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (t : NibbleTrack V r) (i : ℕ)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ nibbleGood G H a D i →
      -nibbleCriticalWidth G a D t ≤ nibbleTrackedProcess G H a D t i ω →
      (probability (r + 1) H)[nibbleTrackedIncrement G H a D t i | Filtration.piLE i] ω ≤ 0 := by
  rcases t with b | (⟨e, b⟩ | f)
  · exact nibbleGood_count_trend G H P hqr hHG Q b i hi
  · exact nibbleGood_edge_trend G H P hqr hHG e b i hi
  · apply nibbleGood_face_trend G H P hHG f i
    exact (P.consecutive_bounds hi
      (removalDensity_difference (q.choose (r + 1)) (G.card : ℝ) i)).2.2.2

end Arxiv2411_18291.CliqueRemovalProcess

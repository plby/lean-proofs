import Arxiv.Arxiv2411_18291.LogNibbleGoodState
import Arxiv.Arxiv2411_18291.NibbleGoodTrend

/-! # Simultaneous critical drift on the common logarithmic good event -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

variable (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) {a D p₀ : ℝ}
variable (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))

include P

theorem logNibbleGood_count_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (b : Bool) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inl b) ≤ logNibbleTrackedProcess G H a D (.inl b) i ω →
      (probability (r + 1) H)[logNibbleTrackedIncrement G H a D (.inl b) i |
        Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let cl := logNibbleCliqueLowerComparison k a (G.card : ℝ) D
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  filter_upwards [logNibbleCliqueCount_critical_trends hqr P.rank P.rank_le G H hHG
    (card_pos.mp (by exact_mod_cast P.graph_pos)) P.error_pos.le P.degree_pos i
    (P.floor_pos.trans_le hi) (P.error_le_floor.trans hi) (P.power_bound hp)
    P.count_steps P.overlap_bound,
    trajectory_support_ae (r := r + 1) H,
    condExp_neg (μ := probability (r + 1) H) (cliqueCountIncrement (r + 1) H cl i)
      (Filtration.piLE i)] with ω htrend hsupp hneg
  intro hgood hcrit
  have hd := logNibbleGood_remaining_degree_bounds P hp hgood hsupp
  have hdev : ∀ e ∈ G \ cliqueSupport (r + 1) (trajectoryCliques ω i),
      |(((remainingCliques (r + 1) H (trajectoryCliques ω i)).filter
        fun Q => e.val ⊆ Q.val).card : ℝ) - nibbleDegreeMain k D p| ≤
          logNibbleDegreeError k a D p := by
    intro e he
    have he' := hd e he
    exact abs_le.mpr ⟨by linarith only [he'.1], by linarith only [he'.2]⟩
  have ht := htrend (logNibbleGood_clique_deviation hgood) hdev
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
      (logNibbleCliqueUpperComparison k a G.card D) i ω at hcrit
    linarith only [hcrit]

theorem logNibbleGood_edge_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (e : Block V (r + 1))
    (b : Bool) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inr (.inl (e, b))) ≤
        logNibbleTrackedProcess G H a D (.inr (.inl (e, b))) i ω →
      (probability (r + 1) H)[logNibbleTrackedIncrement G H a D (.inr (.inl (e, b))) i |
        Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let cl := logNibbleDegreeLowerComparison k a (G.card : ℝ) D
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  by_cases heG : e ∈ G
  case neg =>
    rw [logNibbleTrackedIncrement_nonedge G H a D e b i heG, condExp_zero]
    exact ae_of_all _ fun _ _ _ => le_rfl
  rw [logNibbleTrackedIncrement_edge G H a D e b i heG]
  filter_upwards [logNibbleEdge_critical_trends hqr P.rank P.rank_le H e P.error_pos.le
    P.graph_pos P.degree_pos i (P.floor_pos.trans_le hi)
    (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.1
    (P.power_bound hp) P.many_edges P.codegree_bound,
    trajectory_support_ae (r := r + 1) H,
    condExp_neg (μ := probability (r + 1) H) (edgeIncrement H e cl i)
      (Filtration.piLE i)] with ω htrend hsupp hneg
  intro hgood hcrit
  have ht := htrend (logNibbleGood_remaining_nonempty P hp hgood)
    (logNibbleGood_covered_degree_bounds P hHG hp hgood hsupp)
    (logNibbleGood_clique_deviation hgood)
  have hcurrent := hgood (.inr (.inl (e, b)))
  rw [logNibbleTrackedProcess_edge G H a D e b i heG] at hcurrent hcrit
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
      (logNibbleDegreeUpperComparison k a G.card D) i ω at hcrit
    change frozenEdgeProcess H e (logNibbleDegreeUpperComparison k a G.card D) i ω < 0 at hcurrent
    exact ht.1 ⟨by linarith only [hcrit], hcurrent.le⟩

theorem logNibbleGood_face_trend (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (f : Block V r) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      -nibbleCriticalWidth G a D (.inr (.inr f)) ≤
        logNibbleTrackedProcess G H a D (.inr (.inr f)) i ω →
      (probability (r + 1) H)[logNibbleTrackedIncrement G H a D (.inr (.inr f)) i |
        Filtration.piLE i] ω ≤ 0 := by
  filter_upwards [logNibbleFaceCount_upper_trend G H hHG f P i hi,
    trajectory_support_ae (r := r + 1) H] with ω htrend hsupp
  intro hgood hcrit
  apply htrend (logNibbleGood_clique_deviation hgood)
    (logNibbleGood_remaining_degree_bounds P hi hgood hsupp)
  change -(a * Fintype.card V) ≤ faceCountProcess G f
    (logNibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card) i ω at hcrit
  linarith only [hcrit]

theorem logNibbleGood_tracked_trend (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (t : NibbleTrack V r) (i : ℕ)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      -nibbleCriticalWidth G a D t ≤ logNibbleTrackedProcess G H a D t i ω →
      (probability (r + 1) H)[logNibbleTrackedIncrement G H a D t i | Filtration.piLE i] ω ≤ 0 := by
  rcases t with b | (⟨e, b⟩ | f)
  · exact logNibbleGood_count_trend G H P hqr hHG b i hi
  · exact logNibbleGood_edge_trend G H P hqr hHG e b i hi
  · apply logNibbleGood_face_trend G H P hHG f i
    exact (P.consecutive_bounds hi
      (removalDensity_difference (q.choose (r + 1)) (G.card : ℝ) i)).2.2.2

end Arxiv2411_18291.CliqueRemovalProcess

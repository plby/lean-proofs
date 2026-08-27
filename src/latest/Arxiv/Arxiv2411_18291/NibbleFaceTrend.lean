import Arxiv.Arxiv2411_18291.NibbleFaceComparisons
import Arxiv.Arxiv2411_18291.FaceCountConditionalDrift
import Arxiv.Arxiv2411_18291.GraphBoundedness

/-! # Concrete upper face drift for the random clique-removal process -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

theorem face_degree_le_card {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (G : Hypergraph V (r + 1)) (f : Block V r) :
    (G.filter fun e => f.val ⊆ e.val).card ≤ Fintype.card V := by
  rw [← card_neighbors_eq_degree]
  exact card_le_univ _

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibbleFaceCount_upper_trend (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    let p := removalDensity (q.choose (r + 1)) G.card i
    let c := nibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain (q.choose (r + 1)) G.card D p| ≤
        nibbleCliqueError (q.choose (r + 1)) a G.card D p →
      (∀ e ∈ E,
        nibbleDegreeMain (q.choose (r + 1)) D p - nibbleDegreeError (q.choose (r + 1)) a D p ≤
            ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            nibbleDegreeMain (q.choose (r + 1)) D p + nibbleDegreeError (q.choose (r + 1)) a D p) →
      -a * Fintype.card V ≤ faceCountProcess G f c i ω →
      (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let F : ℝ := (G.filter fun e => f.val ⊆ e.val).card
  let c := nibbleFaceUpperComparison k a (G.card : ℝ) (Fintype.card V : ℝ) F
  filter_upwards [faceCountIncrement_condExp_bounds G H hHG f c i
    (nibbleDegreeMain k D p - nibbleDegreeError k a D p)
    (nibbleDegreeMain k D p + nibbleDegreeError k a D p)] with ω hω
  dsimp only
  intro hh hd hc
  let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
  let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
  let d : ℝ := (E.filter fun e => f.val ⊆ e.val).card
  have hFn : F ≤ (Fintype.card V : ℝ) := by
    dsimp only [F]
    exact_mod_cast face_degree_le_card G f
  have hdn : d ≤ (Fintype.card V : ℝ) := by
    dsimp only [d]
    exact_mod_cast face_degree_le_card E f
  have hcrit : nibbleFaceUpper k a (Fintype.card V : ℝ) F p - a * Fintype.card V ≤ d := by
    change -a * Fintype.card V ≤ d - nibbleFaceUpper k a (Fintype.card V : ℝ) F p at hc
    linarith only [hc]
  have htrend := P.face_upper_drift hi (removalDensity_le_one k P.graph_pos i)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hFn hdn hh hcrit
  have hδ : c (i + 1) - c i = -(k : ℝ) * F / G.card :=
    nibbleFaceUpperComparison_increment k a (G.card : ℝ) (Fintype.card V : ℝ) F i
  calc
    _ ≤ -(d * (nibbleDegreeMain k D p - nibbleDegreeError k a D p) / R.card) -
        (c (i + 1) - c i) := (hω hd).2
    _ = -(d * (nibbleDegreeMain k D p - nibbleDegreeError k a D p) / R.card) +
        (k : ℝ) * F / G.card := by rw [hδ]; ring
    _ ≤ 0 := htrend

end CliqueRemovalProcess

end Arxiv2411_18291

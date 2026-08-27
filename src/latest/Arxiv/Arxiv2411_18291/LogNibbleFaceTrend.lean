import Arxiv.Arxiv2411_18291.LogNibbleFaceComparisons
import Arxiv.Arxiv2411_18291.NibbleFaceTrend
import Arxiv.Arxiv2411_18291.FaceCountVariance

/-! # Logarithmic-route face drift and variance on the actual trajectory -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem logNibbleFaceCount_upper_trend (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    let p := removalDensity (q.choose (r + 1)) G.card i
    let c := logNibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain (q.choose (r + 1)) G.card D p| ≤
        logNibbleCliqueError (q.choose (r + 1)) a G.card D p →
      (∀ e ∈ E,
        nibbleDegreeMain (q.choose (r + 1)) D p - logNibbleDegreeError (q.choose (r + 1)) a D p ≤
            ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            nibbleDegreeMain (q.choose (r + 1)) D p +
              logNibbleDegreeError (q.choose (r + 1)) a D p) →
      -a * Fintype.card V ≤ faceCountProcess G f c i ω →
      (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i] ω ≤ 0 := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let F : ℝ := (G.filter fun e => f.val ⊆ e.val).card
  let c := logNibbleFaceUpperComparison k a (G.card : ℝ) (Fintype.card V : ℝ) F
  filter_upwards [faceCountIncrement_condExp_bounds G H hHG f c i
    (nibbleDegreeMain k D p - logNibbleDegreeError k a D p)
    (nibbleDegreeMain k D p + logNibbleDegreeError k a D p)] with ω hω
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
  have hcrit : logNibbleFaceUpper a (Fintype.card V : ℝ) F p - a * Fintype.card V ≤ d := by
    change -a * Fintype.card V ≤ d - logNibbleFaceUpper a (Fintype.card V : ℝ) F p at hc
    linarith only [hc]
  have htrend := P.face_upper_drift hi (removalDensity_le_one k P.graph_pos i)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hFn hdn hh hcrit
  have hδ : c (i + 1) - c i = -(k : ℝ) * F / G.card :=
    logNibbleFaceUpperComparison_increment k a (G.card : ℝ) (Fintype.card V : ℝ) F i
  calc
    _ ≤ -(d * (nibbleDegreeMain k D p - logNibbleDegreeError k a D p) / R.card) -
        (c (i + 1) - c i) := (hω hd).2
    _ = -(d * (nibbleDegreeMain k D p - logNibbleDegreeError k a D p) / R.card) +
        (k : ℝ) * F / G.card := by rw [hδ]; ring
    _ ≤ 0 := htrend

theorem logNibbleFaceCount_condVar_le (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    let c := logNibbleFaceUpperComparison k a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain k G.card D p| ≤ logNibbleCliqueError k a G.card D p →
      (∀ e ∈ E, ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        nibbleDegreeMain k D p + logNibbleDegreeError k a D p) →
      faceCountProcess G f c i ω ≤ 0 →
      Var[faceCountIncrement G f c i; probability (r + 1) H | Filtration.piLE i] ω ≤
        12 * ((q - r : ℕ) : ℝ) * k * Fintype.card V / G.card := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let F : ℝ := (G.filter fun e => f.val ⊆ e.val).card
  let c := logNibbleFaceUpperComparison k a (G.card : ℝ) (Fintype.card V : ℝ) F
  have hp1 := removalDensity_le_one k P.graph_pos i
  have hk : 0 < k := by have h := P.rank; dsimp only [k]; omega
  have hp0 := P.floor_pos.trans_le hi
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  have hv := ((P.point_conditions hi hp1).count_bounds hk P.degree_pos.le
    P.graph_pos.le hp0.le).1
  filter_upwards [faceCountIncrement_condVar_of_degree_bound G H hHG f c i
    (nibbleDegreeMain k D p + logNibbleDegreeError k a D p)] with ω hω
  dsimp only
  intro hh hd hc
  let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
  let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
  let d : ℝ := (E.filter fun e => f.val ⊆ e.val).card
  have hhalf : nibbleCliqueMain k G.card D p / 2 ≤ (R.card : ℝ) := by
    have hlo := (abs_le.mp hh).1
    dsimp only [R, p, k]
    linarith only [hlo, hv, hh₀]
  have hFn : F ≤ (Fintype.card V : ℝ) := by
    dsimp only [F]
    exact_mod_cast face_degree_le_card G f
  have hface : d ≤ logNibbleFaceUpper a (Fintype.card V : ℝ) F p := by
    change d - logNibbleFaceUpper a (Fintype.card V : ℝ) F p ≤ 0 at hc
    linarith only [hc]
  have havg := P.face_average_loss_le hi hp1 (Nat.cast_nonneg _) hFn
    (Nat.cast_nonneg _) hhalf hface
  calc
    _ ≤ ((q - r : ℕ) : ℝ) *
        (d * (nibbleDegreeMain k D p + logNibbleDegreeError k a D p) / R.card) := hω hd
    _ ≤ ((q - r : ℕ) : ℝ) *
        (12 * k * Fintype.card V / G.card) :=
      mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)
    _ = _ := by ring

theorem logNibbleFaceCount_increment_abs_bound (G : Hypergraph V (r + 1))
    (f : Block V r) (a : ℝ) (hg : 0 < (G.card : ℝ)) (i : ℕ) (ω : ℕ → State V q) :
    let k := q.choose (r + 1)
    let c := logNibbleFaceUpperComparison k a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    |faceCountIncrement G f c i ω| ≤
      ((q - r : ℕ) : ℝ) + (k : ℝ) * Fintype.card V / G.card := by
  dsimp only
  have hF : ((G.filter fun e => f.val ⊆ e.val).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast face_degree_le_card G f
  have h := faceCountIncrement_abs_bound G f
    (logNibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card) i ω
  rw [logNibbleFaceUpperComparison_increment, neg_mul, neg_div, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hg.le)] at h
  exact h.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) hg.le))

end CliqueRemovalProcess

end Arxiv2411_18291

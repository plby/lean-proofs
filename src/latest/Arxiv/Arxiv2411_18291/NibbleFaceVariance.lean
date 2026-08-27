import Arxiv.Arxiv2411_18291.NibbleFaceTrend
import Arxiv.Arxiv2411_18291.NibbleFaceLossBound
import Arxiv.Arxiv2411_18291.FaceCountVariance

/-! # Uniform face variance and absolute increments for the concrete comparison -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibbleFaceCount_condVar_le (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    let c := nibbleFaceUpperComparison k a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain k G.card D p| ≤ nibbleCliqueError k a G.card D p →
      (∀ e ∈ E, ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        nibbleDegreeMain k D p + nibbleDegreeError k a D p) →
      faceCountProcess G f c i ω ≤ 0 →
      Var[faceCountIncrement G f c i; probability (r + 1) H | Filtration.piLE i] ω ≤
        4 * ((q - r : ℕ) : ℝ) * (1 + 128 * (k : ℝ)) * k * Fintype.card V / G.card := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let F : ℝ := (G.filter fun e => f.val ⊆ e.val).card
  let c := nibbleFaceUpperComparison k a (G.card : ℝ) (Fintype.card V : ℝ) F
  have hp1 := removalDensity_le_one k P.graph_pos i
  obtain ⟨_, _, _, _, _, _, _, _, hv, _, _⟩ := P.edge_conditions hi hp1
  filter_upwards [faceCountIncrement_condVar_of_degree_bound G H hHG f c i
    (nibbleDegreeMain k D p + nibbleDegreeError k a D p)] with ω hω
  dsimp only
  intro hh hd hc
  let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
  let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
  let d : ℝ := (E.filter fun e => f.val ⊆ e.val).card
  have hhalf : nibbleCliqueMain k G.card D p / 2 ≤ (R.card : ℝ) := by
    have hlo := (abs_le.mp hh).1
    dsimp only [R, p, k]
    linarith only [hlo, hv]
  have hFn : F ≤ (Fintype.card V : ℝ) := by
    dsimp only [F]
    exact_mod_cast face_degree_le_card G f
  have hface : d ≤ nibbleFaceUpper k a (Fintype.card V : ℝ) F p := by
    change d - nibbleFaceUpper k a (Fintype.card V : ℝ) F p ≤ 0 at hc
    linarith only [hc]
  have havg := P.face_average_loss_le hi hp1 (Nat.cast_nonneg _) hFn
    (Nat.cast_nonneg _) hhalf hface
  calc
    _ ≤ ((q - r : ℕ) : ℝ) *
        (d * (nibbleDegreeMain k D p + nibbleDegreeError k a D p) / R.card) := hω hd
    _ ≤ ((q - r : ℕ) : ℝ) *
        (4 * (1 + 128 * (k : ℝ)) * k * Fintype.card V / G.card) :=
      mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)
    _ = _ := by ring

theorem nibbleFaceCount_increment_abs_bound (G : Hypergraph V (r + 1))
    (f : Block V r) (a : ℝ) (hg : 0 < (G.card : ℝ)) (i : ℕ) (ω : ℕ → State V q) :
    let k := q.choose (r + 1)
    let c := nibbleFaceUpperComparison k a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card
    |faceCountIncrement G f c i ω| ≤
      ((q - r : ℕ) : ℝ) + (k : ℝ) * Fintype.card V / G.card := by
  dsimp only
  have hF : ((G.filter fun e => f.val ⊆ e.val).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast face_degree_le_card G f
  have h := faceCountIncrement_abs_bound G f
    (nibbleFaceUpperComparison (q.choose (r + 1)) a G.card (Fintype.card V)
      (G.filter fun e => f.val ⊆ e.val).card) i ω
  rw [nibbleFaceUpperComparison_increment, neg_mul, neg_div, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hg.le)] at h
  exact h.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) hg.le))

end Arxiv2411_18291.CliqueRemovalProcess

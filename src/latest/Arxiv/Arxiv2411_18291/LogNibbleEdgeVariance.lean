import Arxiv.Arxiv2411_18291.LogNibbleGoodState
import Arxiv.Arxiv2411_18291.LogNibbleEdgeLossBound

/-! # Frozen-edge increments and conditional variance under the logarithmic good event -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable (G : Hypergraph V (r + 1)) (H : Finset (Block V q)) {a D p₀ : ℝ}
variable (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))

include P

theorem logNibbleEdge_increment_abs_bound (hqr : r + 1 < q) (e : Block V (r + 1))
    (c : ℕ → ℝ) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hc : |c (i + 1) - c i| ≤
      2 * nibbleEdgeSlope (q.choose (r + 1)) G.card D
        (removalDensity (q.choose (r + 1)) G.card i)) (ω : ℕ → State V q) :
    |edgeIncrement H e c i ω| ≤ nibbleEdgeStepBound (q.choose (r + 1)) G.card D
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)) :=
  (edgeIncrement_abs_bound hqr H e c i ω).trans
    (P.edge_increment_scale_le hi (removalDensity_le_one _ P.graph_pos i) hc)

theorem logNibbleGood_edge_condVar_le (hqr : r + 1 < q)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (e : Block V (r + 1)) (heG : e ∈ G)
    (c : ℕ → ℝ) (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hc : |c (i + 1) - c i| ≤
      2 * nibbleEdgeSlope (q.choose (r + 1)) G.card D
        (removalDensity (q.choose (r + 1)) G.card i)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      Var[edgeIncrement H e c i; probability (r + 1) H | Filtration.piLE i] ω ≤
        nibbleEdgeStepBound (q.choose (r + 1)) G.card D
          ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)) *
            (10 * (q.choose (r + 1) : ℝ) ^ 2 * D / G.card) := by
  let k := q.choose (r + 1)
  let p := removalDensity k (G.card : ℝ) i
  let m := nibbleDegreeMain k D p
  let u := logNibbleDegreeError k a D p
  let L := (Fintype.card V : ℝ) ^ (q - (r + 1) - 1)
  have hp1 := removalDensity_le_one k P.graph_pos i
  have hp0 := P.floor_pos.trans_le hi
  have hk : 0 < k := by have h := P.rank; dsimp only [k]; omega
  have hm := nibbleDegreeMain_pos (k := k) P.degree_pos hp0
  have hL := nibbleLogFactor_one_le k hp0 hp1
  have hu : 0 ≤ logNibbleDegreeError k a D p := by
    have hD := P.degree_pos
    unfold logNibbleDegreeError
    positivity
  have hh₀ := nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0
  have hv := ((P.point_conditions hi hp1).count_bounds hk P.degree_pos.le
    P.graph_pos.le hp0.le).1
  have hfirst := P.edge_increment_scale_le hi hp1 hc
  have hB : 0 ≤ nibbleEdgeStepBound k G.card D L :=
    nibbleEdgeStepBound_nonneg k P.graph_pos.le P.degree_pos.le P.codegree_nonneg
  have hscale : 0 ≤ 10 * (k : ℝ) ^ 2 * D / G.card := by
    have hD := P.degree_pos
    have hg := P.graph_pos
    positivity
  have hmain := nibbleEdgeSlope_le k P.graph_pos P.degree_pos.le hp0.le hp1
  filter_upwards [edgeIncrement_condVar_of_degree_bounds hqr H e c i (m - u) (m + u),
    edgeIncrement_condVar_of_removed hqr H e c i, trajectory_support_ae (r := r + 1) H]
    with ω hvar hremoved hsupp
  intro hgood
  by_cases he : e ∈ cliqueSupport (r + 1) (trajectoryCliques ω i)
  · rw [hremoved he]
    exact mul_nonneg hB hscale
  let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
  let x : ℝ := (R.filter fun Q => e.val ⊆ Q.val).card
  have hR := logNibbleGood_remaining_nonempty P hi hgood
  have hd := logNibbleGood_covered_degree_bounds P hHG hi hgood hsupp
  have hx := (logNibbleGood_live_degree_bounds P hi hgood hsupp e heG he).2
  have hh := logNibbleGood_clique_deviation hgood
  have hhalf : nibbleCliqueMain k G.card D p / 2 ≤ (R.card : ℝ) := by
    have hlo := (abs_le.mp hh).1
    dsimp only [R, p, k]
    linarith only [hlo, hv, hh₀]
  have havg := P.edge_average_loss_le hi hp1 hx hhalf
  have hsecond : (x / R.card) * ((k - 1 : ℕ) : ℝ) * (m + u) + |c (i + 1) - c i| ≤
      10 * (k : ℝ) ^ 2 * D / G.card := by
    calc
      _ ≤ 8 * nibbleEdgeSlope k G.card D p + 2 * nibbleEdgeSlope k G.card D p :=
        add_le_add havg hc
      _ = 10 * nibbleEdgeSlope k G.card D p := by ring
      _ ≤ 10 * ((k : ℝ) ^ 2 * D / G.card) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = _ := by ring
  have hnonneg : 0 ≤ (x / R.card) * ((k - 1 : ℕ) : ℝ) * (m + u) + |c (i + 1) - c i| := by
    have hmu : 0 ≤ m + u := add_nonneg hm.le hu
    have hx0 : 0 ≤ x := Nat.cast_nonneg _
    positivity
  exact (hvar he hR hd).trans (mul_le_mul hfirst hsecond hnonneg hB)

end Arxiv2411_18291.CliqueRemovalProcess

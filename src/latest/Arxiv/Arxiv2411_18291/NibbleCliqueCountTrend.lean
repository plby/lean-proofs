import Arxiv.Arxiv2411_18291.NibbleComparisonSequences
import Arxiv.Arxiv2411_18291.CliqueCountConditionalDrift
import Arxiv.Arxiv2411_18291.CliqueRemovalAvailability

/-! # Both concrete clique-count drift signs under the actual trajectory law -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibbleCliqueCount_critical_trends (hqr : r < q) (G : Hypergraph V r)
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose r) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - r - 1)))
    (Q : NibbleCountConditions (q.choose r) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - r - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose r) G.card (i + 1)) :
    let p := removalDensity (q.choose r) G.card i
    let cu := nibbleCliqueUpperComparison (q.choose r) a G.card D
    let cl := nibbleCliqueLowerComparison (q.choose r) a G.card D
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let E := G \ cliqueSupport r (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain (q.choose r) G.card D p| ≤
        nibbleCliqueError (q.choose r) a G.card D p →
      (∀ e ∈ E, |((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        nibbleDegreeMain (q.choose r) D p| ≤ nibbleDegreeError (q.choose r) a D p) →
      (-a ^ 3 * D * G.card ≤ cliqueCountProcess r H cu i ω →
        (probability r H)[cliqueCountIncrement r H cu i | Filtration.piLE i] ω ≤ 0) ∧
      (cliqueCountProcess r H cl i ω ≤ a ^ 3 * D * G.card →
        0 ≤ (probability r H)[cliqueCountIncrement r H cl i | Filtration.piLE i] ω) := by
  let p := removalDensity (q.choose r) (G.card : ℝ) i
  let cu := nibbleCliqueUpperComparison (q.choose r) a (G.card : ℝ) D
  let cl := nibbleCliqueLowerComparison (q.choose r) a (G.card : ℝ) D
  have hstep := removalDensity_difference (q.choose r) (G.card : ℝ) i
  have hp := (P.consecutive_bounds hi hstep).2.2.2
  have hp1 := removalDensity_le_one (q.choose r) P.graph_pos i
  have hp0 := P.floor_pos.trans_le hp
  have hG : G.Nonempty := card_pos.mp (by exact_mod_cast P.graph_pos)
  obtain ⟨_, _, _, _, _, _, _, hh₀, hv, _, _⟩ := P.edge_conditions hp hp1
  filter_upwards [trajectory_support_ae (r := r) H,
    cliqueCountIncrement_condExp_bounds hqr G H hHG cu i
      (nibbleDegreeMain (q.choose r) D p) (nibbleDegreeError (q.choose r) a D p),
    cliqueCountIncrement_condExp_bounds hqr G H hHG cl i
      (nibbleDegreeMain (q.choose r) D p) (nibbleDegreeError (q.choose r) a D p)]
    with ω hsupp hcu hcl
  dsimp only
  intro hh hd
  let R := remainingCliques r H (trajectoryCliques ω i)
  let E := G \ cliqueSupport r (trajectoryCliques ω i)
  have hhalf : nibbleCliqueMain (q.choose r) G.card D p / 2 ≤ (R.card : ℝ) := by
    have hlo := (abs_le.mp hh).1
    dsimp only [R, p]
    linarith only [hlo, hv]
  have hRpos : (0 : ℝ) < R.card := (half_pos hh₀).trans_le hhalf
  have hR : R.Nonempty := card_pos.mp (by exact_mod_cast hRpos)
  have hEeq : (E.card : ℝ) = p * G.card :=
    trajectory_leave_density H ω hsupp hqr.le G hG hHG i hR
  have hEpos : (0 : ℝ) < E.card := by
    rw [hEeq]
    exact mul_pos hp0 P.graph_pos
  have hE : E.Nonempty := card_pos.mp (by exact_mod_cast hEpos)
  have hu := (hcu hR hE hd).2
  have hl := (hcl hR hE hd).1
  change _ ≤ -((q.choose r : ℝ) ^ 2 * R.card / E.card) +
    (q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1) - (cu (i + 1) - cu i) at hu
  change -((q.choose r : ℝ) ^ 2 * R.card / E.card) -
    E.card * nibbleDegreeError (q.choose r) a D p ^ 2 / R.card - (cl (i + 1) - cl i) ≤ _ at hl
  rw [hEeq] at hu hl
  constructor
  · intro hc
    have hcrit : nibbleCliqueUpper (q.choose r) a G.card D p - a ^ 3 * D * G.card ≤
        (R.card : ℝ) := by
      change -a ^ 3 * D * G.card ≤ (R.card : ℝ) -
        nibbleCliqueUpper (q.choose r) a G.card D p at hc
      linarith only [hc]
    exact hu.trans (Q.upper_drift P hi hp1 hstep hcrit)
  · intro hc
    have hcrit : (R.card : ℝ) ≤
        nibbleCliqueLower (q.choose r) a G.card D p + a ^ 3 * D * G.card := by
      change (R.card : ℝ) - nibbleCliqueLower (q.choose r) a G.card D p ≤
        a ^ 3 * D * G.card at hc
      linarith only [hc]
    exact (Q.lower_drift P hi hp1 hstep hhalf hcrit).trans hl

end Arxiv2411_18291.CliqueRemovalProcess

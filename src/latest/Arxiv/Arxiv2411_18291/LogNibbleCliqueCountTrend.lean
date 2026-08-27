import Arxiv.Arxiv2411_18291.LogNibbleCountConditions
import Arxiv.Arxiv2411_18291.LogNibbleCliqueSteps
import Arxiv.Arxiv2411_18291.CliqueCountConditionalDrift
import Arxiv.Arxiv2411_18291.CliqueRemovalAvailability
import Arxiv.Arxiv2411_18291.NibbleComparisonSequences

/-! # Both logarithmic clique-count trends under the actual trajectory law -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

def logNibbleCliqueUpperComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  logNibbleCliqueUpper k a g D (removalDensity k g i)

def logNibbleCliqueLowerComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  logNibbleCliqueLower k a g D (removalDensity k g i)

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem logNibbleCliqueCount_critical_trends (hqr : r < q) (hk : 3 ≤ q.choose r)
    (hk5 : q.choose r ≤ 5) (G : Hypergraph V r) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (hG : G.Nonempty)
    {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (i : ℕ)
    (hs : 0 < removalDensity (q.choose r) G.card (i + 1))
    (has : a ≤ removalDensity (q.choose r) G.card (i + 1))
    (hac : a ≤ ((2 / 5 : ℝ) * removalDensity (q.choose r) G.card i) ^ (q.choose r))
    (hsteps : (q.choose r : ℝ) ≤ a ^ 3 * G.card)
    (hL : (Fintype.card V : ℝ) ^ (q - r - 1) ≤ a ^ 3 * D) :
    let p := removalDensity (q.choose r) G.card i
    let cu := logNibbleCliqueUpperComparison (q.choose r) a G.card D
    let cl := logNibbleCliqueLowerComparison (q.choose r) a G.card D
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let E := G \ cliqueSupport r (trajectoryCliques ω i)
      |(R.card : ℝ) - nibbleCliqueMain (q.choose r) G.card D p| ≤
        logNibbleCliqueError (q.choose r) a G.card D p →
      (∀ e ∈ E, |((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        nibbleDegreeMain (q.choose r) D p| ≤ logNibbleDegreeError (q.choose r) a D p) →
      (-a ^ 3 * D * G.card ≤ cliqueCountProcess r H cu i ω →
        (probability r H)[cliqueCountIncrement r H cu i | Filtration.piLE i] ω ≤ 0) ∧
      (cliqueCountProcess r H cl i ω ≤ a ^ 3 * D * G.card →
        0 ≤ (probability r H)[cliqueCountIncrement r H cl i | Filtration.piLE i] ω) := by
  let p := removalDensity (q.choose r) (G.card : ℝ) i
  let cu := logNibbleCliqueUpperComparison (q.choose r) a (G.card : ℝ) D
  let cl := logNibbleCliqueLowerComparison (q.choose r) a (G.card : ℝ) D
  have hg : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr hG
  have hstep := removalDensity_difference (q.choose r) (G.card : ℝ) i
  have hsp : removalDensity (q.choose r) G.card (i + 1) ≤ p := by
    have hh : 0 ≤ (q.choose r : ℝ) / G.card := by positivity
    dsimp only [p]
    linarith only [hstep, hh]
  have hp := hs.trans_le hsp
  have hp1 := removalDensity_le_one (q.choose r) hg i
  have hk0 : 0 < q.choose r := by omega
  have P := log_nibble_scalar_conditions hk hk5 hp hp1 ha hac
  have hh₀ := nibbleCliqueMain_pos hk0 hg hD hp
  have hv := (P.count_bounds hk0 hD.le hg.le hp.le).1
  have hgap := log_nibble_count_overlap_margin (q.choose r) ha hg.le hD.le hp hp1 hL
  have hvariance := log_nibble_count_variance_margin hk ha hg hD hp hp1 hac
  obtain ⟨hδu, hδl, _, _⟩ := logNibbleClique_comparison_step_control hk ha hg hD.le
    hs hsp hp1 has hstep hsteps
  rw [nibbleCliqueSlope_eq_main_ratio hk0 hg.ne' hp.ne'] at hδu hδl
  filter_upwards [trajectory_support_ae (r := r) H,
    cliqueCountIncrement_condExp_bounds hqr G H hHG cu i
      (nibbleDegreeMain (q.choose r) D p) (logNibbleDegreeError (q.choose r) a D p),
    cliqueCountIncrement_condExp_bounds hqr G H hHG cl i
      (nibbleDegreeMain (q.choose r) D p) (logNibbleDegreeError (q.choose r) a D p)]
    with ω hsupp hcu hcl
  dsimp only
  intro hh hd
  let R := remainingCliques r H (trajectoryCliques ω i)
  let E := G \ cliqueSupport r (trajectoryCliques ω i)
  have hhalf : nibbleCliqueMain (q.choose r) G.card D p / 2 ≤ (R.card : ℝ) := by
    have hlo := (abs_le.mp hh).1
    dsimp only [R, p]
    linarith only [hlo, hv, hh₀]
  have hRpos : (0 : ℝ) < R.card := (half_pos hh₀).trans_le hhalf
  have hR : R.Nonempty := card_pos.mp (by exact_mod_cast hRpos)
  have hEeq : (E.card : ℝ) = p * G.card :=
    trajectory_leave_density H ω hsupp hqr.le G hG hHG i hR
  have hEpos : (0 : ℝ) < E.card := by rw [hEeq]; exact mul_pos hp hg
  have hE : E.Nonempty := card_pos.mp (by exact_mod_cast hEpos)
  have hu := (hcu hR hE hd).2
  have hl := (hcl hR hE hd).1
  change _ ≤ -((q.choose r : ℝ) ^ 2 * R.card / E.card) +
    (q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1) - (cu (i + 1) - cu i) at hu
  change -((q.choose r : ℝ) ^ 2 * R.card / E.card) -
    E.card * logNibbleDegreeError (q.choose r) a D p ^ 2 / R.card -
      (cl (i + 1) - cl i) ≤ _ at hl
  rw [hEeq] at hu hl
  constructor
  · intro hc
    have hcrit : nibbleCliqueMain (q.choose r) G.card D p +
        logNibbleCliqueError (q.choose r) a G.card D p - a ^ 3 * D * G.card ≤
        (R.card : ℝ) := by
      change -a ^ 3 * D * G.card ≤ (R.card : ℝ) -
        (nibbleCliqueMain (q.choose r) G.card D p +
          logNibbleCliqueError (q.choose r) a G.card D p) at hc
      linarith only [hc]
    exact hu.trans (clique_count_upper_drift_nonpos (mul_pos hp hg) hgap hcrit hδu)
  · intro hc
    have hcrit : (R.card : ℝ) ≤ nibbleCliqueMain (q.choose r) G.card D p -
        logNibbleCliqueError (q.choose r) a G.card D p + a ^ 3 * D * G.card := by
      change (R.card : ℝ) - (nibbleCliqueMain (q.choose r) G.card D p -
        logNibbleCliqueError (q.choose r) a G.card D p) ≤ a ^ 3 * D * G.card at hc
      linarith only [hc]
    exact (clique_count_lower_drift_nonneg (mul_pos hp hg) hh₀ hhalf hcrit hvariance hδl).trans hl

end CliqueRemovalProcess

end Arxiv2411_18291

import Arxiv.Arxiv2411_18291.NibbleEdgeSequenceSteps
import Arxiv.Arxiv2411_18291.FrozenEdgeCriticalTrend
import Arxiv.Arxiv2411_18291.CliqueRemovalAvailability

/-! # Critical drift of both concrete frozen-edge processes, including removed edges -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem nibbleEdge_critical_trends (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    {a g D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose r) a g D p₀
      ((Fintype.card V : ℝ) ^ (q - r - 1)))
    (i : ℕ) (hi : p₀ ≤ removalDensity (q.choose r) g (i + 1)) :
    let p := removalDensity (q.choose r) g i
    let m := nibbleDegreeMain (q.choose r) D p
    let u := nibbleDegreeError (q.choose r) a D p
    let cu := nibbleDegreeUpperComparison (q.choose r) a g D
    let cl := nibbleDegreeLowerComparison (q.choose r) a g D
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        m - u ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ m + u) →
      |(R.card : ℝ) - nibbleCliqueMain (q.choose r) g D p| ≤
        nibbleCliqueError (q.choose r) a g D p →
      (-a ^ 2 * D ≤ frozenEdgeProcess H e cu i ω ∧ frozenEdgeProcess H e cu i ω ≤ 0 →
        (probability r H)[edgeIncrement H e cu i | Filtration.piLE i] ω ≤ 0) ∧
      (0 ≤ frozenEdgeProcess H e cl i ω ∧ frozenEdgeProcess H e cl i ω ≤ a ^ 2 * D →
        0 ≤ (probability r H)[edgeIncrement H e cl i | Filtration.piLE i] ω) := by
  let p := removalDensity (q.choose r) g i
  let cu := nibbleDegreeUpperComparison (q.choose r) a g D
  let cl := nibbleDegreeLowerComparison (q.choose r) a g D
  have hp := (P.consecutive_bounds hi (removalDensity_difference (q.choose r) g i)).2.2.2
  have hp1 := removalDensity_le_one (q.choose r) P.graph_pos i
  obtain ⟨hm, hu, ht, hwt, htm, hum, hu2, hh₀, hv, hvm, hC⟩ := P.edge_conditions hp hp1
  obtain ⟨_, huneg, hustep⟩ := P.degree_upper_steps i hi
  obtain ⟨hlabs, hlstep⟩ := P.degree_lower_steps i hi
  have hB : 0 ≤ 2 * nibbleEdgeSlope (q.choose r) g D p :=
    mul_nonneg (by norm_num) (nibbleEdgeSlope_nonneg _ P.graph_pos.le P.degree_pos.le
      (P.floor_pos.trans_le hp).le)
  have hδB : -(cl (i + 1) - cl i) ≤ 2 * nibbleEdgeSlope (q.choose r) g D p :=
    (neg_le_abs _).trans hlabs
  filter_upwards [trajectory_support_ae (r := r) H,
    edgeIncrement_condExp_of_removed H e cu i,
    edgeIncrement_condExp_of_removed H e cl i,
    edgeIncrement_nonpos_of_upper_critical hqr H e cu i hm.le hu ht hwt hum hu2
      hh₀ hv hvm hC huneg hustep,
    edgeIncrement_nonneg_of_lower_critical hqr H e cl i hm.le hu ht hwt htm hum hu2
      hh₀ hv hvm hB hδB hlstep] with ω hsupp hremovedu hremovedl hupper hlower
  dsimp only
  intro hR hd hh
  by_cases he : e ∈ cliqueSupport r (trajectoryCliques ω i)
  · exact ⟨fun _ => (hremovedu he).le, fun _ => (hremovedl he).ge⟩
  have huval := frozenEdgeProcess_eq_of_remaining_nonempty H ω hsupp e cu i hR he
  have hlval := frozenEdgeProcess_eq_of_remaining_nonempty H ω hsupp e cl i hR he
  constructor
  · intro hc
    change -a ^ 2 * D ≤ frozenEdgeProcess H e cu i ω ∧
      frozenEdgeProcess H e cu i ω ≤ 0 at hc
    rw [huval] at hc
    change -a ^ 2 * D ≤ _ - (nibbleDegreeMain (q.choose r) D p +
      nibbleDegreeError (q.choose r) a D p) ∧
      _ - (nibbleDegreeMain (q.choose r) D p + nibbleDegreeError (q.choose r) a D p) ≤ 0 at hc
    exact hupper he hR hd hh (by linarith only [hc.1]) (by linarith only [hc.2])
  · intro hc
    change 0 ≤ frozenEdgeProcess H e cl i ω ∧
      frozenEdgeProcess H e cl i ω ≤ a ^ 2 * D at hc
    rw [hlval] at hc
    change 0 ≤ _ - (nibbleDegreeMain (q.choose r) D p - nibbleDegreeError (q.choose r) a D p) ∧
      _ - (nibbleDegreeMain (q.choose r) D p - nibbleDegreeError (q.choose r) a D p) ≤
        a ^ 2 * D at hc
    exact hlower he hR hd hh (by linarith only [hc.1]) (by linarith only [hc.2])

end Arxiv2411_18291.CliqueRemovalProcess

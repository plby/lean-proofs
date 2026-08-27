import Arxiv.Arxiv2411_18291.NibbleTrackedBoundedness

/-! # Conditional variance rates and finite-horizon budgets before the first failure -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
variable (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
variable (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)

include hqr hHG P Q hd

theorem nibbleGood_tracked_condVar_le (t : NibbleTrack V r) (i : ℕ)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ nibbleGood G H a D i →
      Var[nibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω ≤
        nibbleVarianceRate q G D t := by
  let k := q.choose (r + 1)
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  rcases t with b | (⟨e, b⟩ | f)
  · have hv := conditional_variance_le_sq_bound (Filtration.piLE.le i)
      ((nibbleTrackedIncrement_stronglyMeasurable G H a D (.inl b) i).mono
        (Filtration.piLE.le (i + 1)))
      (ae_of_all (probability (r + 1) H) fun ω =>
        nibbleTrackedIncrement_abs_bound hqr G H P Q hd (.inl b) i hi ω)
    exact hv.mono fun _ h _ => h
  · by_cases heG : e ∈ G
    case neg =>
      rw [nibbleTrackedIncrement_nonedge G H a D e b i heG, condVar_zero]
      exact ae_of_all _ fun _ _ => nibbleVarianceRate_nonneg q G P.degree_pos.le _
    rw [nibbleTrackedIncrement_edge G H a D e b i heG]
    cases b
    · let cl := nibbleDegreeLowerComparison k a (G.card : ℝ) D
      filter_upwards [nibbleGood_edge_condVar_le G H P hqr hHG e heG cl i hp
        (P.degree_lower_steps i hi).1,
        condVar_neg (μ := probability (r + 1) H) (m := Filtration.piLE i)
          (edgeIncrement H e cl i)] with ω hv hn
      intro hgood
      change Var[fun ω => -edgeIncrement H e cl i ω;
        probability (r + 1) H | Filtration.piLE i] ω =
          Var[edgeIncrement H e cl i; probability (r + 1) H | Filtration.piLE i] ω at hn
      change Var[fun ω => -edgeIncrement H e cl i ω;
        probability (r + 1) H | Filtration.piLE i] ω ≤ _
      rw [hn]
      exact hv hgood
    · exact nibbleGood_edge_condVar_le G H P hqr hHG e heG _ i hp
        (P.degree_upper_steps i hi).1
  · filter_upwards [nibbleFaceCount_condVar_le G H hHG f P i hp,
      trajectory_support_ae (r := r + 1) H] with ω hv hsupp
    intro hgood
    have hdeg := nibbleGood_remaining_degree_bounds P hp hgood hsupp
    exact hv (nibbleGood_clique_deviation hgood) (fun e he => (hdeg e he).2)
      (hgood (.inr (.inr f))).le

theorem nibbleGood_variance_budget (t : NibbleTrack V r) (N : ℕ)
    (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N) :
    ∀ᵐ ω ∂probability (r + 1) H, ∀ j ≤ N, (∀ i < j, ω ∈ nibbleGood G H a D i) →
      (∑ i ∈ range j,
        Var[nibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω) ≤
          (N : ℝ) * nibbleVarianceRate q G D t := by
  have hb : ∀ i, ∀ᵐ ω ∂probability (r + 1) H, i < N → ω ∈ nibbleGood G H a D i →
      Var[nibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω ≤
        nibbleVarianceRate q G D t := by
    intro i
    by_cases hi : i < N
    · have hnext : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1) :=
        hfloor.trans (removalDensity_antitone _ P.graph_pos (by omega))
      exact (nibbleGood_tracked_condVar_le hqr G H hHG P Q hd t i hnext).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => (hi h).elim
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  intro j hj hgood
  calc
    _ ≤ ∑ _i ∈ range j, nibbleVarianceRate q G D t := by
      apply sum_le_sum
      intro i hi
      exact hω i ((mem_range.mp hi).trans_le hj) (hgood i (mem_range.mp hi))
    _ = (j : ℝ) * nibbleVarianceRate q G D t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj)
      (nibbleVarianceRate_nonneg q G P.degree_pos.le t)

end Arxiv2411_18291.CliqueRemovalProcess

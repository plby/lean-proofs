import Arxiv.Arxiv2411_18291.LogNibbleTrackedBoundedness

/-! # Conditional variance rates and finite-horizon budgets before the first logarithmic failure -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
variable (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
variable (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)

include hqr hHG P hd

theorem logNibbleGood_tracked_condVar_le (t : NibbleTrack V r) (i : ℕ)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1)) :
    ∀ᵐ ω ∂probability (r + 1) H, ω ∈ logNibbleGood G H a D i →
      Var[logNibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω ≤
        nibbleVarianceRate q G D t := by
  let k := q.choose (r + 1)
  have hp := (P.consecutive_bounds hi (removalDensity_difference k (G.card : ℝ) i)).2.2.2
  rcases t with b | (⟨e, b⟩ | f)
  · have hv := conditional_variance_le_sq_bound (Filtration.piLE.le i)
      ((logNibbleTrackedIncrement_stronglyMeasurable G H a D (.inl b) i).mono
        (Filtration.piLE.le (i + 1)))
      (ae_of_all (probability (r + 1) H) fun ω =>
        logNibbleTrackedIncrement_abs_bound hqr G H P hd (.inl b) i hi ω)
    exact hv.mono fun _ h _ => h
  · by_cases heG : e ∈ G
    case neg =>
      rw [logNibbleTrackedIncrement_nonedge G H a D e b i heG, condVar_zero]
      exact ae_of_all _ fun _ _ => nibbleVarianceRate_nonneg q G P.degree_pos.le _
    rw [logNibbleTrackedIncrement_edge G H a D e b i heG]
    cases b
    · let cl := logNibbleDegreeLowerComparison k a (G.card : ℝ) D
      filter_upwards [logNibbleGood_edge_condVar_le G H P hqr hHG e heG cl i hp
        (P.degree_step_abs i hi).2,
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
    · exact logNibbleGood_edge_condVar_le G H P hqr hHG e heG _ i hp
        (P.degree_step_abs i hi).1
  · filter_upwards [logNibbleFaceCount_condVar_le G H hHG f P i hp,
      trajectory_support_ae (r := r + 1) H] with ω hv hsupp
    intro hgood
    have hdeg := logNibbleGood_remaining_degree_bounds P hp hgood hsupp
    have hface := hv (logNibbleGood_clique_deviation hgood) (fun e he => (hdeg e he).2)
      (hgood (.inr (.inr f))).le
    apply hface.trans
    change 12 * ((q - r : ℕ) : ℝ) * k * Fintype.card V / G.card ≤
      4 * ((q - r : ℕ) : ℝ) * (1 + 128 * (k : ℝ)) * k * Fintype.card V / G.card
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
    have hc : (3 : ℝ) ≤ 1 + 128 * (k : ℝ) := by linarith only [hkR]
    have hh := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ 4 * ((q - r : ℕ) : ℝ) * k * Fintype.card V / (G.card : ℝ) by positivity)
    convert! hh using 1 <;> ring

theorem logNibbleGood_variance_budget (t : NibbleTrack V r) (N : ℕ)
    (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N) :
    ∀ᵐ ω ∂probability (r + 1) H, ∀ j ≤ N, (∀ i < j, ω ∈ logNibbleGood G H a D i) →
      (∑ i ∈ range j,
        Var[logNibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω) ≤
          (N : ℝ) * nibbleVarianceRate q G D t := by
  have hb : ∀ i, ∀ᵐ ω ∂probability (r + 1) H, i < N → ω ∈ logNibbleGood G H a D i →
      Var[logNibbleTrackedIncrement G H a D t i; probability (r + 1) H | Filtration.piLE i] ω ≤
        nibbleVarianceRate q G D t := by
    intro i
    by_cases hi : i < N
    · have hnext : p₀ ≤ removalDensity (q.choose (r + 1)) G.card (i + 1) :=
        hfloor.trans (removalDensity_antitone _ P.graph_pos (by omega))
      exact (logNibbleGood_tracked_condVar_le hqr G H hHG P hd t i hnext).mono fun _ h _ => h
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

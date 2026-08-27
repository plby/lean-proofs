import Arxiv.Arxiv2411_18291.WeightedGreedyConcentration
import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-! # Actual greedy families with bounded weighted face degrees

A finite tail bound below one supplies a path in all transition supports.
Positive weights control ordinary degrees along every prefix, so legal
choices remain available and the path supplies actual embeddings.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r t : ℕ}

structure IsWeightedGreedyFamily (Φ : Fin t → F ↪ V) (w : Fin t → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (Ψ : (i : Fin t) → EmbeddingExtension (Φ i)) (L : ℝ) : Prop where
  greedy : IsGreedyFamily Φ H B Ψ L
  weighted : ∀ e ∈ newEdges F H,
    IsWeightedFamilyBounded r (fun i => mapBlock (Ψ i).val e) w L

omit [Fintype W] in
theorem weightedHistoryGood_prefix_mono (w : ℕ → ℕ) (H : Hypergraph W (r + 1))
    (F : Finset W) (L : ℝ) (ω : ℕ → EmbeddingState W V) {s t : ℕ} (hst : s ≤ t)
    (ht : weightedHistoryGood w H F L (frestrictLe t ω)) :
    weightedHistoryGood w H F L (frestrictLe s ω) := by
  intro e he S
  rw [weightedHistoryDegree_prefix]
  have hmono : (weightedTrajectoryDegree w ω s e S.val : ℝ) ≤
      weightedTrajectoryDegree w ω t e S.val := by
    exact_mod_cast weightedTrajectoryDegree_mono w ω hst e S.val
  exact hmono.trans_lt (by simpa only [weightedHistoryDegree_prefix] using ht e he S)

theorem weightedGreedyStep_choose_of_good (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ L : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4) (n : ℕ)
    (hw : ∀ j < n, 1 ≤ w j) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hsuccess : historySuccessful h) (hgood : weightedHistoryGood w H F L h)
    (a : EmbeddingState W V) (ha : a ∈ (weightedGreedyStep Φ w H B L n h).support) :
    ∃ f : EmbeddingExtension (Φ n), a = some f.val ∧
      f ∈ legalExtensions (Φ n) H (historyForbidden H B F h) := by
  classical
  rw [weightedGreedyStep, if_pos hgood] at ha
  exact greedyStep_choose_of_good Φ H B hB hθ hL hn hnpos hsmall n h hsuccess
    (hgood.unweighted w H hw) a ha

theorem weighted_greedy_steps_of_final_good (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ L : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (ω : ℕ → EmbeddingState W V) (t : ℕ) (hw : ∀ j < t, 1 ≤ w j)
    (hsupport : ∀ n, ω (n + 1) ∈ (weightedGreedyStep Φ w H B L n (frestrictLe n ω)).support)
    (hgood : weightedHistoryGood w H F L (frestrictLe t ω)) :
    ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)) := by
  have hsuccessful : ∀ n ≤ t, historySuccessful (frestrictLe n ω) := by
    intro n
    induction n with
    | zero => intro _ j hj; omega
    | succ n ih =>
      intro hnt
      have hprev := ih (by omega)
      obtain ⟨f, hω, _⟩ := weightedGreedyStep_choose_of_good Φ w H B hB hθ hL hn hnpos
        hsmall n (fun j hj => hw j (by omega)) (frestrictLe n ω) hprev
        (weightedHistoryGood_prefix_mono w H F L ω (by omega) hgood) _ (hsupport n)
      intro j hj
      rw [historyAt_prefix ω (n + 1) j hj]
      by_cases hjn : j < n
      · simpa only [historyAt_prefix ω n j hjn] using hprev j hjn
      · have hje : j = n := by omega
        subst j
        rw [hω]
        exact Option.some_ne_none _
  intro i hi
  exact weightedGreedyStep_choose_of_good Φ w H B hB hθ hL hn hnpos hsmall i
    (fun j hj => hw j (by omega)) (frestrictLe i ω) (hsuccessful i hi.le)
    (weightedHistoryGood_prefix_mono w H F L ω hi.le hgood) _ (hsupport i)

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem weightedFamilyDegree_eq_trajectoryDegree (w : ℕ → ℕ) (Ψ : Fin t → W ↪ V)
    (ω : ℕ → EmbeddingState W V) (hω : ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i))
    (e : Block W r) (S : Finset V) :
    weightedFamilyDegree (fun i => mapBlock (Ψ i) e) (fun i => w i) S =
      weightedTrajectoryDegree w ω t e S := by
  calc
    _ = ∑ i : Fin t, w i * edgeIncidence (stateEdge (ω (i + 1)) e) S := by
      apply sum_congr rfl
      intro i _
      rw [hω i]
      change (if S ⊆ (mapBlock (Ψ i) e).val then w i else 0) =
        w i * (if S ⊆ (mapBlock (Ψ i) e).val then 1 else 0)
      split_ifs <;> simp only [mul_one, mul_zero]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i => w i * edgeIncidence (stateEdge (ω (i + 1)) e) S) t

theorem extract_weighted_greedy_family (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ)
    (ω : ℕ → EmbeddingState W V) (t : ℕ) (hw : ∀ j < t, 1 ≤ w j)
    (hsteps : ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)))
    (hgood : weightedHistoryGood w H F L (frestrictLe t ω)) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsWeightedGreedyFamily (fun i => Φ i) (fun i => w i) H B Ψ L := by
  obtain ⟨Ψ, hΨ⟩ := Classical.axiomOfChoice (fun i : Fin t => hsteps i i.isLt)
  refine ⟨Ψ, isGreedyFamily_of_legal Φ H B L ω t Ψ (fun i => (hΨ i).1)
    (fun i => (hΨ i).2) (hgood.unweighted w H hw), ?_⟩
  intro e he S
  rw [weightedFamilyDegree_eq_trajectoryDegree w (fun i => (Ψ i).val) ω
    (fun i => (hΨ i).1)]
  simpa only [weightedHistoryDegree_prefix] using hgood e he S

theorem exists_weighted_greedy_family (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB θR C c : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hθR : 0 ≤ θR)
    (hC : 0 < C) (hc : 0 < c)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * ((1 + c) * (2 * (r + 1).factorial * θR))) ≤ 1 / 4)
    (t : ℕ) (hw : ∀ i < t, 1 ≤ w i) (hCw : ∀ i < t, (w i : ℝ) ≤ C)
    (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsWeightedFamilyBounded r (fun i : Fin t => rootImage (Φ i) f hf) (fun i => w i) θR)
    (hfailure : H.card * Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * θR * Fintype.card V * c ^ 2 / ((2 + c) * C))) < 1) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsWeightedGreedyFamily (fun i => Φ i) (fun i => w i) H B Ψ
        ((1 + c) * (2 * (r + 1).factorial * θR)) := by
  classical
  let L : ℝ := (1 + c) * (2 * (r + 1).factorial * θR)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let P := weightedGreedyProbability Φ w H B L
  have hsupport : ∀ᵐ ω : ℕ → EmbeddingState W V ∂P, ∀ n,
      ω (n + 1) ∈ (weightedGreedyStep Φ w H B L n (frestrictLe n ω)).support :=
    ae_all_iff.mpr fun n => FiniteHistoryProcess.next_mem_support
      (abortedEmbedding W V) (weightedGreedyStep Φ w H B L) n
  have hbadlt : P.real {ω | ¬ weightedHistoryGood w H F L (frestrictLe t ω)} < 1 := by
    have hevent : {ω | ¬ weightedHistoryGood w H F L (frestrictLe t ω)} =
        {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
          (1 + c) * (2 * (r + 1).factorial * θR * Fintype.card V) ≤
            (weightedTrajectoryDegree w ω t e S.val : ℝ)} := by
      ext ω
      simp only [weightedHistoryGood, not_forall, not_lt, weightedHistoryDegree_prefix,
        L, mul_assoc, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
    rw [hevent]
    exact (weightedGreedy_all_degrees_failure Φ w H B hB hθB hθR hL hC hc hn hnpos
      hsmall t hCw hA hroots).trans_lt hfailure
  obtain ⟨ω, hωsupport, hωgood⟩ : ∃ ω : ℕ → EmbeddingState W V, (∀ n,
      ω (n + 1) ∈ (weightedGreedyStep Φ w H B L n (frestrictLe n ω)).support) ∧
      weightedHistoryGood w H F L (frestrictLe t ω) := by
    by_contra hex
    have hbad : ∀ᵐ ω ∂P, ¬ weightedHistoryGood w H F L (frestrictLe t ω) := by
      filter_upwards [hsupport] with ω hω
      exact fun hg => hex ⟨ω, hω, hg⟩
    have heq : {ω | ¬ weightedHistoryGood w H F L (frestrictLe t ω)} =ᵐ[P] Set.univ := by
      filter_upwards [hbad] with ω hω
      exact propext ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
    have hone : P.real {ω | ¬ weightedHistoryGood w H F L (frestrictLe t ω)} = 1 :=
      (measureReal_congr heq).trans probReal_univ
    linarith
  exact extract_weighted_greedy_family Φ w H B L ω t hw
    (weighted_greedy_steps_of_final_good Φ w H B hB hθB hL hn hnpos hsmall
      ω t hw hωsupport hωgood) hωgood

end Arxiv2411_18291

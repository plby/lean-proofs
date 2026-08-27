import Arxiv.Arxiv2411_18291.GreedyDegreeConcentration

/-!
# Success of paths whose final degrees stay below the cap

Degree counts are monotone along a trajectory. If every final degree is
below the stopping cap, then every earlier history is good. The available
choice bound rules out aborts, and the support of the actual transition
measure supplies a legal root-preserving embedding at each step.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

omit [Fintype W] in
theorem historyGood_prefix_mono (H : Hypergraph W (r + 1)) (F : Finset W) (L : ℝ)
    (ω : ℕ → EmbeddingState W V) {s t : ℕ} (hst : s ≤ t)
    (ht : historyGood H F L (frestrictLe t ω)) : historyGood H F L (frestrictLe s ω) := by
  intro e he S
  rw [historyDegree_prefix]
  have hmono : (trajectoryDegree ω s e S.val : ℝ) ≤ trajectoryDegree ω t e S.val := by
    exact_mod_cast trajectoryDegree_mono ω hst e S.val
  exact hmono.trans_lt (by simpa only [historyDegree_prefix] using ht e he S)

theorem greedyStep_choose_of_good (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (n : ℕ) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hsuccess : historySuccessful h) (hgood : historyGood H F L h)
    (a : EmbeddingState W V) (ha : a ∈ (greedyStep Φ H B L n h).support) :
    ∃ f : EmbeddingExtension (Φ n), a = some f.val ∧
      f ∈ legalExtensions (Φ n) H (historyForbidden H B F h) := by
  classical
  have hs := legalExtensions_nonempty (Φ n) H (historyForbidden H B F h)
    (historyForbidden_bounded H B h hB hL hgood) (by positivity) hn hsmall hnpos
  unfold greedyStep at ha
  rw [if_pos ⟨hsuccess, hgood⟩, dif_pos hs] at ha
  obtain ⟨f, hf, hfa⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  refine ⟨f, hfa.symm, ?_⟩
  simpa only [uniformLegalExtension, PMF.support_uniformOfFinset, Finset.mem_coe] using hf

/-- No path in the transition supports can abort while its final degrees are good. -/
theorem greedy_steps_of_final_good (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (ω : ℕ → EmbeddingState W V) (t : ℕ)
    (hsupport : ∀ n, ω (n + 1) ∈ (greedyStep Φ H B L n (frestrictLe n ω)).support)
    (hgood : historyGood H F L (frestrictLe t ω)) :
    ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)) := by
  have hsuccessful : ∀ n ≤ t, historySuccessful (frestrictLe n ω) := by
    intro n
    induction n with
    | zero => intro _ j hj; omega
    | succ n ih =>
      intro hnt
      have hprev := ih (by omega)
      obtain ⟨f, hω, _⟩ := greedyStep_choose_of_good Φ H B hB hθ hL hn hnpos hsmall n
        (frestrictLe n ω) hprev (historyGood_prefix_mono H F L ω (by omega) hgood) _ (hsupport n)
      intro j hj
      rw [historyAt_prefix ω (n + 1) j hj]
      by_cases hjn : j < n
      · simpa only [historyAt_prefix ω n j hjn] using hprev j hjn
      · have hje : j = n := by omega
        subst j
        rw [hω]
        exact Option.some_ne_none _
  intro i hi
  exact greedyStep_choose_of_good Φ H B hB hθ hL hn hnpos hsmall i (frestrictLe i ω)
    (hsuccessful i hi.le) (historyGood_prefix_mono H F L ω hi.le hgood) _ (hsupport i)

omit [Fintype W] [Fintype V] in
theorem previous_edge_mem_historyForbidden (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (ω : ℕ → EmbeddingState W V) {i j : ℕ} (hij : i < j)
    (a : W ↪ V) (ha : ω (i + 1) = some a) (e : Block W (r + 1)) (he : e ∈ newEdges F H) :
    mapBlock a e ∈ historyForbidden H B F (frestrictLe j ω) := by
  apply mem_union.mpr
  right
  apply mem_biUnion.mpr
  refine ⟨e, he, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨i, mem_range.mpr hij, ?_⟩
  simp only [historyAt_prefix ω j i hij, ha, stateEdge, Option.map_some,
    Option.toFinset_some, mem_singleton]

end Arxiv2411_18291

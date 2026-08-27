import Arxiv.Arxiv2411_18291.UnstoppedGreedyProcess

/-! # Certain success from deterministic availability and degree bounds -/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem greedyStep_choose_of_available (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (i : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) i)
    (hsuccess : historySuccessful h) (hgood : historyGood H F L h)
    (hlegal : (legalExtensions (Φ i) H (historyForbidden H B F h)).Nonempty)
    (a : EmbeddingState W V) (ha : a ∈ (greedyStep Φ H B L i h).support) :
    ∃ f : EmbeddingExtension (Φ i), a = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F h) := by
  classical
  unfold greedyStep at ha
  rw [if_pos ⟨hsuccess, hgood⟩, dif_pos hlegal] at ha
  obtain ⟨f, hf, hfa⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  refine ⟨f, hfa.symm, ?_⟩
  simpa only [uniformLegalExtension, PMF.support_uniformOfFinset, Finset.mem_coe] using hf

theorem greedy_steps_of_available (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (ω : ℕ → EmbeddingState W V) (t : ℕ)
    (hsupport : ∀ i, ω (i + 1) ∈ (greedyStep Φ H B L i (frestrictLe i ω)).support)
    (hgood : historyGood H F L (frestrictLe t ω))
    (hlegal : ∀ i < t, ∀ h : FiniteHistoryProcess.History (EmbeddingState W V) i,
      (legalExtensions (Φ i) H (historyForbidden H B F h)).Nonempty) :
    ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)) := by
  have hsuccessful : ∀ i ≤ t, historySuccessful (frestrictLe i ω) := by
    intro i
    induction i with
    | zero => intro _ j hj; omega
    | succ i ih =>
      intro hit
      have hprev := ih (by omega)
      obtain ⟨f, hω, _⟩ := greedyStep_choose_of_available Φ H B L i
        (frestrictLe i ω) hprev (historyGood_prefix_mono H F L ω (by omega) hgood)
        (hlegal i (by omega) _) _ (hsupport i)
      intro j hj
      rw [historyAt_prefix ω (i + 1) j hj]
      by_cases hji : j < i
      · simpa only [historyAt_prefix ω i j hji] using hprev j hji
      · have hje : j = i := by omega
        subst j
        rw [hω]
        exact Option.some_ne_none _
  intro i hi
  exact greedyStep_choose_of_available Φ H B L i (frestrictLe i ω)
    (hsuccessful i hi.le) (historyGood_prefix_mono H F L ω hi.le hgood)
    (hlegal i hi _) _ (hsupport i)

theorem unstopped_greedy_probability_one_of_available
    (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (L : ℝ) (t : ℕ)
    (hgood : ∀ ω : ℕ → EmbeddingState W V, historyGood H F L (frestrictLe t ω))
    (hlegal : ∀ i < t, ∀ h : FiniteHistoryProcess.History (EmbeddingState W V) i,
      (legalExtensions (Φ i) H (historyForbidden H B F h)).Nonempty) :
    (unstoppedGreedyProbability Φ H B).real (greedyFamilyEvent Φ H B L t) = 1 := by
  rw [unstopped_greedy_family_probability_eq]
  let P := greedyProbability Φ H B L
  have hs : ∀ᵐ ω : ℕ → EmbeddingState W V ∂P, ∀ i,
      ω (i + 1) ∈ (greedyStep Φ H B L i (frestrictLe i ω)).support :=
    ae_all_iff.mpr fun i => FiniteHistoryProcess.next_mem_support
      (abortedEmbedding W V) (greedyStep Φ H B L) i
  have hevent : ∀ᵐ ω ∂P, ω ∈ greedyFamilyEvent Φ H B L t := by
    filter_upwards [hs] with ω hω
    have hsteps := greedy_steps_of_available Φ H B L ω t hω (hgood ω) hlegal
    obtain ⟨Ψ, hΨ⟩ := Classical.axiomOfChoice (fun i : Fin t => hsteps i i.isLt)
    exact ⟨Ψ, isGreedyFamily_of_legal Φ H B L ω t Ψ (fun i => (hΨ i).1)
      (fun i => (hΨ i).2) (hgood ω), fun i => (hΨ i).1⟩
  have heq : greedyFamilyEvent Φ H B L t =ᵐ[P] Set.univ := by
    filter_upwards [hevent] with ω hω
    exact propext ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
  exact (measureReal_congr heq).trans probReal_univ

end Arxiv2411_18291

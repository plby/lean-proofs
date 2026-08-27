import Arxiv.Arxiv2411_18291.PrescribedGreedyProcess
import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-!
# Successful paths with prescribed candidates

The candidate lower bound prevents abort at every good history. Final degree
control implies all earlier histories were good, so a supported trajectory
supplies a legal candidate at each step. The extracted family retains both
its candidate membership and the disjointness and boundedness properties.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem prescribed_steps_of_final_good (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hL : 0 ≤ L) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θB + H.card * L) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H L η t) (ω : ℕ → EmbeddingState W V)
    (hsupport : ∀ n, ω (n + 1) ∈ (prescribedGreedyStep Φ A H B L n (frestrictLe n ω)).support)
    (hgood : historyGood H F L (frestrictLe t ω)) :
    ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = chosenEmbedding f.val ∧
      f ∈ A i (frestrictLe i ω) ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)) := by
  have hsuccessful : ∀ n ≤ t, historySuccessful (frestrictLe n ω) := by
    intro n
    induction n with
    | zero => intro _ j hj; omega
    | succ n ih =>
      intro hnt
      have hprev := ih (by omega)
      have hgoodn := historyGood_prefix_mono H F L ω (show n ≤ t by omega) hgood
      obtain ⟨f, hω, _, _⟩ := prescribedGreedyStep_choose_of_good Φ A H B hB hθB hL hη
        hnpos hsmall n (frestrictLe n ω) hprev hgoodn
        (hA n (by omega) _ hprev hgoodn) _ (hsupport n)
      intro j hj
      rw [historyAt_prefix ω (n + 1) j hj]
      by_cases hjn : j < n
      · simpa only [historyAt_prefix ω n j hjn] using hprev j hjn
      · have hje : j = n := by omega
        subst j
        rw [hω]
        exact Option.some_ne_none _
  intro i hi
  have his := hsuccessful i hi.le
  have hig := historyGood_prefix_mono H F L ω hi.le hgood
  exact prescribedGreedyStep_choose_of_good Φ A H B hB hθB hL hη hnpos hsmall i
    (frestrictLe i ω) his hig (hA i hi _ his hig) _ (hsupport i)

theorem extract_prescribed_greedy_family (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ)
    (ω : ℕ → EmbeddingState W V) (t : ℕ)
    (hsteps : ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = chosenEmbedding f.val ∧
      f ∈ A i (frestrictLe i ω) ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)))
    (hgood : historyGood H F L (frestrictLe t ω)) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ L ∧
      (∀ i : Fin t, Ψ i ∈ A i (frestrictLe (i : ℕ) ω)) ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val := by
  obtain ⟨Ψ, hΨ⟩ := Classical.axiomOfChoice (fun i : Fin t => hsteps i i.isLt)
  exact ⟨Ψ, isGreedyFamily_of_legal Φ H B L ω t Ψ (fun i => (hΨ i).1)
    (fun i => (hΨ i).2.2) hgood, (fun i => (hΨ i).2.1), fun i => (hΨ i).1⟩

end Arxiv2411_18291

import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-! # Probability that the actual trajectory realizes a bounded greedy family -/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

def greedyFamilyEvent (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) : Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
    IsGreedyFamily (fun i => Φ i) H B Ψ L ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

def allEdgesGreedyFamilyEvent (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) : Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
    IsGreedyFamily (fun i => Φ i) H B Ψ L ∧
      (∀ e ∈ H, IsEdgeFamilyBounded (fun i => mapBlock (Ψ i).val e) L) ∧
        ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

omit [Fintype W] in
theorem greedyFamilyEvent_mono (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (t : ℕ) {L L' : ℝ} (hL : L ≤ L') :
    greedyFamilyEvent Φ H B L t ⊆ greedyFamilyEvent Φ H B L' t := by
  rintro ω ⟨Ψ, hΨ, hmatch⟩
  refine ⟨Ψ, ⟨hΨ.avoids, hΨ.disjoint, ?_⟩, hmatch⟩
  intro e he S
  exact (hΨ.bounded e he S).trans_le (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg _))

omit [Fintype W] in
theorem allEdgesGreedyFamilyEvent_eq (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (t : ℕ) {θ L : ℝ} (hθL : θ ≤ L)
    (hroots : ∀ e ∈ H, ∀ he : e.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) e he) θ) :
    allEdgesGreedyFamilyEvent Φ H B L t = greedyFamilyEvent Φ H B L t := by
  ext ω
  constructor
  · rintro ⟨Ψ, hΨ, _, hmatch⟩
    exact ⟨Ψ, hΨ, hmatch⟩
  · rintro ⟨Ψ, hΨ, hmatch⟩
    exact ⟨Ψ, hΨ, hΨ.all_edges_bounded hroots hθL, hmatch⟩

omit [Fintype W] in
theorem measurableSet_greedyFamilyEvent [Finite W]
    (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    MeasurableSet (greedyFamilyEvent Φ H B L t) := by
  classical
  let : Fintype W := Fintype.ofFinite W
  unfold greedyFamilyEvent
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro Ψ
  apply MeasurableSet.inter
  · by_cases h : IsGreedyFamily (fun i => Φ i) H B Ψ L <;> simp [h]
  · apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))

theorem greedy_family_failure_probability (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * (4 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    (greedyProbability Φ H B (4 * (r + 1).factorial * θ)).real
        (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t)ᶜ ≤
      H.card * Fintype.card (Block V r) *
        Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) := by
  classical
  let L : ℝ := 4 * (r + 1).factorial * θ
  let P := greedyProbability Φ H B L
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hsupport : ∀ᵐ ω : ℕ → EmbeddingState W V ∂P, ∀ n,
      ω (n + 1) ∈ (greedyStep Φ H B L n (frestrictLe n ω)).support :=
    ae_all_iff.mpr fun n => FiniteHistoryProcess.next_mem_support
      (abortedEmbedding W V) (greedyStep Φ H B L) n
  have hsub : (greedyFamilyEvent Φ H B L t)ᶜ ≤ᵐ[P]
      {ω | ¬ historyGood H F L (frestrictLe t ω)} := by
    filter_upwards [hsupport] with ω hω
    intro hbad hgood
    have hsteps := greedy_steps_of_final_good Φ H B hB hθ hL hn hnpos hsmall
      ω t hω hgood
    obtain ⟨Ψ, hΨ⟩ := Classical.axiomOfChoice (fun i : Fin t => hsteps i i.isLt)
    apply hbad
    exact ⟨Ψ, isGreedyFamily_of_legal Φ H B L ω t Ψ (fun i => (hΨ i).1)
      (fun i => (hΨ i).2) hgood, fun i => (hΨ i).1⟩
  have hevent : {ω | ¬ historyGood H F L (frestrictLe t ω)} =
      {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
        4 * (r + 1).factorial * θ * Fintype.card V ≤
          (trajectoryDegree ω t e S.val : ℝ)} := by
    ext ω
    simp only [historyGood, not_forall, not_lt, historyDegree_prefix, L,
      Set.mem_ofPred_eq]
    constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
  have hmono : P.real (greedyFamilyEvent Φ H B L t)ᶜ ≤
      P.real {ω | ¬ historyGood H F L (frestrictLe t ω)} :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  rw [hevent] at hmono
  exact hmono.trans (greedy_all_degrees_failure Φ H B hB hθ hL hn hnpos hsmall t hA hroots)

theorem greedy_family_success_probability (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * (4 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - H.card * Fintype.card (Block V r) *
        Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) ≤
      (greedyProbability Φ H B (4 * (r + 1).factorial * θ)).real
        (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  have hf := greedy_family_failure_probability Φ H B hB hθ hn hnpos hsmall t hA hroots
  rw [measureReal_compl (measurableSet_greedyFamilyEvent Φ H B _ t), probReal_univ] at hf
  linarith only [hf]

end Arxiv2411_18291

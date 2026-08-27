import Arxiv.Arxiv2411_18291.GreedySuccess

/-!
# Existence of a successful bounded family of greedy extensions

A probability bound strictly below one supplies a trajectory that respects
all transition supports and stays below every degree cap. Extracting its
embeddings gives disjoint new edge sets, avoidance of the forbidden graph,
and bounded output families, with no probabilistic construction assumed.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r t : ℕ}

structure IsGreedyFamily (Φ : Fin t → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (Ψ : (i : Fin t) → EmbeddingExtension (Φ i)) (L : ℝ) : Prop where
  avoids : ∀ i, Disjoint (mapGraph (Ψ i).val (newEdges F H)) B
  disjoint : Pairwise fun i j =>
    Disjoint (mapGraph (Ψ i).val (newEdges F H)) (mapGraph (Ψ j).val (newEdges F H))
  bounded : ∀ e ∈ newEdges F H, IsEdgeFamilyBounded (fun i => mapBlock (Ψ i).val e) L

omit [Fintype W] in
theorem IsGreedyFamily.all_edges_bounded {Φ : Fin t → F ↪ V} {H : Hypergraph W (r + 1)}
    {B : Hypergraph V (r + 1)} {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L θ : ℝ}
    (hΨ : IsGreedyFamily Φ H B Ψ L)
    (hroots : ∀ e ∈ H, ∀ he : e.val ⊆ F, IsEdgeFamilyBounded (fun i => rootImage (Φ i) e he) θ)
    (hθL : θ ≤ L) : ∀ e ∈ H, IsEdgeFamilyBounded (fun i => mapBlock (Ψ i).val e) L := by
  intro e he
  by_cases heF : e.val ⊆ F
  · have heq : (fun i => mapBlock (Ψ i).val e) = (fun i => rootImage (Φ i) e heF) :=
      funext fun i => EmbeddingExtension.map_rootBlock (Φ i) (Ψ i) e heF
    rw [heq]
    intro S
    exact (hroots e he heF S).trans_le (mul_le_mul_of_nonneg_right hθL (Nat.cast_nonneg _))
  · exact hΨ.bounded e ((mem_newEdges H e).mpr ⟨he, heF⟩)

theorem legalExtension_disjoint (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (a : EmbeddingExtension φ) (ha : a ∈ legalExtensions φ H B) :
    Disjoint (mapGraph a.val (newEdges F H)) B := by
  apply disjoint_left.mpr
  intro g hga hgB
  obtain ⟨e, he, heg⟩ := (mem_mapGraph a.val (newEdges F H) g).mp hga
  have hnot := (mem_legalExtensions φ H B a).mp ha e
    ((mem_newEdges H e).mp he).1 ((mem_newEdges H e).mp he).2
  exact hnot (heg.symm ▸ hgB)

theorem legal_extension_disjoint_previous (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (ω : ℕ → EmbeddingState W V) {i j : ℕ} (hij : i < j)
    (a : W ↪ V) (ha : ω (i + 1) = chosenEmbedding a) (φ : F ↪ V) (b : EmbeddingExtension φ)
    (hb : b ∈ legalExtensions φ H (historyForbidden H B F (frestrictLe j ω))) :
    Disjoint (mapGraph a (newEdges F H)) (mapGraph b.val (newEdges F H)) := by
  apply disjoint_left.mpr
  intro g hga hgb
  obtain ⟨e, he, heg⟩ := (mem_mapGraph a (newEdges F H) g).mp hga
  obtain ⟨f, hf, hfg⟩ := (mem_mapGraph b.val (newEdges F H) g).mp hgb
  have hforbid := previous_edge_mem_historyForbidden H B ω hij a ha e he
  have hnot := (mem_legalExtensions φ H (historyForbidden H B F (frestrictLe j ω)) b).mp hb f
    ((mem_newEdges H f).mp hf).1 ((mem_newEdges H f).mp hf).2
  apply hnot
  rw [hfg, ← heg]
  exact hforbid

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem familyDegree_eq_trajectoryDegree (Ψ : Fin t → W ↪ V) (ω : ℕ → EmbeddingState W V)
    (hω : ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i)) (e : Block W r) (S : Finset V) :
    familyDegree (fun i => mapBlock (Ψ i) e) S = trajectoryDegree ω t e S := by
  calc
    _ = ∑ i : Fin t, if S ⊆ (mapBlock (Ψ i) e).val then 1 else 0 := by
      simp only [familyDegree, card_eq_sum_ones, sum_filter]
    _ = ∑ i : Fin t, edgeIncidence (stateEdge (ω (i + 1)) e) S := by
      apply sum_congr rfl
      intro i _
      rw [hω i]
      rfl
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => edgeIncidence (stateEdge (ω (i + 1)) e) S) t

theorem isGreedyFamily_of_legal (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (ω : ℕ → EmbeddingState W V) (t : ℕ)
    (Ψ : (i : Fin t) → EmbeddingExtension (Φ i))
    (hmatch : ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val)
    (hlegal : ∀ i : Fin t,
      Ψ i ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe (i : ℕ) ω)))
    (hgood : historyGood H F L (frestrictLe t ω)) :
    IsGreedyFamily (fun i => Φ i) H B Ψ L := by
  have hsep : ∀ i j : Fin t, i < j →
      Disjoint (mapGraph (Ψ i).val (newEdges F H)) (mapGraph (Ψ j).val (newEdges F H)) := by
    intro i j hij
    exact legal_extension_disjoint_previous H B ω hij (Ψ i).val (hmatch i) (Φ j) (Ψ j) (hlegal j)
  constructor
  · intro i
    exact Disjoint.mono_right
      (show B ⊆ historyForbidden H B F (frestrictLe (i : ℕ) ω) from subset_union_left)
      (legalExtension_disjoint (Φ i) H (historyForbidden H B F (frestrictLe (i : ℕ) ω))
        (Ψ i) (hlegal i))
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hsep i j hlt
    · exact (hsep j i hgt).symm
  · intro e he S
    have hd : familyDegree (fun i : Fin t => mapBlock (Ψ i).val e) S.val =
        trajectoryDegree ω t e S.val :=
      familyDegree_eq_trajectoryDegree (fun i => (Ψ i).val) ω hmatch e S.val
    change (familyDegree (fun i : Fin t => mapBlock (Ψ i).val e) S.val : ℝ) < _
    rw [hd]
    simpa only [historyDegree_prefix] using hgood e he S

theorem extract_greedy_family (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (ω : ℕ → EmbeddingState W V) (t : ℕ)
    (hsteps : ∀ i < t, ∃ f : EmbeddingExtension (Φ i), ω (i + 1) = some f.val ∧
      f ∈ legalExtensions (Φ i) H (historyForbidden H B F (frestrictLe i ω)))
    (hgood : historyGood H F L (frestrictLe t ω)) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i), IsGreedyFamily (fun i => Φ i) H B Ψ L := by
  obtain ⟨Ψ, hΨ⟩ := Classical.axiomOfChoice (fun i : Fin t => hsteps i i.isLt)
  exact ⟨Ψ, isGreedyFamily_of_legal Φ H B L ω t Ψ (fun i => (hΨ i).1)
    (fun i => (hΨ i).2) hgood⟩

/-- A finite numerical criterion for successful bounded greedy embeddings. -/
theorem exists_greedy_family (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * (4 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ)
    (hfailure : H.card * Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) < 1) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * θ) := by
  classical
  let L : ℝ := 4 * (r + 1).factorial * θ
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let P := greedyProbability Φ H B L
  have hsupport : ∀ᵐ ω : ℕ → EmbeddingState W V ∂P, ∀ n,
      ω (n + 1) ∈ (greedyStep Φ H B L n (frestrictLe n ω)).support :=
    ae_all_iff.mpr fun n => FiniteHistoryProcess.next_mem_support
      (abortedEmbedding W V) (greedyStep Φ H B L) n
  have hbadlt : P.real {ω | ¬ historyGood H F L (frestrictLe t ω)} < 1 := by
    have hevent : {ω | ¬ historyGood H F L (frestrictLe t ω)} =
        {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
          4 * (r + 1).factorial * θ * Fintype.card V ≤ (trajectoryDegree ω t e S.val : ℝ)} := by
      ext ω
      simp only [historyGood, not_forall, not_lt, historyDegree_prefix, L,
        Set.mem_ofPred_eq]
      constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
    rw [hevent]
    exact (greedy_all_degrees_failure Φ H B hB hθ hL hn hnpos hsmall t hA hroots).trans_lt hfailure
  obtain ⟨ω, hωsupport, hωgood⟩ : ∃ ω : ℕ → EmbeddingState W V, (∀ n,
      ω (n + 1) ∈ (greedyStep Φ H B L n (frestrictLe n ω)).support) ∧
      historyGood H F L (frestrictLe t ω) := by
    by_contra hex
    have hbad : ∀ᵐ ω ∂P, ¬ historyGood H F L (frestrictLe t ω) := by
      filter_upwards [hsupport] with ω hω
      exact fun hg => hex ⟨ω, hω, hg⟩
    have heq : {ω | ¬ historyGood H F L (frestrictLe t ω)} =ᵐ[P] Set.univ := by
      filter_upwards [hbad] with ω hω
      exact propext ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
    have hone : P.real {ω | ¬ historyGood H F L (frestrictLe t ω)} = 1 :=
      (measureReal_congr heq).trans probReal_univ
    linarith
  exact extract_greedy_family Φ H B L ω t
    (greedy_steps_of_final_good Φ H B hB hθ hL hn hnpos hsmall ω t hωsupport hωgood) hωgood

end Arxiv2411_18291

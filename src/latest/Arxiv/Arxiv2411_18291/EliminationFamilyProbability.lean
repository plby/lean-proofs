import Arxiv.Arxiv2411_18291.EliminationPlacementProbability
import Arxiv.Arxiv2411_18291.EliminationFamily
import Arxiv.Arxiv2411_18291.FiniteObservedOutput

/-! # Finite probability laws for actual cancellation-family outputs -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V I : Type*} [Fintype W] [Fintype V] [Fintype I]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}

theorem EliminationFamily.embedding_injective (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q) (θ : ℝ) :
    Function.Injective (fun E : EliminationFamily S N B P Q θ => E.embedding) := by
  intro E F h
  cases E
  cases F
  cases h
  rfl

instance EliminationFamily.finite (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q) (θ : ℝ) :
    Finite (EliminationFamily S N B P Q θ) :=
  Finite.of_injective (fun E => E.embedding) (EliminationFamily.embedding_injective S N B P Q θ)

def eliminationFamilyOutputEvent (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q) (θ : ℝ) :
    Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ E : EliminationFamily S N B P Q θ,
    ∀ i : I, ω ((Fintype.equivFin I i : ℕ) + 1) = chosenEmbedding (E.embedding i)}

theorem measurableSet_eliminationFamilyOutputEvent (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q) (θ : ℝ) :
    MeasurableSet (eliminationFamilyOutputEvent S N B P Q θ) := by
  unfold eliminationFamilyOutputEvent
  simp only [Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro E
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_singleton (chosenEmbedding (E.embedding i))).preimage
    (measurable_pi_apply ((Fintype.equivFin I i : ℕ) + 1))

def eliminationFamilyOutputLaw (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q)
    (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V) (θ : ℝ) :
    PMF (Option (EliminationFamily S N B P Q θ)) :=
  FiniteHistoryProcess.observedOutputLaw (unstoppedGreedyProbability Φ S.graph B)
    (fun E i => chosenEmbedding (E.embedding i))

theorem eliminationFamilyOutputLaw_failure_real (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (B : Hypergraph V (r + 1)) (P Q : I → Block V q)
    (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V) (θ : ℝ) :
    (eliminationFamilyOutputLaw S N B P Q Φ θ none).toReal =
      1 - (unstoppedGreedyProbability Φ S.graph B).real
        (eliminationFamilyOutputEvent S N B P Q θ) :=
  FiniteHistoryProcess.observedOutputLaw_failure_real _ _

theorem eliminationPlacementEvent_subset_familyOutputEvent
    (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (B : Hypergraph V (r + 1)) (P Q : I → Block V q)
    (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V) (θ L : ℝ)
    (hsupport : ∀ i, cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) ⊆ B) :
    eliminationPlacementEvent S N (Fintype.card I)
        (fun i => P ((Fintype.equivFin I).symm i))
        (fun i => Q ((Fintype.equivFin I).symm i)) Φ B θ L ⊆
      eliminationFamilyOutputEvent S N B P Q (θ + S.graph.card * L) := by
  rintro ω ⟨Ψ, ⟨hΨ, hroots, hbound⟩, hmatch⟩
  let enum : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Ξ : I → W ↪ V := fun i => (Ψ (enum.symm i)).val
  refine ⟨{
    embedding := Ξ
    positive_root := ?_
    negative_root := ?_
    root_support := hsupport
    avoids := fun i => hΨ.avoids (enum.symm i)
    disjoint := ?_
    bounded := ?_ }, ?_⟩
  · intro i
    simpa only [Ξ, enum, Equiv.symm_symm, Equiv.symm_apply_apply] using
      (hroots (enum.symm i)).1
  · intro i
    simpa only [Ξ, enum, Equiv.symm_symm, Equiv.symm_apply_apply] using
      (hroots (enum.symm i)).2
  · intro i j hij
    exact hΨ.disjoint (fun h => hij (enum.symm.injective h))
  · dsimp only [Ξ]
    rw [biUnion_univ_reindex enum.symm
      (fun i : Fin (Fintype.card I) =>
        mapGraph (Ψ i).val (newEdges (S.base.val ∪ N.val) S.graph))]
    exact hbound
  · intro i
    exact hmatch (enum.symm i)

theorem exists_elimination_family_output_probability_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (N : Block W q) (e : Block W (r + 1))
    (hpair : IsEliminationPair S N e) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (M : ℕ) (hM : 0 < M)
    {A ρ : ℝ} (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * M : ℕ) : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hsupport : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M)
    (J : Type) [Fintype J] (P Q : J → Block (Fin n) q)
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hinter : ∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) :
    ∃ Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n,
      (∀ i : Fin (Fintype.card J),
        rootImage (Φ i) S.base subset_union_left = P ((Fintype.equivFin J).symm i) ∧
        rootImage (Φ i) N subset_union_right = Q ((Fintype.equivFin J).symm i)) ∧
      1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
        (unstoppedGreedyProbability Φ S.graph B).real
          (eliminationFamilyOutputEvent S N B P Q
            (A * (n : ℝ) ^ (-ρ) + S.graph.card *
              (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
                A * (n : ℝ) ^ (-ρ))))) := by
  let enum : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hnW : Fintype.card W ≤ n := hw.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  have hmaps (i : Fin (Fintype.card J)) : ∃ φ : ↥(S.base.val ∪ N.val) ↪ Fin n,
      rootImage φ S.base subset_union_left = P (enum i) ∧
        rootImage φ N subset_union_right = Q (enum i) := by
    obtain ⟨d, hd⟩ := hinter (enum i)
    exact hpair.root_map (P (enum i)) (Q (enum i)) d hd
  choose φ hφP hφQ using hmaps
  obtain ⟨f₀⟩ := Function.Embedding.nonempty_of_card_le
    (α := W) (β := Fin n) (by simpa only [Fintype.card_fin] using hnW)
  let φ₀ : ↥(S.base.val ∪ N.val) ↪ Fin n :=
    (Function.Embedding.subtype (· ∈ S.base.val ∪ N.val)).trans f₀
  let Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n := fun i =>
    if hi : i < Fintype.card J then φ ⟨i, hi⟩ else φ₀
  have hΦ (i : Fin (Fintype.card J)) : Φ i = φ i := by
    dsimp only [Φ]
    rw [dif_pos i.isLt]
  have hΦP (i : Fin (Fintype.card J)) : rootImage (Φ i) S.base subset_union_left = P (enum i) := by
    rw [hΦ i]
    exact hφP i
  have hΦQ (i : Fin (Fintype.card J)) : rootImage (Φ i) N subset_union_right = Q (enum i) := by
    rw [hΦ i]
    exact hφQ i
  have hb := elimination_placements_probability_paper_threshold S N e hpair hqr hn hw hS
    M hM hA hAb hρ hρhalf D B hD hB hmult (Fintype.card J)
    (fun i => P (enum i)) (fun i => Q (enum i)) (fun i => hP (enum i))
    (fun i => hQ (enum i)) (hinj.comp enum.injective) Φ hΦP hΦQ
  have hsource : ∀ i : J, cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) ⊆ B := by
    intro i f hf
    rcases mem_union.mp hf with hp | hq
    · exact hsupport (mem_biUnion.mpr ⟨P i, hP i, hp⟩)
    · exact hsupport (mem_biUnion.mpr ⟨Q i, hQ i, hq⟩)
  exact ⟨Φ, fun i => ⟨hΦP i, hΦQ i⟩, hb.trans_le (measureReal_mono
    (eliminationPlacementEvent_subset_familyOutputEvent S N B P Q Φ _ _ hsource))⟩

end Arxiv2411_18291

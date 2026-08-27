import Arxiv.Arxiv2411_18291.SplittingPlacementProbability
import Arxiv.Arxiv2411_18291.SplittingFamily
import Arxiv.Arxiv2411_18291.FiniteObservedOutput

/-! # Actual random outputs of the signed splitting stage -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

theorem SplittingFamily.embedding_injective (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ) (θ : ℝ) :
    Function.Injective (fun F : SplittingFamily S D B C θ => F.embedding) := by
  intro E F h
  cases E
  cases F
  cases h
  rfl

instance SplittingFamily.finite (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ) (θ : ℝ) :
    Finite (SplittingFamily S D B C θ) :=
  Finite.of_injective (fun F => F.embedding) (SplittingFamily.embedding_injective S D B C θ)

def splittingRootSequence (D : Finset (Block V q)) (C : ℕ) (Q₀ : Block V q) :
    ℕ → Block V q :=
  fun i => if hi : i < Fintype.card (SignedCliqueSlots D C) then
    (((Fintype.equivFin (SignedCliqueSlots D C)).symm ⟨i, hi⟩).1).val else Q₀

omit [Fintype V] [DecidableEq V] in
@[simp] theorem splittingRootSequence_eq (D : Finset (Block V q)) (C : ℕ)
    (Q₀ : Block V q) (i : Fin (Fintype.card (SignedCliqueSlots D C))) :
    splittingRootSequence D C Q₀ i =
      (((Fintype.equivFin (SignedCliqueSlots D C)).symm i).1).val := by
  unfold splittingRootSequence
  rw [dif_pos i.isLt]

def splittingFamilyOutputEvent (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ) (θ : ℝ) :
    Set (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.observedOutputEvent
    (fun (F : SplittingFamily S D B C θ) s => chosenEmbedding (F.embedding s))

theorem measurableSet_splittingFamilyOutputEvent (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ) (θ : ℝ) :
    MeasurableSet (splittingFamilyOutputEvent S D B C θ) :=
  FiniteHistoryProcess.measurableSet_observedOutputEvent _

def splittingFamilyOutputLaw (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ)
    (Q₀ : Block V q) (θ : ℝ) : PMF (Option (SplittingFamily S D B C θ)) :=
  let Q := splittingRootSequence D C Q₀
  FiniteHistoryProcess.observedOutputLaw
    (unstoppedPrescribedGreedyProbability (fun i => edgeRootMap S.base (Q i))
      (separatedCandidates (fun i => edgeRootMap S.base (Q i))
        (fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card)) S.graph B)
    (fun F s => chosenEmbedding (F.embedding s))

theorem splittingFamilyOutputLaw_failure_real (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ)
    (Q₀ : Block V q) (θ : ℝ) :
    let Q := splittingRootSequence D C Q₀
    (splittingFamilyOutputLaw S D B C Q₀ θ none).toReal = 1 -
      (unstoppedPrescribedGreedyProbability (fun i => edgeRootMap S.base (Q i))
        (separatedCandidates (fun i => edgeRootMap S.base (Q i))
          (fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card)) S.graph B).real
        (splittingFamilyOutputEvent S D B C θ) :=
  FiniteHistoryProcess.observedOutputLaw_failure_real _ _

theorem splittingPlacementEvent_subset_familyOutputEvent (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ)
    (Q₀ : Block V q) (θ L : ℝ) (hDB : cliqueSupport (r + 1) D ⊆ B) :
    splittingPlacementEvent S (Fintype.card (SignedCliqueSlots D C))
        (splittingRootSequence D C Q₀) B θ L ⊆
      splittingFamilyOutputEvent S D B C (θ + S.graph.card * L) := by
  rintro ω ⟨Ψ, ⟨hΨ, hprivate, hb⟩, hmatch⟩
  let I := SignedCliqueSlots D C
  let enum : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f : I → W ↪ V := fun s => (Ψ (enum.symm s)).val
  have hbase (i : Fin (Fintype.card I)) :
      mapBlock (Ψ i).val S.base = splittingRootSequence D C Q₀ i :=
    (EmbeddingExtension.map_rootBlock (edgeRootMap S.base (splittingRootSequence D C Q₀ i))
      (Ψ i) S.base (Subset.refl _)).trans
        (rootImage_edgeRootMap S.base (splittingRootSequence D C Q₀ i))
  refine ⟨{
    embedding := f
    base := ?_
    source_support := hDB
    avoids := fun s => hΨ.avoids (enum.symm s)
    disjoint := ?_
    free_disjoint := ?_
    bounded := ?_ }, ?_⟩
  · intro s
    simpa only [f, splittingRootSequence_eq, I, enum, Equiv.symm_symm,
      Equiv.symm_apply_apply] using hbase (enum.symm s)
  · intro s u hsu
    exact hΨ.disjoint (fun h => hsu (enum.symm.injective h))
  · intro s u hsu hshare
    apply hprivate (enum.symm s) (enum.symm u) (fun h => hsu (enum.symm.injective h))
    simpa only [splittingRootSequence_eq, I, enum, Equiv.symm_symm,
      Equiv.symm_apply_apply] using hshare
  · dsimp only [f]
    rw [biUnion_univ_reindex enum.symm
      (fun i : Fin (Fintype.card I) => mapGraph (Ψ i).val (newEdges S.base.val S.graph))]
    exact hb
  · intro s
    exact hmatch (enum.symm s)

theorem splitting_family_output_probability_at_exponent
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (C M : ℕ) (hC : 0 < C)
    (hconflict : q.choose (r + 1) * ((2 * C) * M) ≤ (4 * q) ^ (8 * q))
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : 2 * (C : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M)
    (Q₀ : Block (Fin n) q) :
    let Q := splittingRootSequence D C Q₀
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedPrescribedGreedyProbability (fun i => edgeRootMap S.base (Q i))
        (separatedCandidates (fun i => edgeRootMap S.base (Q i))
          (fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card)) S.graph B).real
        (splittingFamilyOutputEvent S D B C
          (A * (n : ℝ) ^ (-ρ) + S.graph.card *
            (8 * (r + 1).factorial * (((2 * C : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ))))) := by
  classical
  dsimp only
  let I := SignedCliqueSlots D C
  let enum : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Q := splittingRootSequence D C Q₀
  have hQ (i : Fin (Fintype.card I)) : Q i = (enum i).1.val :=
    splittingRootSequence_eq D C Q₀ i
  have hQmem (i : Fin (Fintype.card I)) : Q i ∈ D := hQ i ▸ (enum i).1.property
  have hrep (P : Block (Fin n) q) :
      (univ.filter fun i : Fin (Fintype.card I) => Q i = P).card ≤ 2 * C := by
    let eP : {i : Fin (Fintype.card I) // Q i = P} ≃ {s : I // s.1.val = P} :=
      Equiv.subtypeEquiv enum (fun i => by rw [hQ i])
    have heq : (univ.filter fun i : Fin (Fintype.card I) => Q i = P).card =
        (univ.filter fun s : I => s.1.val = P).card := by
      simpa only [Fintype.card_subtype] using Fintype.card_congr eP
    rw [heq]
    exact signedCliqueSlots_root_count D C P
  have hb := splitting_placements_probability_at_exponent S hqr hn hw hS
    (2 * C) M (by omega) hconflict hA (by push_cast; nlinarith only [hAb]) hρ hρhalf
    D B hD hB hmult (Fintype.card I) Q (fun i hi => hQmem ⟨i, hi⟩) hrep
  exact hb.trans_le (measureReal_mono
    (splittingPlacementEvent_subset_familyOutputEvent S D B C Q₀ _ _ hDB))

end Arxiv2411_18291

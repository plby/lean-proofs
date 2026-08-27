import Arxiv.Arxiv2411_18291.VariableCliqueSlots
import Arxiv.Arxiv2411_18291.SplittingFamily
import Arxiv.Arxiv2411_18291.CliquePairRootDegrees

/-! # Actual separated splitting with variable clique capacities

Finite numerical conditions construct one fixed exchange family for all
representations within the capacity function. Root degrees and conflicts
are controlled by capacity sums, without a uniform multiplicity bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

structure VariableSplittingFamily (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1))
    (C : Block V q → ℕ) (θ : ℝ) where
  embedding : VariableCliqueSlots D C → W ↪ V
  base : ∀ s, mapBlock (embedding s) S.base = s.1.val
  source_support : cliqueSupport (r + 1) D ⊆ B
  avoids : ∀ s, Disjoint (mapGraph (embedding s) (newEdges S.base.val S.graph)) B
  disjoint : Pairwise fun s t => Disjoint
    (mapGraph (embedding s) (newEdges S.base.val S.graph))
    (mapGraph (embedding t) (newEdges S.base.val S.graph))
  free_disjoint : ∀ s t : VariableCliqueSlots D C,
    s ≠ t → r + 1 ≤ (s.1.val.val ∩ t.1.val.val).card →
    Disjoint ((univ \ S.base.val).map (embedding s)) ((univ \ S.base.val).map (embedding t))
  bounded : IsGraphBounded
    (B ∪ univ.biUnion fun s => mapGraph (embedding s) (newEdges S.base.val S.graph)) θ

theorem VariableSplittingFamily.replacements_disjoint {S : ExchangeSystem W q (r + 1)}
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}
    (F : VariableSplittingFamily S D B C θ) (hqr : r + 1 ≤ q) :
    Pairwise fun s t => Disjoint (S.map (F.embedding s)).replacementCliques
      (S.map (F.embedding t)).replacementCliques := by
  intro s t hst
  apply replacement_copies_disjoint S hqr (F.embedding s) (F.embedding t) B
    (F.avoids s) _ (F.disjoint hst)
  rw [F.base t]
  intro e he
  exact F.source_support (mem_biUnion.mpr ⟨t.1.val, t.1.property, he⟩)

theorem VariableSplittingFamily.signed_representation {S : ExchangeSystem W q (r + 1)}
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}
    (F : VariableSplittingFamily S D B C θ) (hqr : r + 1 ≤ q) (Φ : Block V q → ℤ)
    (hΦ : ∀ Q, |Φ Q| ≤ C Q) (hs : ∀ Q, Q ∉ D → Φ Q = 0) :
    ∃ P N : Finset (Block V q),
      P ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧
      N ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧ Disjoint P N ∧
      boundary (r + 1) (indicator P - indicator N) = boundary (r + 1) Φ := by
  let c : VariableCliqueSlots D C → ℤ := fun s => signedSlotWeight (Φ s.1.val) s.2
  obtain ⟨P, N, hP, hN, hdis, hboundary⟩ := exchangeSum_signed_sets
    (fun s => S.map (F.embedding s)) c (F.replacements_disjoint hqr)
    (fun s => signedSlotWeight_abs_le _ _)
  have hroot (s : VariableCliqueSlots D C) :
      (S.map (F.embedding s)).base = s.1.val := F.base s
  refine ⟨P, N, hP, hN, hdis, ?_⟩
  rw [hboundary]
  simp only [hroot, c]
  exact variableCliqueSlots_boundary D C Φ hΦ hs

theorem exists_variable_splitting_family (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) (D : Finset (Block V q)) (C : Block V q → ℕ)
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hθ : 0 ≤ θ)
    (hD : IsCliqueCapacityBounded r D C θ) (hB : IsGraphBounded B θ)
    (hDB : cliqueSupport (r + 1) D ⊆ B) (d : ℕ)
    (hconflict : (q.choose r : ℝ) * (2 * θ * Fintype.card V) ≤ d)
    (hnpos : 0 < Fintype.card V) (hn : 4 * Fintype.card W ^ 2 ≤ Fintype.card V)
    (hsize : 4 * Fintype.card W * (d * Fintype.card W) ≤ Fintype.card V)
    (hsmall : S.graph.card * (2 * θ + S.graph.card *
      (8 * (r + 1).factorial * (2 * θ))) ≤ 1 / 4)
    (hfailure : S.graph.card * Fintype.card (Block V r) *
      Real.exp (-(4 * (r + 1).factorial * (2 * θ) * Fintype.card V / 3)) < 1) :
    Nonempty (VariableSplittingFamily S D B C
      (θ + S.graph.card * (16 * (r + 1).factorial * θ))) := by
  classical
  have hqw : q ≤ Fintype.card W := by
    simpa only [S.base.property] using card_le_univ S.base.val
  have hwn : Fintype.card W ≤ Fintype.card V := by
    have hw : 1 ≤ Fintype.card W := by omega
    nlinarith only [hw, hn]
  obtain ⟨s, _, hsq⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (by simpa only [card_univ] using hqw.trans hwn)
  let Q₀ : Block V q := ⟨s, hsq⟩
  let I := VariableCliqueSlots D C
  let t := Fintype.card I
  let enum : Fin t ≃ I := (Fintype.equivFin I).symm
  let Q : ℕ → Block V q := fun i => if hi : i < t then (enum ⟨i, hi⟩).1.val else Q₀
  have hQ (i : Fin t) : Q i = (enum i).1.val := by
    dsimp only [Q]
    rw [dif_pos i.isLt]
  let Φ : ℕ → S.base.val ↪ V := fun i => edgeRootMap S.base (Q i)
  let Rel : ℕ → ℕ → Prop := fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card
  have hrel : ∀ i < t, (priorRelated Rel i).card ≤ d := by
    intro i hi
    let eP : {j : Fin t // r + 1 ≤ ((Q j).val ∩ (Q i).val).card} ≃
        {s : I // r + 1 ≤ (s.1.val.val ∩ (Q i).val).card} :=
      Equiv.subtypeEquiv enum (fun j => by rw [hQ j])
    have heq : (cliqueOverlapIndices (r + 1) (fun j : Fin t => Q j) (Q i)).card =
        (cliqueOverlapIndices (r + 1) (fun s : I => s.1.val) (Q i)).card := by
      simpa only [cliqueOverlapIndices, Fintype.card_subtype] using Fintype.card_congr eP
    have hprior := prior_clique_overlap_le (r + 1) Q hi
    rw [heq] at hprior
    have hpriorR : ((priorRelated Rel i).card : ℝ) ≤
        (cliqueOverlapIndices (r + 1) (fun s : I => s.1.val) (Q i)).card := by
      exact_mod_cast hprior
    exact_mod_cast hpriorR.trans ((hD.variable_overlap_le (Q i)).trans hconflict)
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) (2 * θ) := by
    intro f _ hf
    let E : I → Block V (r + 1) := fun s => rootImage (edgeRootMap S.base s.1.val) f hf
    have hE : IsEdgeFamilyBounded E (2 * θ) := hD.variable_edgeFamily E (by
      intro s
      exact (rootImage_subset_usedVertices (edgeRootMap S.base s.1.val) f hf).trans_eq
        (edgeRootMap_usedVertices S.base s.1.val))
    have heq : (fun i : Fin t => rootImage (Φ i) f hf) = fun i => E (enum i) := by
      funext i
      dsimp only [Φ, E]
      rw [hQ i]
    intro T
    rw [heq, familyDegree_reindex]
    exact hE T
  have hadm := admissible_clique_root S.graph S.base hqr
    (S.positive_decomposition.clique_subset S.base_mem)
  obtain ⟨Ψ, hΨ, hsep⟩ := exists_separated_greedy_family Φ Rel S.graph B
    (hB.mono (by linarith only [hθ])) (by positivity) t d hrel hnpos hn hsize
    hsmall hadm hroots hfailure
  have hbase (i : Fin t) : mapBlock (Ψ i).val S.base = Q i :=
    (EmbeddingExtension.map_rootBlock (edgeRootMap S.base (Q i)) (Ψ i) S.base
      (Subset.refl _)).trans (rootImage_edgeRootMap S.base (Q i))
  have hprivate (i j : Fin t) (hij : i ≠ j)
      (hshare : r + 1 ≤ ((Q i).val ∩ (Q j).val).card) :
      Disjoint ((univ \ S.base.val).map (Ψ i).val) ((univ \ S.base.val).map (Ψ j).val) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hsep i j hlt hshare
    · have hreverse : Rel j i := by
        change r + 1 ≤ ((Q j).val ∩ (Q i).val).card
        rw [inter_comm]
        exact hshare
      exact (hsep j i hgt hreverse).symm
  let f : I → W ↪ V := fun s => (Ψ (enum.symm s)).val
  refine ⟨{
    embedding := f
    base := ?_
    source_support := hDB
    avoids := fun s => hΨ.avoids (enum.symm s)
    disjoint := ?_
    free_disjoint := ?_
    bounded := ?_ }⟩
  · intro s
    dsimp only [f]
    rw [hbase, hQ, Equiv.apply_symm_apply]
  · intro s u hsu
    exact hΨ.disjoint (fun h => hsu (enum.symm.injective h))
  · intro s u hsu hshare
    apply hprivate (enum.symm s) (enum.symm u) (fun h => hsu (enum.symm.injective h))
    simpa only [hQ, Equiv.apply_symm_apply] using hshare
  · change IsGraphBounded (B ∪ univ.biUnion (fun s : I =>
      mapGraph (Ψ (enum.symm s)).val (newEdges S.base.val S.graph))) _
    rw [biUnion_univ_reindex enum.symm
      (fun i : Fin t => mapGraph (Ψ i).val (newEdges S.base.val S.graph))]
    have hg := hΨ.graphBounded hB (by positivity)
    rw [show 8 * ((r + 1).factorial : ℝ) * (2 * θ) =
      16 * (r + 1).factorial * θ by ring] at hg
    exact hg

end Arxiv2411_18291

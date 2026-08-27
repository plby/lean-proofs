import Arxiv.Arxiv2411_18291.ExplicitSplittingPlacements
import Arxiv.Arxiv2411_18291.SplittingFamily

/-! # Finite splitting families for all bounded integer representations -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_splitting_family_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (8 * q)) (C M : ℕ) (hC : 0 < C)
    (hconflict : q.choose (r + 1) * ((2 * C) * M) ≤ (4 * q) ^ (8 * q))
    {A : ℝ} (hA : 1 ≤ A) (hAb : 4 * (C : ℝ) * A ≤ (4 * q : ℝ) ^ (8 * q))
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M) :
    Nonempty (SplittingFamily S D B C
      (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) + S.graph.card *
        (8 * (r + 1).factorial *
          (((2 * C : ℕ) : ℝ) * A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))))) := by
  classical
  have hnq : q ≤ n := by
    have hh := (boost_threshold_root_size_bounds (by omega : 2 ≤ q)
      ((boost_threshold_le_paper_threshold hqr).trans hn)).2.2
    omega
  obtain ⟨s, _, hsq⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (by simpa only [card_univ, Fintype.card_fin] using hnq)
  let Q₀ : Block (Fin n) q := ⟨s, hsq⟩
  let I := SignedCliqueSlots D C
  let t := Fintype.card I
  let enum : Fin t ≃ I := (Fintype.equivFin I).symm
  let Q : ℕ → Block (Fin n) q :=
    fun i => if hi : i < t then (enum ⟨i, hi⟩).1.val else Q₀
  have hQ (i : Fin t) : Q i = (enum i).1.val := by
    dsimp only [Q]
    rw [dif_pos i.isLt]
  have hQmem (i : Fin t) : Q i ∈ D := hQ i ▸ (enum i).1.property
  have hrep (P : Block (Fin n) q) : (univ.filter fun i : Fin t => Q i = P).card ≤ 2 * C := by
    let eP : {i : Fin t // Q i = P} ≃ {s : I // s.1.val = P} :=
      Equiv.subtypeEquiv enum (fun i => by rw [hQ i])
    have heq : (univ.filter fun i : Fin t => Q i = P).card =
        (univ.filter fun s : I => s.1.val = P).card := by
      simpa only [Fintype.card_subtype] using Fintype.card_congr eP
    rw [heq]
    exact signedCliqueSlots_root_count D C P
  obtain ⟨Ψ, hΨ, hprivate, hb⟩ := exists_splitting_placements_paper_threshold S hqr hn hw hS
    (2 * C) M (by omega) hconflict hA (by push_cast; nlinarith only [hAb])
    D B hD hB hmult t Q (fun i hi => hQmem ⟨i, hi⟩) hrep
  have hbase (i : Fin t) : mapBlock (Ψ i).val S.base = Q i :=
    (EmbeddingExtension.map_rootBlock (edgeRootMap S.base (Q i)) (Ψ i) S.base
      (Subset.refl _)).trans (rootImage_edgeRootMap S.base (Q i))
  let f : I → W ↪ Fin n := fun s => (Ψ (enum.symm s)).val
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
    exact hb

end Arxiv2411_18291

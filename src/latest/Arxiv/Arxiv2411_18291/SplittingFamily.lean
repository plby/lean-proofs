import Arxiv.Arxiv2411_18291.SplittingPlacements
import Arxiv.Arxiv2411_18291.SignedCliqueSlots

/-!
# A fixed sparse splitting family for every bounded representation

Construct exchange copies on all positive and negative slots of an input
clique family. The copies are fixed before a represented vector is chosen.
Every vector with coefficients bounded by the slot capacity then becomes
the difference of two sets of replacement cliques, with unchanged boundary.
The construction retains both edge disjointness and the private-vertex
separation needed for the following elimination stages.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r C : ℕ}

structure SplittingFamily (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) (C : ℕ) (θ : ℝ) where
  embedding : SignedCliqueSlots D C → W ↪ V
  base : ∀ s, mapBlock (embedding s) S.base = s.1.val
  source_support : cliqueSupport (r + 1) D ⊆ B
  avoids : ∀ s, Disjoint (mapGraph (embedding s) (newEdges S.base.val S.graph)) B
  disjoint : Pairwise fun s t => Disjoint
    (mapGraph (embedding s) (newEdges S.base.val S.graph))
    (mapGraph (embedding t) (newEdges S.base.val S.graph))
  free_disjoint : ∀ s t : SignedCliqueSlots D C,
    s ≠ t → r + 1 ≤ (s.1.val.val ∩ t.1.val.val).card →
    Disjoint ((univ \ S.base.val).map (embedding s)) ((univ \ S.base.val).map (embedding t))
  bounded : IsGraphBounded
    (B ∪ univ.biUnion fun s => mapGraph (embedding s) (newEdges S.base.val S.graph)) θ

theorem SplittingFamily.replacements_disjoint {S : ExchangeSystem W q (r + 1)}
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)} {θ : ℝ}
    (F : SplittingFamily S D B C θ) (hqr : r + 1 ≤ q) :
    Pairwise fun s t => Disjoint (S.map (F.embedding s)).replacementCliques
      (S.map (F.embedding t)).replacementCliques := by
  intro s t hst
  apply replacement_copies_disjoint S hqr (F.embedding s) (F.embedding t) B
    (F.avoids s) _ (F.disjoint hst)
  rw [F.base t]
  intro e he
  exact F.source_support (mem_biUnion.mpr ⟨t.1.val, t.1.property, he⟩)

theorem SplittingFamily.signed_representation {S : ExchangeSystem W q (r + 1)}
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)} {θ : ℝ}
    (F : SplittingFamily S D B C θ) (hqr : r + 1 ≤ q) (Φ : Block V q → ℤ)
    (hΦ : ∀ Q, |Φ Q| ≤ C) (hs : ∀ Q, Q ∉ D → Φ Q = 0) :
    ∃ P N : Finset (Block V q),
      P ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧
      N ⊆ exchangeSupport (fun s => S.map (F.embedding s)) ∧ Disjoint P N ∧
      boundary (r + 1) (indicator P - indicator N) = boundary (r + 1) Φ := by
  let c : SignedCliqueSlots D C → ℤ := fun s => signedSlotWeight (Φ s.1.val) s.2
  obtain ⟨P, N, hP, hN, hdis, hboundary⟩ := exchangeSum_signed_sets
    (fun s => S.map (F.embedding s)) c (F.replacements_disjoint hqr)
    (fun s => signedSlotWeight_abs_le _ _)
  have hroot (s : SignedCliqueSlots D C) : (S.map (F.embedding s)).base = s.1.val := F.base s
  refine ⟨P, N, hP, hN, hdis, ?_⟩
  rw [hboundary]
  simp only [hroot, c]
  exact signedCliqueSlots_boundary D Φ hΦ hs

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem biUnion_univ_reindex {I J X : Type*} [Fintype I] [Fintype J] [DecidableEq X]
    (e : I ≃ J) (f : J → Finset X) :
    (univ.biUnion fun i => f (e i)) = univ.biUnion f := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨e i, mem_univ _, hi⟩
  · intro hx
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨e.symm j, mem_univ _, by simpa only [Equiv.apply_symm_apply] using hj⟩

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_splitting_family (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) (C M : ℕ) (hC : 0 < C) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)) →
      IsGraphBounded B (A * (n : ℝ) ^ (-ρ)) → cliqueSupport (r + 1) D ⊆ B →
      (∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M) →
      Nonempty (SplittingFamily S D B C (A * (n : ℝ) ^ (-ρ) + S.graph.card *
        (8 * (r + 1).factorial * (((2 * C : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ))))) := by
  classical
  filter_upwards [eventually_ge_atTop q,
    eventually_exists_splitting_placements S hqr (2 * C) M (by omega) hA hρ hρ1]
    with n hnq hplace
  intro D B hD hB hDB hmult
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
  obtain ⟨Ψ, hΨ, hprivate, hb⟩ := hplace D B hD hB hmult t Q
    (fun i hi => hQmem ⟨i, hi⟩) hrep
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

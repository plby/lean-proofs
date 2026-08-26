import ErdosProblems.Erdos547.ReducedPairInterface
import ErdosProblems.Erdos547.SeedForestEmbedding
import ErdosProblems.Erdos547.AllowedSeedDegrees

/-!
# Embedding the actual fine-partition seeds into reduced-graph anchors
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)
  {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

open scoped Classical in
theorem exists_reduced_seed_copy (hT : T.IsTree) (R : EquitableRegularPartition G ε)
    (δ d : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) (hεone : ε ≤ 1) (hclean : ε + 2 * δ < 1)
    (anchor : Fin 2 → ↥R.clusters)
    (hanchor : ∀ c c', c ≠ c' → (R.reducedGraph d).Adj (anchor c) (anchor c'))
    (B Q : ↥R.clusters → Finset V) (hB : ∀ i, B i ⊆ i.val) (hQ : ∀ i, Q i ⊆ i.val)
    (hBsize : ∀ i, (R.clusterSize : ℝ) * ε ≤ (B i).card)
    (hQsize : ∀ i, (R.clusterSize : ℝ) * ε ≤ (Q i).card)
    (hcol : ∀ c, (P.nearVertices c).Nonempty)
    (hsmall : (P.seeds.card : ℝ) ≤ (d - 2 * ε - 2 * δ) * R.clusterSize) :
    ∃ seed : (T.induce (P.seeds : Set U)).Copy G, ∀ z : ↥P.seeds,
      seed z ∈ (anchor (col z.val)).val ∧
      ((P.seedExceptions G ε (fun c ↦ (anchor c).val)
        (fun c ↦ (R.reducedGraph d).neighborFinset (anchor c)) Subtype.val B seed z).card : ℝ) ≤
        δ * R.clusters.card ∧
      ((P.seedExceptions G ε (fun c ↦ (anchor c).val)
        (fun c ↦ (R.reducedGraph d).neighborFinset (anchor c)) Subtype.val Q seed z).card : ℝ) ≤
        δ * R.clusters.card := by
  classical
  let X := fun c ↦ (anchor c).val
  let J := fun c ↦ (R.reducedGraph d).neighborFinset (anchor c)
  have hreg (c : Fin 2) (i : ↥R.clusters) (hi : i ∈ J c) : G.IsUniform ε (X c) i.val :=
    (R.reduced_pair d (anchor c) i ((SimpleGraph.mem_neighborFinset _ _ _).mp hi)).1
  have hsmall' : (Fintype.card ↥P.seeds : ℝ) ≤ (d - 2 * ε - 2 * δ) * R.clusterSize := by
    simpa only [Fintype.card_coe] using hsmall
  obtain ⟨seed, hseed⟩ := exists_typical_seed_forest_copy (T.induce (P.seeds : Set U)) G
    (hT.isAcyclic.induce _) (fun z : ↥P.seeds ↦ col z.val) (P.seed_colour_surjective hcol)
    (fun _ _ h ↦ col.valid h) ε δ d hδ hεδ hεone hclean X R.clusterSize
    (by have hh := R.positive_size; omega) (fun c ↦ R.equal_size (anchor c).val (anchor c).property)
    (fun c c' h ↦ (R.reduced_pair d (anchor c) (anchor c') (hanchor c c' h)).2.1)
    (fun c c' h ↦ (R.reduced_pair d (anchor c) (anchor c') (hanchor c c' h)).1)
    (fun c c' h ↦ (R.reduced_pair d (anchor c) (anchor c') (hanchor c c' h)).2.2)
    hsmall' J Subtype.val B Q hreg (fun _ i _ ↦ hB i) (fun _ i _ ↦ hQ i)
    (fun _ i _ ↦ by simpa only [R.equal_size i.val i.property] using hBsize i)
    (fun _ i _ ↦ by simpa only [R.equal_size i.val i.property] using hQsize i)
  refine ⟨seed, ?_⟩
  intro z
  have hJ : ((J (col z.val)).card : ℝ) ≤ R.clusters.card := by
    have hn : (J (col z.val)).card ≤ R.clusters.card := by
      simpa only [Fintype.card_coe] using Finset.card_le_univ (J (col z.val))
    exact_mod_cast hn
  have hscale := mul_le_mul_of_nonneg_left hJ hδ.le
  exact ⟨(hseed z).1, ((hseed z).2.1).trans hscale, ((hseed z).2.2).trans hscale⟩

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_reduced_seed_copy

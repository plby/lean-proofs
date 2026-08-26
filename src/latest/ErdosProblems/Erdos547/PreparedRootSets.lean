import ErdosProblems.Erdos547.PrivateDemandMargins
import ErdosProblems.Erdos547.AttachmentRootPools

/-!
# Constructing the private sets and both reservoir root pools
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq U]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)}

structure ShrubRootSets (P : FineTreePartition T r ℓ col) (G : SimpleGraph V)
    (C Q : I → Finset V) (head : ↥P.shrubs → I) (seed : ↥P.seeds → V)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val) (b : ℝ) where
  privateSet : ↥P.shrubs → Finset V
  private_sub : ∀ S, privateSet S ⊆ C (head S)
  private_card : ∀ S, (privateSet S).card = (P.nearPart S).card
  private_disjoint : Pairwise (fun S A ↦ Disjoint (privateSet S) (privateSet A))
  private_reservoir : ∀ S i, Disjoint (privateSet S) (Q i)
  private_seed : ∀ S, ∀ z : ↥P.seeds, seed z ∉ privateSet S
  private_adj : ∀ S, ∀ v ∈ privateSet S, G.Adj (seed (D S).seed) v
  primary : ↥P.shrubs → Finset V
  primary_sub : ∀ S, primary S ⊆ Q (head S)
  primary_card : ∀ S, b ≤ ((primary S).card : ℝ)
  primary_adj : ∀ S, ∀ v ∈ primary S, G.Adj (seed (D S).seed) v
  secondary : ↥P.shrubs → Finset V
  secondary_sub : ∀ S, secondary S ⊆ Q (head S)
  secondary_card : ∀ S, b ≤ ((secondary S).card : ℝ)
  secondary_adj : ∀ S z, (D S).second = some z → ∀ v ∈ secondary S, G.Adj (seed z.1) v

namespace FineTreePartition

open scoped BigOperators

open scoped Classical in
theorem exists_prepared_root_sets [DecidableEq I] (P : FineTreePartition T r ℓ col)
    (G : SimpleGraph V) [DecidableRel G.Adj] (C B Q : I → Finset V)
    (head : ↥P.shrubs → I) (seed : ↥P.seeds → V)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val)
    (w density : Fin 2 → I → ℝ) (M s ε θ b : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ s) (hsone : s ≤ 1) (hε : ε ≤ s * θ)
    (hcluster : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hB : ∀ i, B i ⊆ C i) (hQ : ∀ i, Q i ⊆ C i) (hBQ : ∀ i, Disjoint (B i) (Q i))
    (hseed : ∀ S, ∀ z : ↥P.seeds, seed z ∉ C (head S))
    (hfit : ∀ c i, w c i ≤ density c i)
    (hjoint : ∀ i, w 0 i + w 1 i ≤ max (density 0 i) (density 1 i))
    (hactive : ∀ S, θ ≤ w (P.shrubColour S) (head S))
    (hload : ∀ c i, (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ head S = i ∧ P.shrubColour S = c), ((P.nearPart S).card : ℝ)) ≤
        (1 - s) * M * w c i)
    (hmainDegree : ∀ S, ∀ z ∈ P.attachmentSeeds S,
      (density (P.shrubColour S) (head S) - ε) * M ≤ (degreeIn G (B (head S)) (seed z) : ℝ))
    (hrootDegree : ∀ S, ∀ z ∈ P.attachmentSeeds S, b ≤ (degreeIn G (Q (head S)) (seed z) : ℝ)) :
    Nonempty (ShrubRootSets P G C Q head seed D b) := by
  classical
  let candidates := fun S ↦ (B (head S)).filter (G.Adj (seed (D S).seed))
  have hcanSub (S : ↥P.shrubs) : candidates S ⊆ C (head S) :=
    (Finset.filter_subset _ _).trans (hB _)
  have hcanSize (S : ↥P.shrubs) :
      (density (P.shrubColour S) (head S) - ε) * M ≤ ((candidates S).card : ℝ) :=
    hmainDegree S (D S).seed (P.primary_mem_attachmentSeeds S (D S))
  obtain ⟨R, hR, hcard, hdis⟩ := exists_private_sets_from_relative_demands
    C head P.shrubColour (fun S ↦ (P.nearPart S).card) candidates w density M s ε θ
    hM hs hsone hε hcluster hcanSub hfit hjoint hactive hload hcanSize
  obtain ⟨primary, secondary, hpsub, hpcard, hpadj, hssub, hscard, hsadj⟩ :=
    P.exists_attachment_root_pools G head Q seed D b hrootDegree
  refine ⟨{
    privateSet := R
    private_sub := fun S ↦ (hR S).trans (hcanSub S)
    private_card := hcard
    private_disjoint := hdis
    private_reservoir := ?_
    private_seed := fun S z h ↦ hseed S z (hcanSub S (hR S h))
    private_adj := fun S v hv ↦ (Finset.mem_filter.mp (hR S hv)).2
    primary := primary
    primary_sub := hpsub
    primary_card := hpcard
    primary_adj := hpadj
    secondary := secondary
    secondary_sub := hssub
    secondary_card := hscard
    secondary_adj := hsadj
  }⟩
  intro S i
  have hRB : R S ⊆ B (head S) := (hR S).trans (Finset.filter_subset _ _)
  by_cases hi : head S = i
  · rw [← hi]
    exact (hBQ (head S)).mono_left hRB
  · exact (hcluster (head S) i hi).mono (hRB.trans (hB _)) (hQ i)

end FineTreePartition
end Erdos547

#print axioms Erdos547.FineTreePartition.exists_prepared_root_sets

import ErdosProblems.Erdos547.SeedAttachments

/-!
# Actual reservoir-neighbour pools for the two distinguished roots
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq U]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

def secondarySeed (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val) : ↥P.seeds :=
  (D.second.map Prod.fst).getD D.seed

theorem secondarySeed_mem (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val) :
    P.secondarySeed S D ∈ P.attachmentSeeds S := by
  cases hs : D.second with
  | none =>
      simpa only [secondarySeed, hs, Option.map_none, Option.getD_none] using
        P.primary_mem_attachmentSeeds S D
  | some z =>
      simpa only [secondarySeed, hs, Option.map_some, Option.getD_some] using
        P.secondary_mem_attachmentSeeds S D z hs

theorem secondarySeed_eq (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val)
    (z : ↥P.seeds × ↥S.val) (hz : D.second = some z) : P.secondarySeed S D = z.1 := by
  simp only [secondarySeed, hz, Option.map_some, Option.getD_some]

theorem exists_attachment_root_pools (G : SimpleGraph V) [DecidableRel G.Adj]
    (head : ↥P.shrubs → I) (Q : I → Finset V) (seed : ↥P.seeds → V)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val) (b : ℝ)
    (hdegree : ∀ S, ∀ z ∈ P.attachmentSeeds S,
      b ≤ (degreeIn G (Q (head S)) (seed z) : ℝ)) :
    ∃ primary secondary : ↥P.shrubs → Finset V,
      (∀ S, primary S ⊆ Q (head S)) ∧ (∀ S, b ≤ ((primary S).card : ℝ)) ∧
      (∀ S, ∀ v ∈ primary S, G.Adj (seed (D S).seed) v) ∧
      (∀ S, secondary S ⊆ Q (head S)) ∧ (∀ S, b ≤ ((secondary S).card : ℝ)) ∧
      (∀ S z, (D S).second = some z → ∀ v ∈ secondary S, G.Adj (seed z.1) v) := by
  let primary := fun S ↦ (Q (head S)).filter (G.Adj (seed (D S).seed))
  let secondary := fun S ↦ (Q (head S)).filter (G.Adj (seed (P.secondarySeed S (D S))))
  refine ⟨primary, secondary, fun _ ↦ Finset.filter_subset _ _, ?_, ?_,
    fun _ ↦ Finset.filter_subset _ _, ?_, ?_⟩
  · intro S
    exact hdegree S (D S).seed (P.primary_mem_attachmentSeeds S (D S))
  · intro S v hv
    exact (Finset.mem_filter.mp hv).2
  · intro S
    exact hdegree S (P.secondarySeed S (D S)) (P.secondarySeed_mem S (D S))
  · intro S z hz v hv
    have hh := (Finset.mem_filter.mp hv).2
    rwa [P.secondarySeed_eq S (D S) z hz] at hh

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_attachment_root_pools

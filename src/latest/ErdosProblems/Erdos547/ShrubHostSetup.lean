import ErdosProblems.Erdos547.ShrubStateLoads
import ErdosProblems.Erdos547.ShrubRootCount

/-!
# Explicit data for the two-phase shrub embedding

This structure records regular pairs, finite allocations, private sets, and
numerical margins. It contains no tree-embedding existence assumption.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)}

structure ShrubHostSetup (P : FineTreePartition T r ℓ col) (G : SimpleGraph V)
    [DecidableRel G.Adj] (I : Type*) [Fintype I] [DecidableEq I] where
  clusters : I → Finset V
  head : ↥P.shrubs → I
  seed : (T.induce (P.seeds : Set U)).Copy G
  roots : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val
  ε : ℝ
  d : ℝ
  η : ℝ
  slack : ℝ
  targetFloor : ℝ
  m : ℕ
  mainSize : ℕ
  q : ℕ
  ε_pos : 0 < ε
  η_nonneg : 0 ≤ η
  slack_pos : 0 < slack
  slack_le_one : slack ≤ 1
  targetFloor_pos : 0 < targetFloor
  degree_margin : 2 * ε ≤ d
  embedding_margin : 8 * ε ≤ d ^ 2 * η
  ε_volume : 1 ≤ ε * m
  seed_small : (P.seeds.card : ℝ) ≤ ε * m
  seed_buffer : 2 * P.seeds.card ≤ q
  buffer_margin : η * m ≤ (q : ℝ) / 2
  volume : mainSize + 2 * q = m
  cluster_card : ∀ i, (clusters i).card = m
  cluster_disjoint : ∀ i j, i ≠ j → Disjoint (clusters i) (clusters j)
  shrub_small : ∀ S : ↥P.shrubs, (S.val.card : ℝ) ≤ ε * m
  target_shrub_margin : ∀ S : ↥P.shrubs,
    ((P.farPart S).card : ℝ) ≤ slack / 4 * targetFloor
  capacity : (Fin 2 × I) → I → ℝ
  capacity_nonneg : ∀ a i, 0 ≤ capacity a i
  capacity_regular : ∀ a i, 0 < capacity a i →
    G.IsUniform ε (clusters a.2) (clusters i) ∧
    Disjoint (clusters a.2) (clusters i) ∧
    d ≤ (G.edgeDensity (clusters a.2) (clusters i) : ℝ)
  cluster_budget : ∀ i,
    (∑ S, if head S = i then ((P.nearPart S).card : ℝ) else 0) +
      (∑ a, capacity a i) ≤ mainSize
  group_demand : ∀ a,
    (∑ S, if ShrubState.shrubGroup P head S = a then ((P.farPart S).card : ℝ) else 0) ≤
      (1 - slack) * ∑ i, capacity a i
  group_positive : ∀ S, 0 < ∑ i, capacity (ShrubState.shrubGroup P head S) i
  group_target_margin : ∀ S,
    targetFloor * Fintype.card I ≤ slack / 4 * ∑ i, capacity (ShrubState.shrubGroup P head S) i
  reservoir : I → Finset V
  reservoir_sub : ∀ i, reservoir i ⊆ clusters i
  reservoir_card : ∀ i, (reservoir i).card = q
  privateSet : ↥P.shrubs → Finset V
  private_sub : ∀ S, privateSet S ⊆ clusters (head S)
  private_card : ∀ S, (privateSet S).card = (P.nearPart S).card
  private_disjoint : ∀ S A, S ≠ A → Disjoint (privateSet S) (privateSet A)
  private_reservoir : ∀ S i, Disjoint (privateSet S) (reservoir i)
  private_seed : ∀ S, ∀ v : ↥P.seeds, seed v ∉ privateSet S
  private_adj : ∀ S, ∀ v ∈ privateSet S, G.Adj (seed (roots S).seed) v
  primaryPool : ↥P.shrubs → Finset V
  primary_sub : ∀ S, primaryPool S ⊆ reservoir (head S)
  primary_card : ∀ S, 12 * ε * m ≤ ((primaryPool S).card : ℝ)
  primary_adj : ∀ S, ∀ v ∈ primaryPool S, G.Adj (seed (roots S).seed) v
  secondaryPool : ↥P.shrubs → Finset V
  secondary_sub : ∀ S, secondaryPool S ⊆ reservoir (head S)
  secondary_card : ∀ S, 12 * ε * m ≤ ((secondaryPool S).card : ℝ)
  secondary_adj : ∀ S z, (roots S).second = some z →
    ∀ v ∈ secondaryPool S, G.Adj (seed z.1) v

end Erdos547

import ErdosProblems.Erdos547.PreparedRootSets
import ErdosProblems.Erdos547.ShrubGlobalEmbedding

/-!
# Assembling the explicit shrub host from skew allocations and prepared roots
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

theorem exists_host_setup_of_skew_heads (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : SimpleGraph I) (C Q : I → Finset V) (head : ↥P.shrubs → I)
    (seed : (T.induce (P.seeds : Set U)).Copy G)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val)
    (γ : Fin 2 → ℝ) (σ : ∀ c, DPRS.SkewMatching K (γ c))
    (ε d η s L θ : ℝ) (m M q : ℕ)
    (hε : 0 < ε) (hη : 0 ≤ η) (hs : 0 < s) (hsone : s ≤ 1)
    (hL : 0 < L) (hθ : 0 < θ) (hM : 0 < M) (hγ : ∀ c, 0 < γ c)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η)
    (hεm : 1 ≤ ε * m) (hseed : (P.seeds.card : ℝ) ≤ ε * m)
    (hseedq : 2 * P.seeds.card ≤ q) (hbuffer : η * m ≤ (q : ℝ) / 2)
    (hvolume : M + 2 * q = m) (hsize : ∀ i, (C i).card = m)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsmall : (ℓ : ℝ) ≤ ε * m) (hℓtarget : (ℓ : ℝ) ≤ s / 4 * L)
    (hreg : ∀ i j, K.Adj i j → G.IsUniform ε (C i) (C j) ∧
      Disjoint (C i) (C j) ∧ d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    (hload : ∀ i, (∑ c, (σ c).load i) ≤ 1)
    (hnear : ∀ c i, (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.nearPart S).card : ℝ)) ≤
        (1 - s) * M * (σ c).outLoad i)
    (hfar : ∀ c i, (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.farPart S).card : ℝ)) ≤
        (1 - s) * M * γ c * (σ c).outLoad i)
    (hactive : ∀ S, θ ≤ (σ (P.shrubColour S)).outLoad (head S))
    (htarget : ∀ c, L * Fintype.card I ≤ s / 4 * (γ c * M * θ))
    (hQ : ∀ i, Q i ⊆ C i) (hQsize : ∀ i, (Q i).card = q)
    (roots : ShrubRootSets P G C Q head seed D (12 * ε * m)) :
    Nonempty (ShrubHostSetup P G I) := by
  classical
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hnear' (c : Fin 2) (i : I) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.nearPart S).card : ℝ)) ≤ M * (σ c).outLoad i := by
    apply (hnear c i).trans
    have hh := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith only [hs])
      (mul_nonneg hMreal.le ((σ c).outLoad_nonneg i))
    nlinarith only [hh]
  have hrow (S : ↥P.shrubs) : γ (P.shrubColour S) * M * θ ≤
      ∑ i, DPRS.familyCapacity σ M (ShrubState.shrubGroup P head S) i := by
    change γ (P.shrubColour S) * M * θ ≤
      ∑ i, (σ (P.shrubColour S)).arcCapacity M (head S) i
    rw [DPRS.SkewMatching.arcCapacity_row]
    have hh := mul_le_mul_of_nonneg_left (hactive S)
      (mul_nonneg hMreal.le (hγ (P.shrubColour S)).le)
    simpa only [ShrubState.shrubGroup, mul_comm (γ (P.shrubColour S)) (M : ℝ)] using hh
  refine ⟨{
    clusters := C
    head := head
    seed := seed
    roots := D
    ε := ε
    d := d
    η := η
    slack := s
    targetFloor := L
    m := m
    mainSize := M
    q := q
    ε_pos := hε
    η_nonneg := hη
    slack_pos := hs
    slack_le_one := hsone
    targetFloor_pos := hL
    degree_margin := hde
    embedding_margin := hmargin
    ε_volume := hεm
    seed_small := hseed
    seed_buffer := hseedq
    buffer_margin := hbuffer
    volume := hvolume
    cluster_card := hsize
    cluster_disjoint := hdis
    shrub_small := ?_
    target_shrub_margin := ?_
    capacity := DPRS.familyCapacity σ M
    capacity_nonneg := fun a i ↦ (σ a.1).arcCapacity_nonneg hMreal.le a.2 i
    capacity_regular := fun a i h ↦ hreg a.2 i ((σ a.1).arcCapacity_supported M a.2 i h)
    cluster_budget := P.cluster_budget_of_skew_heads σ M hMreal.le head hload hnear'
    group_demand := P.group_demand_of_skew_heads σ M s head hfar
    group_positive := fun S ↦ (mul_pos (mul_pos (hγ _) hMreal) hθ).trans_le (hrow S)
    group_target_margin := fun S ↦ (htarget (P.shrubColour S)).trans
      (mul_le_mul_of_nonneg_left (hrow S) (div_nonneg hs.le (by norm_num)))
    reservoir := Q
    reservoir_sub := hQ
    reservoir_card := hQsize
    privateSet := roots.privateSet
    private_sub := roots.private_sub
    private_card := roots.private_card
    private_disjoint := fun S A hSA ↦ roots.private_disjoint hSA
    private_reservoir := roots.private_reservoir
    private_seed := roots.private_seed
    private_adj := roots.private_adj
    primaryPool := roots.primary
    primary_sub := roots.primary_sub
    primary_card := roots.primary_card
    primary_adj := roots.primary_adj
    secondaryPool := roots.secondary
    secondary_sub := roots.secondary_sub
    secondary_card := roots.secondary_card
    secondary_adj := roots.secondary_adj
  }⟩
  · intro S
    exact (show (S.val.card : ℝ) ≤ ℓ by exact_mod_cast P.shrub_size S.val S.property).trans hsmall
  · intro S
    have hh : (P.farPart S).card ≤ ℓ :=
      (Finset.card_filter_le _ _).trans (P.shrub_size S.val S.property)
    exact (show ((P.farPart S).card : ℝ) ≤ ℓ by exact_mod_cast hh).trans hℓtarget

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_host_setup_of_skew_heads

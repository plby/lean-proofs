import ErdosProblems.Erdos547.ReducedStructureEmbedding
import ErdosProblems.Erdos547.ShrubScaleNumbers

/-!
# The finite embedding with all allocation parameters constructed
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem scale_pos_of_near_nonempty (c : Fin 2) (hc : (P.nearVertices c).Nonempty) :
    0 < ℓ := by
  classical
  obtain ⟨u, hu⟩ := hc
  obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hu).1
  exact (Finset.card_pos.mpr ⟨u, huC⟩).trans_le
    (P.shrub_size C (Finset.mem_filter.mp hC).1)

theorem isContained_of_coated_reduced_degrees {a : ℝ} (k : EmbeddingConstants a)
    (hT : T.IsTree) (R : EquitableRegularPartition G k.epsilon)
    (n B ρ : ℝ) (hn : 0 < n) (hB : 0 < B) (hρ : 0 < ρ)
    (hcoat : (Fintype.card U : ℝ) ≤ 2 * n)
    (hparts : ∀ c, k.treeEta * n ≤ (P.nearVertices c).card ∧
      k.treeEta * n ≤ (P.farVertices c).card)
    (hvolume : (R.clusterSize : ℝ) * R.clusters.card ≤ 2 * n)
    (hnB : n ≤ 8 * B * R.clusterSize) (htB : (R.clusters.card : ℝ) ≤ B)
    (hclusters : 8 ≤ k.slack * k.treeEta * R.clusters.card)
    (hρsmall : 16 * ρ * B ≤ k.epsilon)
    (hρtarget : 1024 * ρ * B ^ 2 ≤ k.slack ^ 2 * k.treeEta * k.theta)
    (hρvariance : 256 * ρ * B ^ 2 < k.errorFraction ^ 2)
    (hseed : (P.seeds.card : ℝ) ≤ k.epsilon * R.clusterSize)
    (hreservoir : 2 ≤ k.beta * R.clusterSize)
    (hℓ : (ℓ : ℝ) ≤ ρ * Fintype.card U)
    (v₀ : ↥R.clusters)
    (hlarge : ((1 + 10 * k.slack) / R.clusterSize) * Fintype.card U <
      (R.reducedWeights k.density).degree v₀)
    (hminimum : ∀ i, ((1 + 10 * k.slack) / R.clusterSize) * Fintype.card U / 2 <
      (R.reducedWeights k.density).degree i) : T ⊑ G := by
  classical
  let m : ℝ := R.clusterSize
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast R.positive_size
  have hnearR (c : Fin 2) : 0 < ((P.nearVertices c).card : ℝ) :=
    (mul_pos k.treeEta_pos hn).trans_le (hparts c).1
  have hfarR (c : Fin 2) : 0 < ((P.farVertices c).card : ℝ) :=
    (mul_pos k.treeEta_pos hn).trans_le (hparts c).2
  have hnear (c : Fin 2) : 0 < (P.nearVertices c).card := by exact_mod_cast hnearR c
  have hfar (c : Fin 2) : 0 < (P.farVertices c).card := by exact_mod_cast hfarR c
  have hℓpos : 0 < (ℓ : ℝ) := by
    exact_mod_cast P.scale_pos_of_near_nonempty 0 (Finset.card_pos.mp (hnear 0))
  have hpartupper (c : Fin 2) : ((P.nearVertices c).card : ℝ) +
      (P.farVertices c).card ≤ 2 * n := by
    have hh : (P.nearVertices c).card + (P.farVertices c).card ≤ Fintype.card U := by
      rw [P.near_card_add_far_card c]
      exact Finset.card_le_univ _
    exact (show ((P.nearVertices c).card : ℝ) + (P.farVertices c).card ≤ Fintype.card U
      by exact_mod_cast hh).trans hcoat
  have hratio (c : Fin 2) : k.treeEta / 2 ≤ P.partRatio c := by
    apply coated_part_ratio_lower k.treeEta n _ _ k.treeEta_pos.le (hnearR c)
    · have hf : 0 ≤ ((P.farVertices c).card : ℝ) := by positivity
      linarith only [hpartupper c, hf]
    · exact (hparts c).2
  have hℓn : (ℓ : ℝ) ≤ 2 * ρ * n := by
    have hh := mul_le_mul_of_nonneg_left hcoat hρ.le
    nlinarith only [hℓ, hh]
  have hℓm : (ℓ : ℝ) ≤ 16 * ρ * B * m :=
    shrub_cluster_scale ρ n B m ℓ hρ.le hnB hℓn
  have hsmall : (ℓ : ℝ) ≤ k.epsilon * m :=
    hℓm.trans (mul_le_mul_of_nonneg_right hρsmall hm.le)
  obtain ⟨Q⟩ := exists_reservoir_numbers k R.clusterSize R.positive_size hreservoir
  let scale : ℝ := (1 + 10 * k.slack) / m
  let A : Fin 2 → ℝ := fun c ↦ (1 - k.slack) * scale * (P.nearVertices c).card
  let L : ℝ := 4 * ℓ / k.slack
  have hscale : 0 < scale := div_pos (by linarith only [k.slack_pos]) hm
  have hsone : k.slack < 1 := by linarith only [k.slack_le]
  have hA (c : Fin 2) : 0 < A c :=
    mul_pos (mul_pos (sub_pos.mpr hsone) hscale) (hnearR c)
  have hL : 0 < L := div_pos (mul_pos (by norm_num) hℓpos) k.slack_pos
  have hmean (c : Fin 2) : ((P.nearVertices c).card : ℝ) / A c + k.slack * Q.main ≤
      (1 - k.slack) * Q.main :=
    relative_allocation_mean k.slack k.beta m Q.main (P.nearVertices c).card
      k.slack_pos.le k.slack_le k.beta_pos.le k.beta_slack hm (hnearR c) Q.main_lower
  have hεm : 1 ≤ k.epsilon * m := by
    have hseedpos : 1 ≤ P.seeds.card := Finset.card_pos.mpr ⟨r, P.root_mem⟩
    have hh : (1 : ℝ) ≤ P.seeds.card := by exact_mod_cast hseedpos
    exact hh.trans hseed
  have hseedForest : (P.seeds.card : ℝ) ≤
      (k.density - 2 * k.epsilon - 2 * k.delta) * m := by
    have hh := mul_le_mul_of_nonneg_right k.seed_margin hm.le
    nlinarith only [hseed, hh]
  apply P.isContained_of_reduced_degrees hT R k.delta k.density (k.beta / 4)
    k.slack L k.theta (k.errorFraction * m) scale A Q.main Q.q
    k.epsilon_pos k.delta_pos k.epsilon_delta (by linarith only [k.epsilon_le]) k.clean
    (div_nonneg k.beta_pos.le (by norm_num)) k.slack_pos hsone.le hL k.theta_pos
    (mul_nonneg k.errorFraction_pos.le hm.le) hA hscale Q.main_pos hnear hfar v₀
    hlarge hminimum k.degree_margin k.embedding_margin k.private_margin hεm hseed
    (Q.seeds_fit P.seeds.card hseed) Q.buffer Q.volume hsmall
  · dsimp only [L]
    have hs := k.slack_pos.ne'
    field_simp
    ring_nf
    exact le_rfl
  · intro c
    exact allowed_head_mass_margin k.slack k.treeEta k.theta k.delta n m R.clusters.card
      (P.nearVertices c).card k.slack_pos.le k.treeEta_pos.le hm (by positivity)
      (hnearR c).le hvolume (hparts c).1 k.exception_margin hclusters
  · intro c
    exact shrub_variance_margin ρ n B m ℓ
      (((P.nearVertices c).card : ℝ) + (P.farVertices c).card) k.errorFraction
      hρ.le hB.le hm hℓpos.le (by positivity) hnB hℓm (hpartupper c) hρvariance
  · exact hmean
  · intro c
    exact relative_far_mean_of_near k.slack Q.main (P.nearVertices c).card
      (P.farVertices c).card (A c) (hnearR c) (hfarR c).le (hA c) (hmean c)
  · exact k.rounding_error_near m Q.main hm.le Q.main_half
  · intro c
    exact k.rounding_error_far m Q.main (P.partRatio c) hm.le Q.main_half (hratio c)
  · intro c
    exact shrub_target_margin k.slack k.treeEta k.theta ρ B m Q.main R.clusters.card ℓ
      (P.partRatio c) k.slack_pos k.treeEta_pos.le k.theta_pos.le hρ.le hB.le hm.le
      (by positivity) htB Q.main_half (hratio c) hℓm hρtarget
  · exact Q.main_typical
  · exact Q.reservoir_typical
  · exact hseedForest
  · exact Q.roots

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.isContained_of_coated_reduced_degrees

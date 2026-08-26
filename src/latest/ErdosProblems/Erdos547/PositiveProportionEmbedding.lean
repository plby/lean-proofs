import ErdosProblems.Erdos547.CoatedReducedEmbedding
import ErdosProblems.Erdos547.UniformEmbeddingNumbers
import ErdosProblems.Erdos547.StrongRegularity
import ErdosProblems.Erdos547.TreeCoating

/-!
# Uniform positive-proportion tree embedding

Every constant is selected before the guest tree and the host graph.  The
regularity bound is selected before the shrub fraction and seed bound.
-/

namespace Erdos547

open Finset SimpleGraph

universe u v

theorem eventually_positive_proportion_tree_embedding (a : ℝ) (ha : 0 < a) (haone : a ≤ 1) :
    ∃ n₀ : ℕ, ∀ (U : Type u) (V : Type v) [Fintype U] [Fintype V]
      [DecidableEq U] [DecidableEq V] (T : SimpleGraph U) [DecidableRel T.Adj]
      (G : SimpleGraph V) [DecidableRel G.Adj], T.IsTree → n₀ ≤ Fintype.card U →
      (Fintype.card U : ℝ) / 4 ≤ Fintype.card V →
      (Fintype.card V : ℝ) ≤ 2 * Fintype.card U →
      (∀ v, (1 + a) * ((Fintype.card U : ℝ) - 1) / 2 ≤ (G.degree v : ℝ)) →
      ∀ H : Finset V,
        (∀ v ∈ H, (1 + a) * ((Fintype.card U : ℝ) - 1) ≤ (G.degree v : ℝ)) →
        a * Fintype.card V ≤ (H.card : ℝ) → T ⊑ G := by
  classical
  obtain ⟨k⟩ := nonempty_embedding_constants a ha haone
  obtain ⟨l, hl, hla, hlparts⟩ := exists_embedding_cluster_lower k ha
  obtain ⟨M, nReg, hregular⟩ := eventually_equitable_regular_partition.{v} k.epsilon
    k.epsilon_pos (by linarith only [k.epsilon_le]) l hl
  let B : ℝ := (M : ℝ) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨ρ, hρ, hρη, hρsmall, hρtarget, hρvariance⟩ := k.exists_shrub_fraction B hB
  obtain ⟨K, nCoat, hcoating⟩ := eventually_tree_coating.{u} k.treeEta ρ hρ hρη k.treeEta_le
  obtain ⟨n₀, hn₀, hnCoat, hnReg, hnumbers⟩ :=
    exists_embedding_order_threshold k ha B hB K nCoat nReg
  refine ⟨n₀, ?_⟩
  intro U V instU instV instEqU instEqV T instT G instG hT hn hhostLower hhostUpper
    hminimum H hH hHcard
  let n : ℝ := Fintype.card U
  have hnposNat : 0 < Fintype.card U := hn₀.trans hn
  have hnpos : 0 < n := by dsimp only [n]; exact_mod_cast hnposNat
  have hhostpos : 0 < Fintype.card V := by
    have hh : 0 < (Fintype.card V : ℝ) := (div_pos hnpos (by norm_num)).trans_le hhostLower
    exact_mod_cast hh
  have hRegOrder : nReg ≤ Fintype.card V := by
    have hh : (4 : ℝ) * nReg ≤ n := by
      dsimp only [n]
      exact_mod_cast hnReg.trans hn
    have hc : (nReg : ℝ) ≤ Fintype.card V := by linarith only [hh, hhostLower]
    exact_mod_cast hc
  obtain ⟨R, htLower, htUpper⟩ := hregular V G hRegOrder
  have htB : (R.clusters.card : ℝ) ≤ B := by
    have hh : (R.clusters.card : ℝ) ≤ M := by exact_mod_cast htUpper
    dsimp only [B]
    linarith only [hh]
  have hnB : n ≤ 8 * B * R.clusterSize :=
    R.order_le_cluster_scale k.epsilon_le n B hhostLower htB
  have hsizeNumbers := hnumbers (Fintype.card U) hn
  have hclusterNumbers := hsizeNumbers.2 R.clusterSize hnB
  have htLowerR : (l : ℝ) ≤ R.clusters.card := by exact_mod_cast htLower
  have hclusters : 8 ≤ k.slack * k.treeEta * R.clusters.card :=
    hlparts.trans (mul_le_mul_of_nonneg_left htLowerR (mul_nonneg k.slack_pos.le k.treeEta_pos.le))
  have hclustersDegree : 32 ≤ a * R.clusters.card :=
    hla.trans (mul_le_mul_of_nonneg_left htLowerR ha.le)
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨p, ℓ, P, hTree, hcopy, hseeds, hcoated, hℓ, hparts⟩ :=
    hcoating U T hT r (hnCoat.trans hn)
  have hcoatedTwo : (Fintype.card (CoatedVertex U p) : ℝ) ≤ 2 * n := by
    have hh := mul_le_mul_of_nonneg_right k.treeEta_le hnpos.le
    nlinarith only [hcoated, hh]
  have hvolume : (R.clusterSize : ℝ) * R.clusters.card ≤ 2 * n :=
    (show (R.clusterSize : ℝ) * R.clusters.card ≤ Fintype.card V by
      exact_mod_cast R.cluster_volume_le).trans hhostUpper
  obtain ⟨v₀, hlarge, hsmallDegree⟩ := R.exists_strict_reduced_degrees k n
    (Fintype.card (CoatedVertex U p)) ha haone hnpos hhostpos hhostUpper hcoated
    hclustersDegree hsizeNumbers.1 hminimum H hH hHcard
  have hseedBound : (P.seeds.card : ℝ) ≤ k.epsilon * R.clusterSize :=
    (show (P.seeds.card : ℝ) ≤ K by exact_mod_cast hseeds).trans hclusterNumbers.1
  exact hcopy.trans (P.isContained_of_coated_reduced_degrees k hTree R n B ρ
    hnpos hB hρ hcoatedTwo hparts hvolume hnB htB hclusters hρsmall hρtarget hρvariance
    hseedBound hclusterNumbers.2 hℓ v₀ hlarge hsmallDegree)

end Erdos547

#print axioms Erdos547.eventually_positive_proportion_tree_embedding

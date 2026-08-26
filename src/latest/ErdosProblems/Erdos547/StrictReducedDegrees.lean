import ErdosProblems.Erdos547.EmbeddingConstants
import ErdosProblems.Erdos547.ReducedMaximumDegree

/-!
# Strict reduced degrees from the positive-proportion host hypotheses
-/

namespace Erdos547.EquitableRegularPartition

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {a : ℝ}

theorem exists_strict_reduced_degrees (k : EmbeddingConstants a)
    (R : EquitableRegularPartition G k.epsilon) (n N : ℝ)
    (ha : 0 < a) (haone : a ≤ 1) (hn : 0 < n)
    (hhostpos : 0 < Fintype.card V) (hhost : (Fintype.card V : ℝ) ≤ 2 * n)
    (hcoat : N ≤ (1 + 10 * k.treeEta) * n)
    (hclusters : 32 ≤ a * R.clusters.card) (hnlarge : 8 ≤ a * n)
    (hminimum : ∀ v, (1 + a) * (n - 1) / 2 ≤ (G.degree v : ℝ))
    (H : Finset V) (hH : ∀ v ∈ H, (1 + a) * (n - 1) ≤ (G.degree v : ℝ))
    (hHcard : a * Fintype.card V ≤ (H.card : ℝ)) :
    ∃ v₀ : ↥R.clusters,
      ((1 + 10 * k.slack) / R.clusterSize) * N < (R.reducedWeights k.density).degree v₀ ∧
      ∀ i, ((1 + 10 * k.slack) / R.clusterSize) * N / 2 <
        (R.reducedWeights k.density).degree i := by
  have hm : 0 < (R.clusterSize : ℝ) := by exact_mod_cast R.positive_size
  have hhostposR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hhostpos
  have hHlarge : (k.epsilon + k.delta) * Fintype.card V < (H.card : ℝ) :=
    (mul_lt_mul_of_pos_right k.high_fraction hhostposR).trans_le hHcard
  obtain ⟨v₀, hv₀⟩ := R.exists_reduced_high_degree k.epsilon_pos.le
    (by linarith only [k.epsilon_le]) k.density k.density_pos.le k.delta k.delta_pos
    k.epsilon_delta ((1 + a) * (n - 1)) H hH hHlarge
  have hvolume : (R.clusterSize : ℝ) * R.clusters.card ≤ 2 * n :=
    (show (R.clusterSize : ℝ) * R.clusters.card ≤ Fintype.card V by
      exact_mod_cast R.cluster_volume_le).trans hhost
  have htarget : (1 + 10 * k.slack) * N ≤ (1 + a / 4) * n := by
    have hscale := coating_scale_bound a k.slack k.treeEta ha.le k.slack_pos.le
      k.treeEta_pos.le k.slack_surplus k.treeEta_surplus k.treeEta_le
    have hc := mul_le_mul_of_nonneg_left hcoat
      (show 0 ≤ 1 + 10 * k.slack by linarith only [k.slack_pos])
    have hs := mul_le_mul_of_nonneg_right hscale hn.le
    nlinarith only [hc, hs]
  have hsurplus (i : ↥R.clusters) := degree_surplus_after_losses a n (Fintype.card V)
    R.clusterSize R.clusters.card k.epsilon k.density k.delta ((1 + 10 * k.slack) * N)
    ((R.reducedWeights k.density).degree v₀) ((R.reducedWeights k.density).degree i)
    ha haone hn hm.le k.epsilon_pos.le k.density_pos.le k.delta_pos.le hhost hvolume
    k.degree_loss hclusters hnlarge htarget hv₀
    (R.reduced_min_degree_lower k.epsilon_pos.le k.density k.density_pos.le
      ((1 + a) * (n - 1) / 2) hminimum i)
  refine ⟨v₀, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hm).mpr
    nlinarith only [(hsurplus v₀).1]
  · intro i
    rw [div_mul_eq_mul_div, div_div]
    apply (div_lt_iff₀ (mul_pos hm (by norm_num))).mpr
    nlinarith only [(hsurplus i).2]

end Erdos547.EquitableRegularPartition

#print axioms Erdos547.EquitableRegularPartition.exists_strict_reduced_degrees

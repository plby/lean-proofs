import ErdosProblems.Erdos547.EquitableRegularPartition
import ErdosProblems.Erdos547.RegularityClusterCleaning
import ErdosProblems.Erdos547.TrimmedClusterRegularity

/-!
# Assembling a regular equitable partition after cleaning and trimming
-/

namespace Erdos547

open Finset SimpleGraph

theorem regular_partition_of_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (δ ε : ℝ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hδε : 2 * δ ≤ ε)
    (hslice : 2 * δ ^ 2 ≤ ε) (hε : ε ≤ 1)
    (P : Finpartition (Finset.univ : Finset V)) (hequip : P.IsEquipartition)
    (hreg : P.IsUniform G (δ ^ 2)) (ht : 1 ≤ P.parts.card)
    (hsmall : (P.parts.card : ℝ) ≤ δ * Fintype.card V) :
    ∃ Q : EquitableRegularPartition G ε,
      Q.clusters.card ≤ P.parts.card ∧ P.parts.card ≤ 2 * Q.clusters.card := by
  classical
  obtain ⟨J, hJ, hdrop, hhalf, hrow⟩ := exists_cluster_clean_subfamily G P δ hδ hδhalf hreg
  obtain ⟨m, hm, hmn, hnm, C, hC, hdis⟩ := exists_equal_cluster_trimming P hequip ht J hJ
  have hsize (i : ↥J) : (C i).card = m := (hC i).2.1
  have hpos (i : ↥J) : 1 ≤ (C i).card := (hsize i).symm ▸ hm
  have hbad0 := trimmed_cluster_bad_count_le G J C (fun i ↦ (hC i).1)
    (fun i ↦ (hC i).2.2) hpos (δ ^ 2) ε (2 * δ * J.card) hslice hε hrow
  have hbad : ∀ i : ↥J, (((Finset.univ : Finset ↥J).filter
      (fun j ↦ i ≠ j ∧ ¬ G.IsUniform ε (C i) (C j))).card : ℝ) ≤ ε * Fintype.card ↥J := by
    intro i
    have hh := mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg J.card)
    have hbound : (2 : ℝ) * δ * J.card ≤ ε * Fintype.card ↥J := by simpa using hh
    exact (hbad0 i).trans hbound
  have hcount := card_outside_clusters C hdis m hsize
  have hcount' : (Finset.univ \ Finset.univ.biUnion C).card + m * J.card = Fintype.card V := by
    simpa using hcount
  have hdrop' : ((P.parts.card - J.card : ℕ) : ℝ) ≤ δ * P.parts.card := by
    rwa [Finset.card_sdiff_of_subset hJ] at hdrop
  have hgarbage0 := discarded_vertices_bound δ hδ.le (Fintype.card V) m P.parts.card J.card
    (Finset.univ \ Finset.univ.biUnion C).card hmn hnm (Finset.card_le_card hJ) hcount' hdrop' hsmall
  have hgarbage : ((Finset.univ \ Finset.univ.biUnion C).card : ℝ) ≤ ε * Fintype.card V :=
    hgarbage0.trans (by
      have hh := mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg (Fintype.card V))
      nlinarith only [hh])
  obtain ⟨Q, hQcard, _⟩ := regular_partition_of_equal_family G ε C m hm hsize hdis hgarbage hbad
  have he : Q.clusters.card = J.card := by simpa using hQcard
  refine ⟨Q, ?_, ?_⟩
  · rw [he]
    exact Finset.card_le_card hJ
  · rw [he]
    exact_mod_cast hhalf

end Erdos547

#print axioms Erdos547.regular_partition_of_uniform

import ErdosProblems.Erdos547.ClusterDegrees
import ErdosProblems.Erdos547.RegularityUpperTypical

/-!
# A high-degree host vertex typical to almost all of its regular partners
-/

noncomputable section

namespace Erdos547.EquitableRegularPartition

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}
variable (P : EquitableRegularPartition G ε)

def upperExceptionalPairs (X : Finset V) (v : V) : Finset (Finset V) :=
  P.clusters.filter (fun Y ↦ G.IsUniform ε X Y ∧
    ((G.edgeDensity X Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ))

def upperExceptionalVertices (δ : ℝ) (X : Finset V) : Finset V :=
  X.filter (fun v ↦ δ * P.clusters.card < ((P.upperExceptionalPairs X v).card : ℝ))

theorem card_upperExceptionalVertices_le (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) (X : Finset V) :
    ((P.upperExceptionalVertices δ X).card : ℝ) ≤ δ * X.card := by
  classical
  unfold upperExceptionalVertices upperExceptionalPairs
  refine card_many_incidents_le (fun v Y ↦ G.IsUniform ε X Y ∧
    ((G.edgeDensity X Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ))
      X P.clusters ε δ hδ hεδ ?_
  intro Y _
  by_cases hr : G.IsUniform ε X Y
  · have hcol := card_upper_nonTypical_le G hr (Finset.Subset.refl Y)
      (show (Y.card : ℝ) * ε ≤ Y.card by
        simpa using mul_le_mul_of_nonneg_left hεone (Nat.cast_nonneg Y.card))
    simpa only [hr, true_and, mul_comm ε] using hcol
  · simp only [hr, false_and, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε (Nat.cast_nonneg _)

def upperExceptionalSet (δ : ℝ) : Finset V :=
  (Finset.univ \ P.clusters.biUnion id) ∪
    P.clusters.biUnion (P.upperExceptionalVertices δ)

theorem card_upperExceptionalSet_le (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) :
    ((P.upperExceptionalSet δ).card : ℝ) ≤ (ε + δ) * Fintype.card V := by
  classical
  have hsum : (∑ X ∈ P.clusters, ((P.upperExceptionalVertices δ X).card : ℝ)) ≤
      δ * ((P.clusterSize : ℝ) * P.clusters.card) := by
    calc
      _ ≤ ∑ X ∈ P.clusters, δ * X.card :=
        Finset.sum_le_sum fun X _ ↦ P.card_upperExceptionalVertices_le hε hεone δ hδ hεδ X
      _ = ∑ _X ∈ P.clusters, δ * P.clusterSize := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [P.equal_size X hX]
      _ = _ := by simp; ring
  have hunion : ((P.clusters.biUnion (P.upperExceptionalVertices δ)).card : ℝ) ≤
      ∑ X ∈ P.clusters, ((P.upperExceptionalVertices δ X).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := P.clusters)
      (t := P.upperExceptionalVertices δ))
  have hvol : (P.clusterSize : ℝ) * P.clusters.card ≤ Fintype.card V := by
    exact_mod_cast P.cluster_volume_le
  have hdiscard := P.discarded_bound
  have hall : ((P.upperExceptionalSet δ).card : ℝ) ≤
      (Finset.univ \ P.clusters.biUnion id).card +
        ((P.clusters.biUnion (P.upperExceptionalVertices δ)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (Finset.univ \ P.clusters.biUnion id)
      (P.clusters.biUnion (P.upperExceptionalVertices δ))
  have hδvol := mul_le_mul_of_nonneg_left hvol hδ.le
  nlinarith only [hsum, hunion, hdiscard, hall, hδvol]

theorem exists_high_upper_typical_vertex (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2) (D : ℝ)
    (H : Finset V) (hH : ∀ v ∈ H, D ≤ (G.degree v : ℝ))
    (hHcard : (ε + δ) * Fintype.card V < (H.card : ℝ)) :
    ∃ X : ↥P.clusters, ∃ v ∈ X.val, D ≤ (G.degree v : ℝ) ∧
      ((P.upperExceptionalPairs X.val v).card : ℝ) ≤ δ * P.clusters.card := by
  classical
  have hnsub : ¬ H ⊆ P.upperExceptionalSet δ := by
    intro hsub
    have hh : (H.card : ℝ) ≤ (P.upperExceptionalSet δ).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact (not_le_of_gt hHcard) (hh.trans (P.card_upperExceptionalSet_le hε hεone δ hδ hεδ))
  obtain ⟨v, hvH, hvbad⟩ := Finset.not_subset.mp hnsub
  have hvunion : v ∈ P.clusters.biUnion id := by
    by_contra hn
    exact hvbad (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))
  obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.mp hvunion
  refine ⟨⟨X, hX⟩, v, hvX, hH v hvH, ?_⟩
  by_contra hn
  have hbad : v ∈ P.upperExceptionalVertices δ X :=
    Finset.mem_filter.mpr ⟨hvX, lt_of_not_ge hn⟩
  exact hvbad (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨X, hX, hbad⟩))

end Erdos547.EquitableRegularPartition

#print axioms Erdos547.EquitableRegularPartition.exists_high_upper_typical_vertex

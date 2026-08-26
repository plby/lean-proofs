/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceTwoSidedRows
import ErdosProblems.Erdos547b.SourceThresholdGraphs

/-! # Physical pair densities and realized source entries agree on good targets -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePhysicalRowError

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceTwoSidedRows Erdos547b.ZhaoSourceThresholdGraphs
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoRichClaim61Lemma611

theorem normalized_count_error (N d ε : ℝ) (count : ℕ) (hN : 0 < N) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hlower : (d - ε) * N ≤ count)
    (hupper : 0 < count → (count : ℝ) ≤ (d + ε) * N) :
    |(count : ℝ) / N - d| ≤ ε := by
  have hu : (count : ℝ) ≤ (d + ε) * N := by
    by_cases hc : 0 < count
    · exact hupper hc
    · have hc0 : count = 0 := by omega
      rw [hc0, Nat.cast_zero]
      exact mul_nonneg (add_nonneg hd hε) hN.le
  have hlo : d - ε ≤ (count : ℝ) / N := (le_div_iff₀ hN).mpr hlower
  have hhi : (count : ℝ) / N ≤ d + ε := (div_le_iff₀ hN).mpr hu
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi]

theorem source_gap_of_physical_gap {a b a' b' ε η : ℝ}
    (ha : |a - a'| ≤ ε) (hb : |b - b'| ≤ ε)
    (hε : 2 * ε ≤ η) (hgap : 2 * η ≤ |a' - b'|) : η ≤ |a - b| := by
  have h₁ := abs_sub_le a' a b'
  have h₂ := abs_sub_le a b b'
  rw [abs_sub_comm a' a] at h₁
  linarith only [h₁, h₂, ha, hb, hε, hgap]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : TwoSidedSource W Q)

theorem source_density_error_A (hα : 0 < α)
    {j : Index W} (hjA : j ≠ Q.A) (hjB : j ≠ Q.B) (hj : j ∉ S.badA) :
    |rootDensity W S.clean (Sum.inl Q.A) (Sum.inl j) -
      density W (Sum.inl Q.A) (Sum.inl j)| ≤ (epsilon α : ℝ) := by
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hcluster : clusterVertices (assignment W) j = j.val :=
    clusterVertices_partitionAssignment W.exceptional W.partition j
  have heq : rootDensity W S.clean (Sum.inl Q.A) (Sum.inl j) =
      (degreeInto S.clean.source S.clean.zA (clusterVertices (assignment W) j) : ℝ) / W.clusterSize := by
    simp only [rootDensity, twoRootSourceDensity_row_A, rootedSourceDensity, padCluster, hcluster]
  rw [heq]
  simp only [density, clusterVertices_padAssignment_inl]
  apply normalized_count_error _ _ _ _ hN
    (by
      exact_mod_cast (host W).edgeDensity_nonneg
        (clusterVertices (assignment W) Q.A) (clusterVertices (assignment W) j)) hε
    (S.lowerA j hjA hjB hj)
  intro hpos
  have h := S.clean.upperA j hjA hjB hpos
  have hcard : (clusterVertices (assignment W) j).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters j.val j.property
  simpa only [hcard] using h

theorem source_density_error_B (hα : 0 < α)
    {j : Index W} (hjA : j ≠ Q.A) (hjB : j ≠ Q.B) (hj : j ∉ S.badB) :
    |rootDensity W S.clean (Sum.inl Q.B) (Sum.inl j) -
      density W (Sum.inl Q.B) (Sum.inl j)| ≤ (epsilon α : ℝ) := by
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hcluster : clusterVertices (assignment W) j = j.val :=
    clusterVertices_partitionAssignment W.exceptional W.partition j
  have heq : rootDensity W S.clean (Sum.inl Q.B) (Sum.inl j) =
      (degreeInto S.clean.source S.clean.zB (clusterVertices (assignment W) j) : ℝ) / W.clusterSize := by
    have hAB : (Sum.inl Q.A : EvenPadding (Index W)) ≠ Sum.inl Q.B :=
      fun h => Q.adj.ne (Sum.inl.inj h)
    rw [rootDensity, twoRootSourceDensity_row_B _ _ _ _ _ _ _ hAB]
    simp only [rootedSourceDensity, padCluster, hcluster]
  rw [heq]
  simp only [density, clusterVertices_padAssignment_inl]
  apply normalized_count_error _ _ _ _ hN
    (by
      exact_mod_cast (host W).edgeDensity_nonneg
        (clusterVertices (assignment W) Q.B) (clusterVertices (assignment W) j)) hε
    (S.lowerB j hjA hjB hj)
  intro hpos
  have h := S.clean.upperB j hjA hjB hpos
  have hcard : (clusterVertices (assignment W) j).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters j.val j.property
  simpa only [hcard] using h

end Erdos547b.ZhaoSourcePhysicalRowError

#print axioms Erdos547b.ZhaoSourcePhysicalRowError.source_gap_of_physical_gap
#print axioms Erdos547b.ZhaoSourcePhysicalRowError.source_density_error_A
#print axioms Erdos547b.ZhaoSourcePhysicalRowError.source_density_error_B

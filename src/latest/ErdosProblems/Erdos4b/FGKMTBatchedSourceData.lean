/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceBatchPartition

/-! # Constructed regular arithmetic data with nonempty geometric prime batches -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter FiniteEdgeFamily

structure SourceGeometricPartition {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) where
  assignment : commonPinnedPrimeSet (x / 2) x → Option (Fin (sourceBatchCount x))
  degree_error : ∀ q ∈ H.edgeFamily.vertices, ∀ j : Fin (sourceBatchCount x),
    |(H.edgeFamily.restrictLabels (batchLabels assignment j)).degree q - geometricBatchTarget j| <
      2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2)
  labels_nonempty : ∀ j : Fin (sourceBatchCount x), (batchLabels assignment j).Nonempty

theorem exists_batchedSourceData {a e : ℝ} (ha : 0 < a) (hepos : 0 < e) (he : e ≤ 1 / 120) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ (D : SourceProbabilityData c e x)
        (b : ResidueAssignment (sourceSmallPrimes a x)) (H : RegularSourceConditions D a b),
        2 * Real.log 5 ≤ D.expectedDegreeScale (sourceSmallPrimes a x) ∧
        D.expectedDegreeScale (sourceSmallPrimes a x) ≤ K ∧
        Nonempty (SourceGeometricPartition H) := by
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  obtain ⟨c, K, hc, hK, hdata⟩ := exists_regularSourceData_with_degree_range
    (T := 2 * Real.log 5) ha (mul_pos (by norm_num) hlog5) hepos he
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [hdata, eventually_source_geometric_partition] with x hx hpartition
  obtain ⟨D, b, H, hlo, hhi⟩ := hx
  obtain ⟨z, hdegree, hnonempty⟩ := hpartition a c e D b H (by linarith)
  exact ⟨D, b, H, hlo, hhi,
    ⟨{ assignment := z, degree_error := hdegree, labels_nonempty := hnonempty }⟩⟩

end

end Erdos4b.FGKMT

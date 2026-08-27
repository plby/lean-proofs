/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceBatchFamily
import ErdosProblems.Erdos4b.FGKMTSourceSurvivalBudget

/-! # Verified survival and degree bounds for every constructed source partition -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

namespace SourceGeometricPartition

variable {a c e : ℝ} {x : ℕ} {D : SourceProbabilityData c e x}
  {b : ResidueAssignment (sourceSmallPrimes a x)} {H : RegularSourceConditions D a b}
  (B : SourceGeometricPartition H)

theorem survival_error {j : ℕ} (hj : j ≤ sourceBatchCount x)
    {q : ℕ} (hq : q ∈ H.edgeFamily.vertices) :
    |coveringSurvival B.family j q - geometricSurvival j| ≤
      (j : ℝ) * (2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2)) :=
  coveringSurvival_geometric_error B.family q
    (fun _ hk => B.family_degree_error hk hq) hj

structure SurvivalBounds : Prop where
  lower : ∀ j ≤ sourceBatchCount x, ∀ q ∈ H.edgeFamily.vertices,
    sourceSurvivalFloor x ≤ coveringSurvival B.family j q
  degree_bound : ∀ j < sourceBatchCount x, ∀ q ∈ H.edgeFamily.vertices,
    (B.family j).degree q ≤ 4 * coveringSurvival B.family j q
  final_upper : ∀ q ∈ H.edgeFamily.vertices,
    coveringSurvival B.family (sourceBatchCount x) q ≤
      (5 / 4 : ℝ) * geometricSurvival (sourceBatchCount x)

theorem survivalBounds_of_budget
    (hbudget : ((sourceBatchCount x : ℝ) + 1) *
      (2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2)) ≤
        geometricSurvival (sourceBatchCount x) / 4) : B.SurvivalBounds := by
  have hε : 0 ≤ 2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro j hj q hq
    exact coveringSurvival_geometric_lower B.family q hε
      (fun k hk => B.family_degree_error hk hq) hbudget hj
  · intro j hj q hq
    exact coveringSurvival_geometric_degree B.family q hε
      (fun k hk => B.family_degree_error hk hq) hbudget hj
  · intro q hq
    exact (coveringSurvival_geometric_bounds B.family q hε
      (fun k hk => B.family_degree_error hk hq) hbudget le_rfl).2

end SourceGeometricPartition

theorem eventually_source_survival_bounds :
    ∀ᶠ x : ℕ in atTop, ∀ (a c e : ℝ) (D : SourceProbabilityData c e x)
      (b : ResidueAssignment (sourceSmallPrimes a x)) (H : RegularSourceConditions D a b)
      (B : SourceGeometricPartition H), B.SurvivalBounds := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    eventually_source_survival_error_budget] with x hx a c e D b H B
  exact B.survivalBounds_of_budget hx

end

end Erdos4b.FGKMT

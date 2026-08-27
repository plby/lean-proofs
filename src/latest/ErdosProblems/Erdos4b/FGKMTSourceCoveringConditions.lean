/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSurvival
import ErdosProblems.Erdos4b.FGKMTSourceCoveringSmallness
import ErdosProblems.Erdos4b.FGKMTCoveringConditions

/-! # All finite-covering hypotheses for the actual arithmetic source -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_source_covering_conditions :
    ∀ᶠ x : ℕ in atTop, ∀ (a c e : ℝ) (D : SourceProbabilityData c e x)
      (b : ResidueAssignment (sourceSmallPrimes a x)) (H : RegularSourceConditions D a b)
      (B : SourceGeometricPartition H),
      CoveringConditions B.family H.edgeFamily.vertices D.dimension
        (sourceCoveringSize D.dimension x) (sourceBatchCount x)
        (sourceSurvivalFloor x) ((x : ℝ) ^ (-1 / 20 : ℝ)) 4 := by
  filter_upwards [eventually_source_survival_bounds,
    tendsto_natCast_atTop_atTop.eventually eventually_source_covering_smallness,
    eventually_ge_atTop (1 : ℕ)] with x hsurv hsmall hx a c e D b H B
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx1
  have hs := hsurv a c e D b H B
  refine {
    size_pos := by unfold sourceCoveringSize; omega
    degree_ge_one := by norm_num
    survival_pos := sourceSurvivalFloor_pos x
    survival_le_one := (sourceSurvivalFloor_le_half x).trans (by norm_num)
    error_pos := Real.rpow_pos_of_pos hx0 _
    smallness := hsmall D.dimension ?_
    vertices_eq := fun j _ => B.family_vertices j
    rank_le := fun j _ => (B.family_rank j).le
    labels_pos := fun _ hj => B.labels_card_pos hj
    survival_lower := hs.lower
    degree_bound := hs.degree_bound
    codegree_bound := fun j _ _ hq _ hq' hne => B.family_codegree_le j hq hq' hne.symm
    vertex_bound := ?_ }
  · rw [D.dimension_eq]
    exact growingSieveDimension_le x
  · intro j hj p q _
    exact (B.family_vertexMass_le j p q).trans
      (source_normalized_sparsity hx1 (B.labels_card_pos hj)
        (by exact_mod_cast B.labels_card_le j))

end

end Erdos4b.FGKMT

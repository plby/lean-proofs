/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceCoveringConditions
import ErdosProblems.Erdos4b.FGKMTCoveringFinalTolerance
import ErdosProblems.Erdos4b.FGKMTCoveringRealization

/-! # Constructed supported histories with the source survivor bound -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

namespace SourceGeometricPartition

variable {a c e : ℝ} {x : ℕ} {D : SourceProbabilityData c e x}
  {b : ResidueAssignment (sourceSmallPrimes a x)} {H : RegularSourceConditions D a b}
  (B : SourceGeometricPartition H)

structure CoveringWitness where
  conditions : CoveringConditions B.family H.edgeFamily.vertices D.dimension
    (sourceCoveringSize D.dimension x) (sourceBatchCount x)
    (sourceSurvivalFloor x) ((x : ℝ) ^ (-1 / 20 : ℝ)) 4
  history : CoverHistory (fun j => B.labels j)
    (fun _ => integerWeightWindow (sourceIntervalLength c x)) (sourceBatchCount x)
  mass_pos : 0 < coveringHistoryMass B.family H.edgeFamily.vertices
    ((x : ℝ) ^ (-1 / 20 : ℝ)) (sourceBatchCount x) history
  remaining_le :
    ((coveringRemaining B.family H.edgeFamily.vertices (sourceBatchCount x) history).card : ℝ) ≤
      2 * geometricSurvival (sourceBatchCount x) * H.edgeFamily.vertices.card

theorem exists_coveringWitness (hS : B.SurvivalBounds)
    (hC : CoveringConditions B.family H.edgeFamily.vertices D.dimension
      (sourceCoveringSize D.dimension x) (sourceBatchCount x)
      (sourceSurvivalFloor x) ((x : ℝ) ^ (-1 / 20 : ℝ)) 4) :
    Nonempty B.CoveringWitness := by
  have hsize : 1 + 2 * D.dimension * sourceBatchCount x ≤ sourceCoveringSize D.dimension x := by
    unfold sourceCoveringSize
    omega
  obtain ⟨s, hs, hbound⟩ := hC.exists_supported_covering_history hsize
  have hsum : (∑ q ∈ H.edgeFamily.vertices, coveringSurvival B.family (sourceBatchCount x) q) ≤
      (5 / 4 : ℝ) * geometricSurvival (sourceBatchCount x) * H.edgeFamily.vertices.card := by
    calc
      _ ≤ ∑ _q ∈ H.edgeFamily.vertices,
          (5 / 4 : ℝ) * geometricSurvival (sourceBatchCount x) :=
        Finset.sum_le_sum (fun q hq => hS.final_upper q hq)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hsum0 : 0 ≤ ∑ q ∈ H.edgeFamily.vertices,
      coveringSurvival B.family (sourceBatchCount x) q :=
    Finset.sum_nonneg (fun q _ => (coveringSurvival_pos B.family _ q).le)
  have htol : 1 + coveringTolerance ((x : ℝ) ^ (-1 / 20 : ℝ)) (sourceBatchCount x + 1) ≤
      (3 / 2 : ℝ) := by linarith [hC.final_tolerance_le_half]
  refine ⟨{ conditions := hC, history := s, mass_pos := hs, remaining_le := ?_ }⟩
  apply hbound.trans
  calc
    _ ≤ (3 / 2 : ℝ) *
        ((5 / 4 : ℝ) * geometricSurvival (sourceBatchCount x) * H.edgeFamily.vertices.card) :=
      mul_le_mul htol hsum hsum0 (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg (geometricSurvival_pos (sourceBatchCount x)).le
        (Nat.cast_nonneg H.edgeFamily.vertices.card : (0 : ℝ) ≤ H.edgeFamily.vertices.card)]

theorem CoveringWitness.remaining_le_of_mean_bound (W : B.CoveringWitness)
    (hℓ : 1 ≤ Real.log (Real.log (x : ℝ))) {K : ℝ}
    (hmean : sourceSurvivorMean a c x ≤
      K * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) :
    ((coveringRemaining B.family H.edgeFamily.vertices (sourceBatchCount x) W.history).card : ℝ) ≤
      20 * K * x / Real.log (x : ℝ) := by
  have hℓ0 : 0 < Real.log (Real.log (x : ℝ)) := zero_lt_one.trans_le hℓ
  have hM : 0 ≤ sourceSurvivorMean a c x := by
    have hc := H.cardinal_upper
    have hn : (0 : ℝ) ≤ (D.sourceRegularVertices a b).card := Nat.cast_nonneg _
    linarith
  have hgeo := (geometricSurvival_sourceBatchCount_lt hℓ).le
  calc
    _ ≤ 2 * geometricSurvival (sourceBatchCount x) * H.edgeFamily.vertices.card := W.remaining_le
    _ ≤ 2 * geometricSurvival (sourceBatchCount x) * (2 * sourceSurvivorMean a c x) :=
      mul_le_mul_of_nonneg_left H.cardinal_upper
        (mul_nonneg (by norm_num) (geometricSurvival_pos _).le)
    _ ≤ 2 * (5 / Real.log (Real.log (x : ℝ))) * (2 * sourceSurvivorMean a c x) := by
      gcongr
    _ = 20 * sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)) := by ring
    _ ≤ 20 * (K * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) /
        Real.log (Real.log (x : ℝ)) := by gcongr
    _ = _ := by field_simp

theorem CoveringWitness.selectedEdge_support (W : B.CoveringWitness)
    {j : ℕ} (hj : j < sourceBatchCount x) (p : B.labels j) :
    coveringSelectedEdge B.family hj W.history p = ∅ ∨
      ∃ n, 0 < H.edgeFamily.mass p.val n ∧
        coveringSelectedEdge B.family hj W.history p = H.edgeFamily.edge p.val n :=
  W.conditions.final_selectedEdge_support hj W.history W.mass_pos p

end SourceGeometricPartition

theorem exists_sourceCoveringData {a e : ℝ} (ha : 0 < a) (hepos : 0 < e) (he : e ≤ 1 / 120) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ (D : SourceProbabilityData c e x)
        (b : ResidueAssignment (sourceSmallPrimes a x)) (H : RegularSourceConditions D a b)
        (B : SourceGeometricPartition H) (W : B.CoveringWitness),
        ((coveringRemaining B.family H.edgeFamily.vertices
          (sourceBatchCount x) W.history).card : ℝ) ≤ K * x / Real.log (x : ℝ) := by
  obtain ⟨c, _C, hc, _hC, hdata⟩ := exists_batchedSourceData ha hepos he
  obtain ⟨_A, M, _hA, hM, hmean⟩ := exists_sourceSurvivorMean_bounds
  refine ⟨c, 20 * M * a * c, hc, by positivity, ?_⟩
  have hℓ := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hdata, eventually_source_survival_bounds, eventually_source_covering_conditions,
    hmean a c ha hc, hℓ.eventually_ge_atTop 1] with x hx hs hcond hm hℓ1
  obtain ⟨D, b, H, _hlo, _hhi, ⟨B⟩⟩ := hx
  obtain ⟨W⟩ := B.exists_coveringWitness (hs a c e D b H B) (hcond a c e D b H B)
  refine ⟨D, b, H, B, W, ?_⟩
  have hbound := W.remaining_le_of_mean_bound B hℓ1 hm.2
  convert hbound using 1
  ring

end

end Erdos4b.FGKMT

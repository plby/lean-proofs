import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Classical
noncomputable section

-- [TABLET NODE: SegmentFiniteSetComplementDense]
lemma SegmentFiniteSetComplementDense
    (x y : EuclideanSpace ℝ (Fin 2))
    (F : Finset (EuclideanSpace ℝ (Fin 2))) (hxy : x ≠ y) :
    segment ℝ x y ⊆
      closure (segment ℝ x y \ (F : Set (EuclideanSpace ℝ (Fin 2)))) := by
-- BODY
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, htIcc, rfl⟩
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun r => AffineMap.lineMap x y r
  let bad : Finset ℝ := F.preimage f (AffineMap.lineMap_injective ℝ hxy).injOn
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
  let δ : ℝ := ε / (dist x y + 1)
  have hden_pos : 0 < dist x y + 1 := by positivity
  have hδpos : 0 < δ := div_pos hε hden_pos
  have hδ_half_pos : 0 < δ / 2 := half_pos hδpos
  have hscale_lt : δ * dist x y < ε := by
    calc
      δ * dist x y < δ * (dist x y + 1) :=
        mul_lt_mul_of_pos_left (by linarith : dist x y < dist x y + 1) hδpos
      _ = ε := by
        dsimp [δ]
        exact div_mul_cancel₀ ε hden_pos.ne'
  have ht0 : 0 ≤ t := htIcc.1
  have ht1le : t ≤ 1 := htIcc.2
  have hparam :
      ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ dist t r < δ ∧ r ∉ bad := by
    by_cases ht_one : t = 1
    · let lo : ℝ := max 0 (1 - δ / 2)
      have hlo_lt : lo < 1 := by
        dsimp [lo]
        rw [max_lt_iff]
        constructor <;> linarith
      rcases (Set.Ioo_infinite hlo_lt).exists_notMem_finset bad with ⟨r, hrIoo, hrbad⟩
      refine ⟨r, ?_, ?_, hrbad⟩
      · exact ⟨le_of_max_le_left hrIoo.1.le, hrIoo.2.le⟩
      · rw [ht_one, Real.dist_eq]
        have hr_gt : 1 - δ / 2 < r :=
          (le_max_right (0 : ℝ) (1 - δ / 2)).trans_lt hrIoo.1
        have habs : |1 - r| = 1 - r :=
          abs_of_nonneg (sub_nonneg.mpr hrIoo.2.le)
        rw [habs]
        linarith
    · have ht_lt_one : t < 1 := lt_of_le_of_ne ht1le ht_one
      let hi : ℝ := min 1 (t + δ / 2)
      have ht_hi : t < hi := by
        dsimp [hi]
        rw [lt_min_iff]
        constructor <;> linarith
      rcases (Set.Ioo_infinite ht_hi).exists_notMem_finset bad with ⟨r, hrIoo, hrbad⟩
      refine ⟨r, ?_, ?_, hrbad⟩
      · exact ⟨ht0.trans hrIoo.1.le, (lt_of_lt_of_le hrIoo.2 (min_le_left _ _)).le⟩
      · rw [Real.dist_eq]
        have htr_lt : t < r := hrIoo.1
        have hru : r < t + δ / 2 := hrIoo.2.trans_le (min_le_right _ _)
        have habs : |t - r| = r - t := by
          rw [abs_of_nonpos (by linarith : t - r ≤ 0)]
          ring
        rw [habs]
        linarith
  rcases hparam with ⟨r, hrIcc, htr, hrbad⟩
  refine ⟨f r, ?_, ?_⟩
  · constructor
    · rw [segment_eq_image_lineMap]
      exact ⟨r, hrIcc, rfl⟩
    · intro hfmem
      exact hrbad (Finset.mem_preimage.mpr hfmem)
  · dsimp [f]
    rw [dist_lineMap_lineMap]
    exact (mul_lt_mul_of_pos_right htr (dist_pos.mpr hxy)).trans hscale_lt

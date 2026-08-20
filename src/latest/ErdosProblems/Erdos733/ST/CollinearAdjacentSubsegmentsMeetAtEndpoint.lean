import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: CollinearAdjacentSubsegmentsMeetAtEndpoint]
lemma CollinearAdjacentSubsegmentsMeetAtEndpoint
    (a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b)
    (u v w : Set.Icc (0 : ℝ) 1)
    (huv : u < v) (hvw : v < w) :
    segment ℝ (AffineMap.lineMap a b u.1) (AffineMap.lineMap a b v.1) ∩
        segment ℝ (AffineMap.lineMap a b v.1) (AffineMap.lineMap a b w.1) =
      ({AffineMap.lineMap a b v.1} : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective (k := ℝ) hab
  have hleft :
      segment ℝ (AffineMap.lineMap a b u.1) (AffineMap.lineMap a b v.1) =
        f '' Set.Icc u.1 v.1 := by
    have huv' : u.1 ≤ v.1 := huv.le
    rw [← image_segment ℝ f u.1 v.1, segment_eq_Icc huv']
  have hright :
      segment ℝ (AffineMap.lineMap a b v.1) (AffineMap.lineMap a b w.1) =
        f '' Set.Icc v.1 w.1 := by
    have hvw' : v.1 ≤ w.1 := hvw.le
    rw [← image_segment ℝ f v.1 w.1, segment_eq_Icc hvw']
  have hI :
      Set.Icc u.1 v.1 ∩ Set.Icc v.1 w.1 = ({v.1} : Set ℝ) := by
    ext t
    constructor
    · rintro ⟨htu, htv⟩
      exact Set.mem_singleton_iff.2 (le_antisymm htu.2 htv.1)
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨⟨huv.le, le_rfl⟩, ⟨le_rfl, hvw.le⟩⟩
  rw [hleft, hright, ← Set.image_inter hf, hI]
  simp [f]

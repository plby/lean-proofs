import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Defs

/-!
# Angular intervals inherited from a genuine local dissection

No interval-cover or interval-disjointness premise is inserted into the
geometric input: both are derived from the region cover and its disjoint
interiors by testing short positive rays.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

theorem ray_coords_nonneg {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ ThreeCorners.ray θ 0 ∧ 0 ≤ ThreeCorners.ray θ 1 := by
  refine ⟨?_, ?_⟩
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])

theorem positive_smul_ray_mem_ball {θ t r : ℝ} (ht : 0 < t) (htr : t < r) :
    t • ThreeCorners.ray θ ∈ ball (0 : Plane) r := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    ThreeCorners.norm_ray, mul_one]
  exact htr

theorem exists_small_positive_three (r : Fin 3 → ℝ) (hr : ∀ i, 0 < r i)
    {R : ℝ} (hR : 0 < R) :
    ∃ t : ℝ, 0 < t ∧ t < R ∧ ∀ i, t < r i := by
  let ε : ℝ := min R (min (r 0) (min (r 1) (r 2)))
  have hε : 0 < ε := lt_min hR (lt_min (hr 0) (lt_min (hr 1) (hr 2)))
  have hhalf : ε / 2 < ε := by linarith
  refine ⟨ε / 2, by positivity, hhalf.trans_le (min_le_left _ _), ?_⟩
  intro i
  have htail : ε ≤ min (r 0) (min (r 1) (r 2)) := min_le_right _ _
  fin_cases i
  · exact hhalf.trans_le (htail.trans (min_le_left _ _))
  · exact hhalf.trans_le (htail.trans ((min_le_right _ _).trans (min_le_left _ _)))
  · exact hhalf.trans_le (htail.trans ((min_le_right _ _).trans (min_le_right _ _)))

/-- Disjoint actual interiors give disjoint open angular intervals. -/
theorem intervals_pairwise_disjoint {ι : Type*} {P : ι → Set Plane}
    (g : ∀ i, AngularGerm (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j))) :
    Pairwise fun i j => Disjoint (Ioo (g i).lower (g i).upper)
      (Ioo (g j).lower (g j).upper) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro θ hi hj
  have hθ : θ ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(g i).lower_nonneg.trans hi.1.le, hi.2.le.trans (g i).upper_le⟩
  let t : ℝ := min (g i).radius (g j).radius / 2
  have hmin : 0 < min (g i).radius (g j).radius :=
    lt_min (g i).radius_pos (g j).radius_pos
  have ht : 0 < t := by dsimp [t]; positivity
  have htmin : t < min (g i).radius (g j).radius := by dsimp [t]; linarith
  have hti : t < (g i).radius := htmin.trans_le (min_le_left _ _)
  have htj : t < (g j).radius := htmin.trans_le (min_le_right _ _)
  exact Set.disjoint_left.mp (hdis hij)
    (((g i).interior_ray_iff θ hθ t ht hti).mpr hi)
    (((g j).interior_ray_iff θ hθ t ht htj).mpr hj)

/-- Covering a neighborhood of the first quadrant by three actual pieces
forces their closed angular intervals to cover the entire right angle. -/
theorem intervals_cover_of_local_cover {P : Fin 3 → Set Plane}
    (g : ∀ i, AngularGerm (P i))
    (hcover : ∃ R > 0, ball (0 : Plane) R ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ ⋃ i, P i) :
    ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2), ∃ i, θ ∈ Icc (g i).lower (g i).upper := by
  obtain ⟨R, hR, hcover⟩ := hcover
  obtain ⟨t, ht, htR, htr⟩ :=
    exists_small_positive_three (fun i => (g i).radius) (fun i => (g i).radius_pos) hR
  intro θ hθ
  have hcoords := ray_coords_nonneg hθ
  have hxquad : 0 ≤ (t • ThreeCorners.ray θ) 0 ∧ 0 ≤ (t • ThreeCorners.ray θ) 1 := by
    exact ⟨mul_nonneg ht.le hcoords.1, mul_nonneg ht.le hcoords.2⟩
  have hxcover := hcover ⟨positive_smul_ray_mem_ball ht htR, hxquad⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxcover
  exact ⟨i, (g i).piece_ray_imp θ hθ t ht (htr i) hi⟩

theorem interval_union_eq_of_local_cover {P : Fin 3 → Set Plane}
    (g : ∀ i, AngularGerm (P i))
    (hcover : ∃ R > 0, ball (0 : Plane) R ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ ⋃ i, P i) :
    (⋃ i, Icc (g i).lower (g i).upper) = Icc (0 : ℝ) (Real.pi / 2) := by
  apply Subset.antisymm
  · intro θ hθ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hθ
    exact ⟨(g i).lower_nonneg.trans hi.1, hi.2.trans (g i).upper_le⟩
  · intro θ hθ
    obtain ⟨i, hi⟩ := intervals_cover_of_local_cover g hcover θ hθ
    exact mem_iUnion.mpr ⟨i, hi⟩

end Puzzling139335.N6.TripleSectors.Angles

import ErdosProblems.Erdos633b.AngleParameter
import ErdosProblems.Erdos633b.IntervalTransport

/-! A finite partition of a triangle's opposite side induces the exact
sum of its angular pieces at the remaining vertex. -/

namespace Erdos633b.Triangle

theorem edge_partition_angle_sum {ι : Type*} [Fintype ι] (T : Triangle) (i : Fin 3)
    (A B : ι → Plane) (hAB : ∀ e, A e ≠ B e)
    (hc : (⋃ e, segment ℝ (A e) (B e)) = T.edge i)
    (hd : Pairwise fun e f => Disjoint (openSegment ℝ (A e) (B e))
      (openSegment ℝ (A f) (B f))) :
    T.angle i = ∑ e, EuclideanGeometry.angle (A e) (T.points i) (B e) := by
  have hsub (e : ι) : segment ℝ (A e) (B e) ⊆ T.edge i := by
    rw [← hc]
    exact Set.subset_iUnion (fun f : ι => segment ℝ (A f) (B f)) e
  have himage : T.edgeParam i '' Set.Icc (0 : ℝ) 1 = T.edge i := by
    rw [T.edge_eq_segment]
    exact (segment_eq_image_lineMap ℝ _ _).symm
  have hA (e : ι) : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ T.edgeParam i t = A e := by
    have h := hsub e (left_mem_segment ℝ (A e) (B e))
    rwa [← himage] at h
  have hB (e : ι) : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ T.edgeParam i t = B e := by
    have h := hsub e (right_mem_segment ℝ (A e) (B e))
    rwa [← himage] at h
  choose a ha hAa using hA
  choose b hb hBb using hB
  have hab (e : ι) : a e ≠ b e := by
    intro h
    exact hAB e (hAa e ▸ hBb e ▸ congrArg (T.edgeParam i) h)
  have he (e : ι) : T.edgeParam i '' segment ℝ (a e) (b e) = segment ℝ (A e) (B e) := by
    rw [image_segment, hAa, hBb]
  have ho (e : ι) : T.edgeParam i '' openSegment ℝ (a e) (b e) =
      openSegment ℝ (A e) (B e) := by
    rw [image_openSegment, hAa, hBb]
  have hcover : (⋃ e, segment ℝ (a e) (b e)) = Set.Icc (0 : ℝ) 1 := by
    apply (T.edgeParam_injective i).image_injective
    rw [Set.image_iUnion, himage]
    simpa only [he] using hc
  have hdisj : Pairwise fun e f => Disjoint (openSegment ℝ (a e) (b e))
      (openSegment ℝ (a f) (b f)) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro t hte htf
    have h1 : T.edgeParam i t ∈ openSegment ℝ (A e) (B e) := ho e ▸ ⟨t, hte, rfl⟩
    have h2 : T.edgeParam i t ∈ openSegment ℝ (A f) (B f) := ho f ▸ ⟨t, htf, rfl⟩
    exact Set.disjoint_left.mp (hd hef) h1 h2
  have hsum := interval_partition_monotone_sum a b ha hb hab hcover hdisj (T.edgeAngle i)
    (T.edgeAngle_continuous i) (T.edgeAngle_strictMonoOn i)
  rw [T.edgeAngle_one, T.edgeAngle_zero, sub_zero] at hsum
  have hangle (e : ι) : EuclideanGeometry.angle (A e) (T.points i) (B e) =
      |T.edgeAngle i (a e) - T.edgeAngle i (b e)| := by
    rw [← hAa e, ← hBb e, T.edgeParam_angle_eq_abs i (ha e) (hb e), abs_sub_comm]
  simpa only [hangle] using hsum.symm

end Erdos633b.Triangle

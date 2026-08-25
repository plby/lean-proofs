import StackExchange.Puzzling139335.BoundaryGerm

/-!
# Transport of actual boundary rays

Equal germs of unions of two initial segments determine their positive
rays.  Applying this observation after transporting a boundary germ by
an affine isometry avoids any assumption that the chosen far endpoints
are mapped to far endpoints.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles.Congruence

noncomputable section

/-- A nonzero point common to two initial segments determines their
common positive ray. -/
theorem exists_pos_smul_of_nonzero_segment_inter
    {a c z : Plane} (hz : z ≠ 0)
    (hza : z ∈ segment ℝ 0 a) (hzc : z ∈ segment ℝ 0 c) :
    ∃ s : ℝ, 0 < s ∧ a = s • c := by
  have hza' : ∃ t ∈ Icc (0 : ℝ) 1, t • a = z := by
    simpa only [segment_eq_image, smul_zero, zero_add, mem_image] using hza
  have hzc' : ∃ u ∈ Icc (0 : ℝ) 1, u • c = z := by
    simpa only [segment_eq_image, smul_zero, zero_add, mem_image] using hzc
  obtain ⟨t, ht, htz⟩ := hza'
  obtain ⟨u, hu, huz⟩ := hzc'
  have ht0 : t ≠ 0 := by
    intro h
    apply hz
    rw [← htz, h, zero_smul]
  have hu0 : u ≠ 0 := by
    intro h
    apply hz
    rw [← huz, h, zero_smul]
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  refine ⟨t⁻¹ * u, mul_pos (inv_pos.mpr htp) hup, ?_⟩
  calc
    a = t⁻¹ • (t • a) := (inv_smul_smul₀ ht0 a).symm
    _ = t⁻¹ • (u • c) := by rw [htz, huz]
    _ = (t⁻¹ * u) • c := by rw [smul_smul]

/-- The first ray of a two-segment germ is one of the two target rays.
The selected endpoint may lie beyond the neighborhood where the germs
agree; only a shorter nonzero point is used. -/
theorem left_ray_of_segment_union_germ
    {a b c d : Plane} (ha : a ≠ 0)
    (hgerm : SameBoundaryGerm
      (segment ℝ 0 a ∪ segment ℝ 0 b)
      (segment ℝ 0 c ∪ segment ℝ 0 d) 0) :
    (∃ s : ℝ, 0 < s ∧ a = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ a = s • d) := by
  obtain ⟨r, hr, heq⟩ := hgerm
  obtain ⟨z, hz, hseg⟩ := exists_initial_segment_subset_ball ha hr
  have hza : z ∈ segment ℝ 0 a := (hseg (right_mem_segment ℝ 0 z)).1
  have hzball : z ∈ ball (0 : Plane) r := (hseg (right_mem_segment ℝ 0 z)).2
  have hztarget : z ∈ segment ℝ 0 c ∪ segment ℝ 0 d :=
    ((Set.ext_iff.mp heq z).mp ⟨hzball, Or.inl hza⟩).2
  rcases hztarget with hzc | hzd
  · exact Or.inl (exists_pos_smul_of_nonzero_segment_inter hz hza hzc)
  · exact Or.inr (exists_pos_smul_of_nonzero_segment_inter hz hza hzd)

/-- An origin-fixing congruence sends each actual nonzero boundary ray to
a positive multiple of one of the target boundary rays. -/
theorem image_left_ray_of_boundary_germs
    {A B : Set Plane} {a b c d : Plane}
    (hA : SameBoundaryGerm A (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hB : SameBoundaryGerm B (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' A = B)
    (ha : a ≠ 0) :
    (∃ s : ℝ, 0 < s ∧ e a = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ e a = s • d) := by
  have hea : e a ≠ 0 := by
    intro h
    exact ha (e.injective (h.trans hzero.symm))
  have haImage : e '' segment ℝ 0 a = segment ℝ 0 (e a) := by
    have h : e '' segment ℝ 0 a = segment ℝ (e 0) (e a) :=
      image_segment ℝ e.toAffineMap 0 a
    simpa only [hzero] using h
  have hbImage : e '' segment ℝ 0 b = segment ℝ 0 (e b) := by
    have h : e '' segment ℝ 0 b = segment ℝ (e 0) (e b) :=
      image_segment ℝ e.toAffineMap 0 b
    simpa only [hzero] using h
  have htransport := hA.symm.image_affineIsometry e
  rw [Set.image_union, haImage, hbImage, he, hzero] at htransport
  exact left_ray_of_segment_union_germ hea (htransport.trans hB)

/-- The corresponding statement for the second source ray. -/
theorem image_right_ray_of_boundary_germs
    {A B : Set Plane} {a b c d : Plane}
    (hA : SameBoundaryGerm A (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hB : SameBoundaryGerm B (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' A = B)
    (hb : b ≠ 0) :
    (∃ s : ℝ, 0 < s ∧ e b = s • c) ∨
      (∃ s : ℝ, 0 < s ∧ e b = s • d) := by
  have hA' : SameBoundaryGerm A (segment ℝ 0 b ∪ segment ℝ 0 a) 0 := by
    simpa only [union_comm] using hA
  exact image_left_ray_of_boundary_germs hA' hB e hzero he hb

end

end Puzzling139335.N6.TripleSectors.Angles.Congruence

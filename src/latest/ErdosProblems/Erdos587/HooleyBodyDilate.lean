import ErdosProblems.Erdos587.HooleyConvexBody

/-! # Dilations of convex progression bodies, with controlled lattice rounding -/

namespace Erdos587.GeneralizedAP

lemma delta_bodyDilate_one {d : ℕ} (B : Set (Fin d → ℝ)) : bodyDilate 1 B = B := by
  ext x
  simp only [bodyDilate, Set.mem_ofPred_eq, one_smul, exists_eq_right]

lemma delta_bodyDilate_mul {d : ℕ} (c s : ℝ) (B : Set (Fin d → ℝ)) :
    bodyDilate c (bodyDilate s B) = bodyDilate (c * s) B := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, mul_smul c s z⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨s • z, ⟨z, hz, rfl⟩, (mul_smul c s z).symm⟩

lemma delta_bodyDilate_image {d n : ℕ} (c : ℝ)
    (q : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (B : Set (Fin d → ℝ)) :
    bodyDilate c (q '' B) = q '' bodyDilate c B := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨c • z, ⟨z, hz, rfl⟩, map_smul q c z⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨q z, ⟨z, hz, rfl⟩, (map_smul q c z).symm⟩

lemma delta_bodyDilate_mono_set {d : ℕ} (c : ℝ) {B D : Set (Fin d → ℝ)}
    (h : B ⊆ D) : bodyDilate c B ⊆ bodyDilate c D := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

lemma delta_bodyDilate_mono {d : ℕ} {B : Set (Fin d → ℝ)}
    (hzero : (0 : Fin d → ℝ) ∈ B) (hconv : Convex ℝ B)
    {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) : bodyDilate c B ⊆ bodyDilate s B := by
  rintro x ⟨y, hy, rfl⟩
  by_cases hs : s = 0
  · have hc0 : c = 0 := le_antisymm (hs ▸ hcs) hc
    subst c
    exact ⟨0, hzero, by simp⟩
  · have hspos : 0 < s := lt_of_le_of_ne (hc.trans hcs) (Ne.symm hs)
    refine ⟨(c / s) • y, ?_, ?_⟩
    · have hh := hconv hy hzero (div_nonneg hc hspos.le)
        (sub_nonneg.mpr ((div_le_one hspos).mpr hcs)) (by ring : c / s + (1 - c / s) = 1)
      simpa only [smul_zero, add_zero] using hh
    · rw [smul_smul]
      congr 1
      field_simp

noncomputable def deltaDilatedConvexProgression (X : ConvexProgression) (c : ℝ)
    (hc : 0 < c)
    (hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) (bodyDilate c X.body)) :
    ConvexProgression :=
  deltaConvexProgression X.base X.eval (bodyDilate c X.body)
    (by
      have hcompact := Metric.isCompact_of_isClosed_isBounded X.body_closed X.body_bounded
      exact hcompact.image
        (c • (LinearMap.id : (Fin X.rank → ℝ) →ₗ[ℝ] _)).continuous_of_finiteDimensional)
    ⟨0, X.body_zero, smul_zero c⟩
    (by
      change Convex ℝ ((c • (LinearMap.id : (Fin X.rank → ℝ) →ₗ[ℝ] _)) '' X.body)
      exact X.body_convex.linear_image _)
    (by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨-y, X.body_neg y hy, smul_neg c y⟩)
    (by
      intro x
      obtain ⟨s, hs, hsx⟩ := X.body_full x
      exact ⟨c * s, mul_pos hc hs, s • x, hsx, (mul_smul c s x).symm⟩)
    hround

theorem deltaDilatedConvexProgression_carrier_subset (X : ConvexProgression)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hround) :
    (deltaDilatedConvexProgression X c hc hround).carrier ⊆ X.carrier := by
  rintro z ⟨v, hv, rfl⟩
  refine ⟨v, ?_, rfl⟩
  have hmem := delta_bodyDilate_mono X.body_zero X.body_convex hc.le hc1 hv
  rwa [delta_bodyDilate_one] at hmem

end Erdos587.GeneralizedAP

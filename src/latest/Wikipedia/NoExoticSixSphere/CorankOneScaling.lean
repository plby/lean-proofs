import Wikipedia.NoExoticSixSphere.CorankOneChart

/-!
# Nonzero scalar changes of the actual corank-one residual

Multiplying an operator by a nonzero real scalar preserves its range and
leading-block chart. On that chart its residual is multiplied by the same
scalar. These are identities for the original operators, not replacement
definitions of their rank or residual.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.CorankOne

variable {V W E F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem injective_smul_iff (L : V →L[ℝ] W) {a : ℝ} (ha : a ≠ 0) :
    Injective (a • L) ↔ Injective L := by
  constructor
  · intro hi x y hxy
    exact hi (congrArg (a • ·) hxy)
  · intro hi x y hxy
    apply hi
    have h := congrArg (a⁻¹ • ·) hxy
    change a⁻¹ • (a • L x) = a⁻¹ • (a • L y) at h
    simpa only [inv_smul_smul₀ ha] using h

theorem range_smul_eq (L : V →L[ℝ] W) {a : ℝ} (ha : a ≠ 0) :
    (a • L).range = L.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨a • x, L.map_smul a x⟩
  · rintro ⟨x, rfl⟩
    refine ⟨a⁻¹ • x, ?_⟩
    change a • L (a⁻¹ • x) = L x
    rw [map_smul, smul_inv_smul₀ ha]

omit [FiniteDimensional ℝ E] in
theorem leading_smul (L : BlockMap E F) (a : ℝ) :
    leading (a • L) = a • leading L := by
  ext x
  rfl

theorem smul_mem_chart_iff (L : BlockMap E F) {a : ℝ} (ha : a ≠ 0) :
    a • L ∈ chart ↔ L ∈ chart := by
  change Injective (leading (a • L)) ↔ Injective (leading L)
  rw [leading_smul, injective_smul_iff _ ha]

theorem residual_smul {L : BlockMap E F} (hL : L ∈ chart)
    {a : ℝ} (ha : a ≠ 0) : residual (a • L) = a • residual L := by
  let v : E := -(leading L).inverse (column L).1
  have hv : (L (v, 1)).1 = 0 := by
    rw [block_apply]
    change leading L v + (1 : ℝ) • (column L).1 = 0
    simp only [v, map_neg, (leading_invertible hL).self_apply_inverse, one_smul,
      neg_add_cancel]
  have hsv : ((a • L) (v, 1)).1 = 0 := by
    change a • (L (v, 1)).1 = 0
    rw [hv, smul_zero]
  rw [← tail_eq_residual_of_head_zero (a • L)
    (leading_invertible ((smul_mem_chart_iff L ha).mpr hL)) v hsv]
  change a • (L (v, 1)).2 = a • residual L
  rw [tail_eq_residual_of_head_zero L (leading_invertible hL) v hv]

end NoExoticSixSphere.CorankOne

import Wikipedia.NoExoticSixSphere.AffineParameterEvaluation

/-!
# Weighted affine differences with only one active source point

Distinct source points admit independent affine value prescriptions. Thus the
difference of two composed weighted evaluations is surjective if the left
weight and left outer derivative are surjective, regardless of the right
weight. Swapping the two points gives the corresponding right-active result.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.AffinePerturbation

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem surjective_weighted_difference_left (x y : E) (hxy : x ≠ y)
    (A B : F →L[ℝ] G) (hA : Surjective A) (a b : ℝ) (ha : a ≠ 0) :
    Surjective (A.comp (a • evaluation x) - B.comp (b • evaluation y) :
      Parameters E F →L[ℝ] G) := by
  intro v
  obtain ⟨w, hw⟩ := hA v
  obtain ⟨p, hp⟩ := surjective_pairEvaluation (F := F) x y hxy (a⁻¹ • w, 0)
  have hx : evaluation x p = a⁻¹ • w := congrArg Prod.fst hp
  have hy : evaluation y p = 0 := congrArg Prod.snd hp
  refine ⟨p, ?_⟩
  change A (a • evaluation x p) - B (b • evaluation y p) = v
  rw [hx, hy, smul_inv_smul₀ ha, smul_zero, map_zero, sub_zero, hw]

theorem surjective_weighted_difference_right (x y : E) (hxy : x ≠ y)
    (A B : F →L[ℝ] G) (hB : Surjective B) (a b : ℝ) (hb : b ≠ 0) :
    Surjective (A.comp (a • evaluation x) - B.comp (b • evaluation y) :
      Parameters E F →L[ℝ] G) := by
  intro v
  obtain ⟨p, hp⟩ := surjective_weighted_difference_left y x hxy.symm B A hB b a hb (-v)
  refine ⟨p, ?_⟩
  change A (a • evaluation x p) - B (b • evaluation y p) = v
  change B (b • evaluation y p) - A (a • evaluation x p) = -v at hp
  exact neg_injective (by simpa only [neg_sub] using hp)

theorem surjective_weighted_difference (x y : E) (hxy : x ≠ y)
    (A B : F →L[ℝ] G) (hA : Surjective A) (hB : Surjective B)
    (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    Surjective (A.comp (a • evaluation x) - B.comp (b • evaluation y) :
      Parameters E F →L[ℝ] G) := by
  rcases h with ha | hb
  · exact surjective_weighted_difference_left x y hxy A B hA a b ha
  · exact surjective_weighted_difference_right x y hxy A B hB a b hb

end NoExoticSixSphere.AffinePerturbation

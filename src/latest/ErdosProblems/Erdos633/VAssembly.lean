import ErdosProblems.Erdos633.VGrid

/-!
# Assembly of the four exceptional V regions

This gluing theorem retains all coverage and pairwise-disjointness obligations.
The remaining shape-specific work is to give the three triangular tilings with
the same reference tile as the affine parallelogram grid.
-/

namespace Erdos633

theorem disjoint_interiors_affine_image (e : ℂ ≃ᵃ[ℝ] ℂ) {S U : Set ℂ}
    (h : Disjoint (interior S) (interior U)) :
    Disjoint (interior (e '' S)) (interior (e '' U)) := by
  let f := e.toContinuousAffineEquiv.toHomeomorph
  change Disjoint (interior (f '' S)) (interior (f '' U))
  rw [← f.image_interior, ← f.image_interior]
  exact Set.disjoint_image_of_injective e.injective h

/-- Four congruent region tilings combine into a congruent tiling of the
transported standard triangle, with the exact sum of their cardinalities. -/
noncomputable def vRegions_assemble (e : ℂ ≃ᵃ[ℝ] ℂ) (b : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (R : Triangle)
    {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄]
    (T₁ : RegionTiling (e '' vLowerRegion b) R ι₁)
    (T₂ : RegionTiling (e '' vLeftRegion b) R ι₂)
    (T₃ : RegionTiling (e '' vUpperRegion b) R ι₃)
    (T₄ : RegionTiling (e '' vParallelogramRegion b) R ι₄) :
    CongruentTiling (standardTriangle.mapAffineEquiv e) R
      (Fintype.card ι₁ + Fintype.card ι₂ + Fintype.card ι₃ + Fintype.card ι₄) := by
  let T := T₁.unionFour T₂ T₃ T₄
    (disjoint_interiors_affine_image e (vLower_left_disjoint b))
    (disjoint_interiors_affine_image e (vLower_upper_disjoint b hb0))
    (disjoint_interiors_affine_image e (vLower_parallelogram_disjoint b))
    (disjoint_interiors_affine_image e (vLeft_upper_disjoint b))
    (disjoint_interiors_affine_image e (vLeft_parallelogram_disjoint b hb0))
    (disjoint_interiors_affine_image e (vUpper_parallelogram_disjoint b))
  have hcover : (((e '' vLowerRegion b ∪ e '' vLeftRegion b) ∪ e '' vUpperRegion b) ∪
      e '' vParallelogramRegion b) = (standardTriangle.mapAffineEquiv e).carrier := by
    rw [← Set.image_union, ← Set.image_union, ← Set.image_union,
      vRegions_cover b hb0 hb1, Triangle.mapAffineEquiv_carrier]
  simpa only [Fintype.card_sum] using T.toCongruentTiling _ hcover

end Erdos633

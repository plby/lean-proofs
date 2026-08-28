import Wikipedia.SmoothSixDPoincare.CleanNeighborhoodAvoidance

/-!
# Restricting a closed obstacle image to an open ambient submanifold

The obstacle's restricted parameter space need not be compact. Its image is
nevertheless closed in the open ambient submanifold, and the restriction is
smooth for the native open-submanifold structures.
-/

noncomputable section

open Set ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenObstacle

section Topological

variable {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]

/-- The actual open part of the obstacle parameter space mapping into `U`. -/
def source (g : C(Y, N)) (U : Opens N) : Opens Y :=
  ⟨g ⁻¹' (U : Set N), U.isOpen.preimage g.continuous⟩

/-- The obstacle restricted both in its source and in its target. -/
def restrict (g : C(Y, N)) (U : Opens N) : C(source g U, U) where
  toFun y := ⟨g y, y.property⟩
  continuous_toFun := (g.continuous.comp continuous_subtype_val).subtype_mk _

/-- Restricting the parameter space loses exactly the image points outside `U`. -/
theorem mem_range_restrict_iff (g : C(Y, N)) (U : Opens N) (x : U) :
    x ∈ range (restrict g U) ↔ (x : N) ∈ range g := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact hy.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩

/-- The restricted image is the inverse image of the full original image. -/
theorem range_restrict (g : C(Y, N)) (U : Opens N) :
    range (restrict g U) = (Subtype.val : U → N) ⁻¹' range g := by
  ext x
  exact mem_range_restrict_iff g U x

/-- A closed full obstacle image remains closed in the open ambient submanifold. -/
theorem isClosed_range_restrict (g : C(Y, N)) (U : Opens N)
    (hclosed : IsClosed (range g)) : IsClosed (range (restrict g U)) := by
  rw [range_restrict]
  exact hclosed.preimage continuous_subtype_val

/-- Restricting an arbitrary chosen part of the obstacle gives its exact image inside `U`. -/
theorem image_restrict (g : C(Y, N)) (U : Opens N) (A : Set Y) :
    restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A) =
      (Subtype.val : U → N) ⁻¹' (g '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨y, hy, congrArg Subtype.val heq⟩
  · rintro ⟨y, hy, heq⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact heq.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, hy, Subtype.ext heq⟩

/-- A closed selected obstacle image stays closed after restricting to the open ambient target. -/
theorem isClosed_image_restrict (g : C(Y, N)) (U : Opens N) (A : Set Y)
    (hclosed : IsClosed (g '' A)) :
    IsClosed (restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A)) := by
  rw [image_restrict]
  exact hclosed.preimage continuous_subtype_val

end Topological

variable {E' G H H' Y N : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace H N]

/-- The actual obstacle restriction is smooth with the inherited manifold structures. -/
theorem contMDiff_restrict (g : C(Y, N)) (U : Opens N)
    (hg : ContMDiff I' J ∞ g) : ContMDiff I' J ∞ (restrict g U) := by
  apply (ContMDiff.subtypeVal_comp_iff U (restrict g U)).mp
  exact hg.comp contMDiff_subtype_val

end Wikipedia.SmoothSixDPoincare.OpenObstacle

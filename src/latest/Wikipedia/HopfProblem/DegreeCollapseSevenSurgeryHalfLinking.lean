import Wikipedia.HopfProblem.DegreeCollapseTimeCollarLinking
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseSevenAmbientFiniteHomology

/-!
# The actual new surgery half carries the required nondegenerate linking pairing

Use the preserved original collar and the actual target atlas. The proved
surgery invariants supply the closed manifold's connectivity and homology.
The pairing is the original target linking restricted along its literal
new-half inclusion. An order-four class forces a nonzero diagonal for the
next reduction; this statement does not perform that next surgery.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 7) = 7) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [Finite (SingularHomology (PositiveHalf A hR T) 3)]
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)

local instance : ChartedSpace (Vector 7) (Target A hR) := targetChartedSpace A hR
local instance : IsManifold (𝓡 7) ∞ (Target A hR) := target_isManifold A hR
local instance : CompactSpace (Target A hR) := compactSpace_target A hR
local instance : SimplyConnectedSpace (Target A hR) :=
  (target_simplyConnected_iff A hR).2 inferInstance
local instance : Subsingleton (SingularHomology (Target A hR) 2) := target_second_homology A hR

def positiveHalfLinking :
    SingularHomology (PositiveHalf A hR T) 3 →ₗ[ℤ]
      (SingularHomology (PositiveHalf A hR T) 3 →ₗ[ℤ] RationalResidue.Value) := by
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  exact (preservedTimeCollar A hR T C).halfLinking (E := Vector 7)

theorem positiveHalfLinking_apply (x y : SingularHomology (PositiveHalf A hR T) 3) :
    letI : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T;
    positiveHalfLinking A hR T C x y = IntegralSevenLinking.linking (E := Vector 7) (Target A hR)
      (singularHomologyMap (newHalfToClosed A hR T) 3 x)
      (singularHomologyMap (newHalfToClosed A hR T) 3 y) := rfl

theorem positiveHalfLinking_symmetry (x y : SingularHomology (PositiveHalf A hR T) 3) :
    positiveHalfLinking A hR T C x y = positiveHalfLinking A hR T C y x := by
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  exact (preservedTimeCollar A hR T C).halfLinking_symmetry (E := Vector 7) x y

variable [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

theorem positiveHalfLinking_left_nondegenerate
    (x : SingularHomology (PositiveHalf A hR T) 3)
    (hx : ∀ y, positiveHalfLinking A hR T C x y = 0) : x = 0 := by
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  exact (preservedTimeCollar A hR T C).halfLinking_left_nondegenerate (E := Vector 7) x hx

theorem positiveHalfLinking_right_nondegenerate
    (y : SingularHomology (PositiveHalf A hR T) 3)
    (hy : ∀ x, positiveHalfLinking A hR T C x y = 0) : y = 0 := by
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  exact (preservedTimeCollar A hR T C).halfLinking_right_nondegenerate (E := Vector 7) y hy

theorem positiveHalfLinking_diagonal_dichotomy :
    (∃ x : SingularHomology (PositiveHalf A hR T) 3, positiveHalfLinking A hR T C x x ≠ 0) ∨
      ∀ x : SingularHomology (PositiveHalf A hR T) 3, x + x = 0 := by
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  exact (preservedTimeCollar A hR T C).halfLinking_diagonal_dichotomy (E := Vector 7)

theorem positiveHalfLinking_nonzero_diagonal_of_double_ne_zero
    (x : SingularHomology (PositiveHalf A hR T) 3) (hx : (2 : ℤ) • x ≠ 0) :
    ∃ y : SingularHomology (PositiveHalf A hR T) 3, positiveHalfLinking A hR T C y y ≠ 0 := by
  rcases positiveHalfLinking_diagonal_dichotomy A hR T C with h | h
  · exact h
  · exact (hx (by simpa only [two_zsmul] using h x)).elim

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

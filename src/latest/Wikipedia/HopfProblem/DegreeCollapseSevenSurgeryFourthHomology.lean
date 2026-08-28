import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfHomology
import Wikipedia.HopfProblem.DegreeCollapseCyclicCoordinateInjectivity
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite new third homology preserves zero fourth homology of the actual half

The original two endpoint sequences concern the same actual common body.
Zero old H4 makes its old integer connecting coordinate injective. Finite
new H3 forces its new coordinate to be nonzero, so the rank-one integer
argument makes that coordinate injective too. Exactness and the original
new-half inclusion then give zero new H4. No new reflected-double
presentation, duality theorem, or finiteness of the exterior is assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def oldHalfFourthCoordinate : SingularHomology (HalfBody A hR T) 4 →ₗ[ℤ] ℤ :=
  (unitSphereHomologyTopEquiv 2).toLinearMap.comp (oldHalfConnecting A hR T 3)

def newHalfFourthCoordinate : SingularHomology (HalfBody A hR T) 4 →ₗ[ℤ] ℤ :=
  (unitSphereHomologyTopEquiv 2).toLinearMap.comp (newHalfConnecting A hR T 3)

theorem oldHalfFourthCoordinate_injective
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)] :
    Injective (oldHalfFourthCoordinate A hR T) := by
  have hi : Injective (oldHalfConnecting A hR T 3) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    rw [← half_exact_at_body_old A hR T 3] at hx
    obtain ⟨y, rfl⟩ := hx
    change singularHomologyMap (oldHalfInclusion A hR T) 4 y = 0
    rw [Subsingleton.elim y 0, map_zero]
  exact (unitSphereHomologyTopEquiv 2).injective.comp hi

theorem newHalfFourthCoordinate_nonzero
    [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    ∃ w, newHalfFourthCoordinate A hR T w ≠ 0 := by
  let N : ℤ := Nat.card (SingularHomology (PositiveHalf A hR T) 3)
  have hs : N • unitSphereTopClass 2 ∈
      LinearMap.ker (singularHomologyMap (halfBeltSphere A hR T) 3) := by
    change singularHomologyMap (halfBeltSphere A hR T) 3 (N • unitSphereTopClass 2) = 0
    rw [map_zsmul]
    dsimp only [N]
    exact_mod_cast (card_nsmul_eq_zero' :
      Nat.card (SingularHomology (PositiveHalf A hR T) 3) •
        singularHomologyMap (halfBeltSphere A hR T) 3 (unitSphereTopClass 2) = 0)
  rw [← half_exact_at_belt A hR T 3 (by decide)] at hs
  obtain ⟨w, hw⟩ := hs
  have he : newHalfFourthCoordinate A hR T w = N := by
    change unitSphereHomologyTopEquiv 2 (newHalfConnecting A hR T 3 w) = N
    rw [hw, map_zsmul, unitSphereHomologyTopEquiv_topClass]
    simp only [zsmul_eq_mul, Int.cast_id, mul_one]
  refine ⟨w, ?_⟩
  rw [he]
  dsimp only [N]
  exact_mod_cast (Nat.card_pos.ne' : Nat.card (SingularHomology (PositiveHalf A hR T) 3) ≠ 0)

theorem newHalfFourthCoordinate_injective
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    Injective (newHalfFourthCoordinate A hR T) :=
  CyclicCoordinateInjectivity.injective_of_nonzero
    (oldHalfFourthCoordinate A hR T).toAddMonoidHom
    (oldHalfFourthCoordinate_injective A hR T)
    (newHalfFourthCoordinate A hR T).toAddMonoidHom
    (newHalfFourthCoordinate_nonzero A hR T)

theorem newHalfFourthCoordinate_inclusion
    (x : SingularHomology (PositiveHalf A hR T) 4) :
    newHalfFourthCoordinate A hR T (singularHomologyMap (newHalfInclusion A hR T) 4 x) = 0 := by
  have hx : singularHomologyMap (newHalfInclusion A hR T) 4 x ∈
      LinearMap.ker (newHalfConnecting A hR T 3) := by
    rw [← half_exact_at_body_new A hR T 3]
    exact ⟨x, rfl⟩
  change newHalfConnecting A hR T 3 (singularHomologyMap (newHalfInclusion A hR T) 4 x) = 0 at hx
  change unitSphereHomologyTopEquiv 2
    (newHalfConnecting A hR T 3 (singularHomologyMap (newHalfInclusion A hR T) 4 x)) = 0
  rw [hx, map_zero]

theorem positiveHalf_fourth_homology_of_finite
    [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    [Finite (SingularHomology (PositiveHalf A hR T) 3)] :
    Subsingleton (SingularHomology (PositiveHalf A hR T) 4) := by
  refine ⟨fun x y ↦ ?_⟩
  apply newHalf_injective_four A hR T
  apply newHalfFourthCoordinate_injective A hR T
  rw [newHalfFourthCoordinate_inclusion, newHalfFourthCoordinate_inclusion]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct

/-!
# Actual cap and positive-circle coordinates on elliptic boundary homology

The genuine boundary product homeomorphism and the proved singular
circle-product splitting give homology coordinates in all positive degrees.
The first coordinate is the actual central-cap map.  The inverse is the
actual cap-section map plus the actual positive-circle cross product,
transported through the same homeomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology

local notation "B" => ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary
local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The same literal product homeomorphism with the positive circle placed first. -/
def boundaryCircleFirstHomeomorph (j : Kind) :
    B j ≃ₜ MappingTorus.Circle × S j :=
  (boundaryProductHomeomorph j).trans (Homeomorph.prodComm _ _)

/-- Projecting away the circle is exactly the original central-cap map. -/
theorem boundaryCircleFirstHomeomorph_projection (j : Kind) :
    (productProjection (S j)).comp (boundaryCircleFirstHomeomorph j : C(_, _)) =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j := by
  ext q
  exact boundaryProductHomeomorph_fst j q

/-- The genuine cap section becomes the zero-circle section under this homeomorphism. -/
theorem boundaryCircleFirstHomeomorph_section (j : Kind) :
    (boundaryCircleFirstHomeomorph j : C(_, _)).comp (capSection j) =
      productSection (S j) := by
  apply ContinuousMap.ext
  intro x
  change Prod.swap (boundaryProductHomeomorph j
    ((boundaryProductHomeomorph j).symm (x, 0))) = (0, x)
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- Actual integral boundary homology, split into cap and positive-circle parts. -/
def boundaryCapHomologyEquiv (j : Kind) (n : ℕ) :
    SingularHomology (B j) (n + 1) ≃ₗ[ℤ]
      (SingularHomology (S j) (n + 1) × SingularHomology (S j) n) :=
  (homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) (n + 1)).trans
    (circleProductHomologyEquiv (S j) n)

/-- The first coordinate is induced by the original continuous cap map. -/
theorem boundaryCapHomologyEquiv_fst (j : Kind) (n : ℕ)
    (a : SingularHomology (B j) (n + 1)) :
    (boundaryCapHomologyEquiv j n a).1 =
      singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) (n + 1) a := by
  change singularHomologyMap (productProjection (S j)) (n + 1)
    (singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _)) (n + 1) a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_projection]

/-- The actual section contributes the cap summand and no circle summand. -/
@[simp] theorem boundaryCapHomologyEquiv_section (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) (n + 1)) :
    boundaryCapHomologyEquiv j n (singularHomologyMap (capSection j) (n + 1) a) =
      (a, 0) := by
  change circleProductHomologyEquiv (S j) n
    (singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _)) (n + 1)
      (singularHomologyMap (capSection j) (n + 1) a)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_section]
  exact circleProductHomologyEquiv_section (S j) n a

/-- The genuine positive-circle cross product, carried back to the native boundary. -/
def boundaryPositiveCircleCross (j : Kind) (n : ℕ) :
    SingularHomology (S j) n →ₗ[ℤ] SingularHomology (B j) (n + 1) :=
  (homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) (n + 1)).symm.toLinearMap.comp
    (positiveCircleCross (S j) n)

/-- This is the actual homology pushforward of the singular positive-circle cross product. -/
theorem boundaryPositiveCircleCross_apply (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    boundaryPositiveCircleCross j n a =
      singularHomologyMap ((boundaryCircleFirstHomeomorph j).symm : C(_, _)) (n + 1)
        (positiveCircleCross (S j) n a) := rfl

/-- The positive-circle cross product is exactly the second summand. -/
@[simp] theorem boundaryCapHomologyEquiv_positiveCircleCross (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    boundaryCapHomologyEquiv j n (boundaryPositiveCircleCross j n a) = (0, a) := by
  change circleProductHomologyEquiv (S j) n
    (homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) (n + 1)
      ((homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) (n + 1)).symm
        (positiveCircleCross (S j) n a))) = _
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_positiveCircleCross]

/-- The cap section and positive-circle cross product are the literal inverse formula. -/
theorem boundaryCapHomologyEquiv_symm_eq_section_add_cross (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) (n + 1) × SingularHomology (S j) n) :
    (boundaryCapHomologyEquiv j n).symm a =
      singularHomologyMap (capSection j) (n + 1) a.1 +
        boundaryPositiveCircleCross j n a.2 := by
  apply (boundaryCapHomologyEquiv j n).injective
  rw [LinearEquiv.apply_symm_apply, map_add, boundaryCapHomologyEquiv_section,
    boundaryCapHomologyEquiv_positiveCircleCross]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

@[simp] theorem boundaryCapHomologyEquiv_symm_inl (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) (n + 1)) :
    (boundaryCapHomologyEquiv j n).symm (a, 0) =
      singularHomologyMap (capSection j) (n + 1) a := by
  rw [boundaryCapHomologyEquiv_symm_eq_section_add_cross, map_zero, add_zero]

@[simp] theorem boundaryCapHomologyEquiv_symm_inr (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    (boundaryCapHomologyEquiv j n).symm (0, a) = boundaryPositiveCircleCross j n a := by
  rw [boundaryCapHomologyEquiv_symm_eq_section_add_cross, map_zero, zero_add]

theorem boundaryPositiveCircleCross_injective (j : Kind) (n : ℕ) :
    Function.Injective (boundaryPositiveCircleCross j n) := by
  intro a b h
  have hc := congrArg (boundaryCapHomologyEquiv j n) h
  rw [boundaryCapHomologyEquiv_positiveCircleCross,
    boundaryCapHomologyEquiv_positiveCircleCross] at hc
  exact congrArg Prod.snd hc

/-- In degree zero the same actual cap map is an isomorphism. -/
def boundaryCapHomologyZeroEquiv (j : Kind) :
    SingularHomology (B j) 0 ≃ₗ[ℤ] SingularHomology (S j) 0 :=
  (homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) 0).trans
    (circleProductHomologyZeroEquiv (S j))

theorem boundaryCapHomologyZeroEquiv_apply (j : Kind)
    (a : SingularHomology (B j) 0) :
    boundaryCapHomologyZeroEquiv j a =
      singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) 0 a := by
  change singularHomologyMap (productProjection (S j)) 0
    (singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _)) 0 a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_projection]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

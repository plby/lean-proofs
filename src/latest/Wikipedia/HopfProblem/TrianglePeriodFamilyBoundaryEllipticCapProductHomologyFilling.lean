import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductHomologyCore
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessElliptic
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# The literal elliptic filling coefficient in cap-product coordinates

The actual small-piece retraction composed with the actual boundary
inclusion is the original central-cap map.  Consequently the actual
attachment coefficient is projection to the first product coordinate,
followed by the inverse retraction isomorphism.  In every positive degree
its kernel is exactly the genuine positive-circle cross-product summand.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology.Finiteness
open ThreefoldOverlapMappingTorus

local notation "B" => ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary
local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- Composing the literal small-piece boundary coefficient with its actual
radial retraction gives the previously identified central-cap map. -/
theorem boundaryToFilling_centralRetraction (j : Kind) :
    (EllipticGeometry.pieceSurfaceRetraction j).comp (boundaryToFilling (some j)) =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j := by
  rw [boundaryToFilling_elliptic]
  rfl

/-- The same identity holds for the actual induced singular homology maps. -/
theorem boundaryFillingHomologyMap_central (j : Kind) (n : ℕ)
    (a : SingularHomology (B j) n) :
    ellipticPieceRetractionHomologyEquiv j n (boundaryFillingHomologyMap (some j) n a) =
      singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) n a := by
  change singularHomologyMap (EllipticGeometry.pieceSurfaceRetraction j) n
    (singularHomologyMap (boundaryToFilling (some j)) n a) = _
  exact (LinearMap.congr_fun (singularHomologyMap_comp (boundaryToFilling (some j))
    (EllipticGeometry.pieceSurfaceRetraction j) n) a).symm.trans
      (congrArg (fun f : C(B j, S j) => singularHomologyMap f n a)
        (boundaryToFilling_centralRetraction j))

/-- In all positive degrees the literal filling coefficient is the cap coordinate. -/
theorem boundaryFillingHomologyMap_first (j : Kind) (n : ℕ)
    (a : SingularHomology (B j) (n + 1)) :
    ellipticPieceRetractionHomologyEquiv j (n + 1)
        (boundaryFillingHomologyMap (some j) (n + 1) a) =
      (boundaryCapHomologyEquiv j n a).1 :=
  (boundaryFillingHomologyMap_central j (n + 1) a).trans
    (boundaryCapHomologyEquiv_fst j n a).symm

/-- The filling class itself is the original central inclusion applied to
the first coordinate, with no chosen abstract splitting in the filling. -/
theorem boundaryFillingHomologyMap_eq_retraction_symm (j : Kind) (n : ℕ)
    (a : SingularHomology (B j) (n + 1)) :
    boundaryFillingHomologyMap (some j) (n + 1) a =
      (ellipticPieceRetractionHomologyEquiv j (n + 1)).symm
        (boundaryCapHomologyEquiv j n a).1 := by
  apply (ellipticPieceRetractionHomologyEquiv j (n + 1)).injective
  rw [boundaryFillingHomologyMap_first, LinearEquiv.apply_symm_apply]

/-- Under the cap section the actual boundary coefficient is the original
central-surface inclusion in the small filling. -/
@[simp] theorem boundaryFillingHomologyMap_section (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) (n + 1)) :
    boundaryFillingHomologyMap (some j) (n + 1)
        (singularHomologyMap (capSection j) (n + 1) a) =
      (ellipticPieceRetractionHomologyEquiv j (n + 1)).symm a := by
  rw [boundaryFillingHomologyMap_eq_retraction_symm, boundaryCapHomologyEquiv_section]

/-- The actual filling coefficient kills the genuine positive-circle cross product. -/
@[simp] theorem boundaryFillingHomologyMap_positiveCircleCross (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    boundaryFillingHomologyMap (some j) (n + 1) (boundaryPositiveCircleCross j n a) = 0 := by
  rw [boundaryFillingHomologyMap_eq_retraction_symm,
    boundaryCapHomologyEquiv_positiveCircleCross, map_zero]

/-- The actual boundary-to-filling homomorphism is onto in every degree. -/
theorem boundaryFillingHomologyMap_surjective (j : Kind) (n : ℕ) :
    Function.Surjective (boundaryFillingHomologyMap (some j) n) := by
  cases n with
  | zero =>
    intro a
    obtain ⟨b, hb⟩ := (boundaryCapHomologyZeroEquiv j).surjective
      (ellipticPieceRetractionHomologyEquiv j 0 a)
    refine ⟨b, (ellipticPieceRetractionHomologyEquiv j 0).injective ?_⟩
    rw [boundaryFillingHomologyMap_central, ← boundaryCapHomologyZeroEquiv_apply]
    exact hb
  | succ n =>
    intro a
    refine ⟨singularHomologyMap (capSection j) (n + 1)
      (ellipticPieceRetractionHomologyEquiv j (n + 1) a), ?_⟩
    rw [boundaryFillingHomologyMap_section, LinearEquiv.symm_apply_apply]

/-- A class is killed by the actual filling map exactly when its cap coordinate vanishes. -/
theorem boundaryFillingHomologyMap_eq_zero_iff (j : Kind) (n : ℕ)
    (a : SingularHomology (B j) (n + 1)) :
    boundaryFillingHomologyMap (some j) (n + 1) a = 0 ↔
      (boundaryCapHomologyEquiv j n a).1 = 0 := by
  constructor
  · intro h
    rw [← boundaryFillingHomologyMap_first, h, map_zero]
  · intro h
    rw [boundaryFillingHomologyMap_eq_retraction_symm, h, map_zero]

/-- The kernel is the image of the actual positive-circle cross product. -/
theorem boundaryFillingHomologyMap_ker (j : Kind) (n : ℕ) :
    LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1)) =
      LinearMap.range (boundaryPositiveCircleCross j n) := by
  ext a
  constructor
  · intro ha
    have hf := (boundaryFillingHomologyMap_eq_zero_iff j n a).mp ha
    refine ⟨(boundaryCapHomologyEquiv j n a).2, ?_⟩
    apply (boundaryCapHomologyEquiv j n).injective
    rw [boundaryCapHomologyEquiv_positiveCircleCross]
    exact Prod.ext hf.symm rfl
  · rintro ⟨b, rfl⟩
    exact boundaryFillingHomologyMap_positiveCircleCross j n b

/-- Canonical kernel coordinates retain the actual positive-circle cross product. -/
def boundaryCapKernelEquiv (j : Kind) (n : ℕ) :
    LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1)) ≃ₗ[ℤ]
      SingularHomology (S j) n :=
  ({ toFun a := (boundaryCapHomologyEquiv j n a.val).2
     map_add' a b := congrArg Prod.snd ((boundaryCapHomologyEquiv j n).map_add a.val b.val)
     invFun b := ⟨boundaryPositiveCircleCross j n b,
       boundaryFillingHomologyMap_positiveCircleCross j n b⟩
     left_inv a := by
       apply Subtype.ext
       apply (boundaryCapHomologyEquiv j n).injective
       rw [boundaryCapHomologyEquiv_positiveCircleCross]
       exact Prod.ext
         ((boundaryFillingHomologyMap_eq_zero_iff j n a.val).mp a.property).symm rfl
     right_inv b := congrArg Prod.snd (boundaryCapHomologyEquiv_positiveCircleCross j n b) } :
    LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1)) ≃+
      SingularHomology (S j) n).toIntLinearEquiv

@[simp] theorem boundaryCapKernelEquiv_apply (j : Kind) (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1))) :
    boundaryCapKernelEquiv j n a = (boundaryCapHomologyEquiv j n a.val).2 := rfl

/-- The inverse kernel isomorphism is the actual cross-product homomorphism. -/
@[simp] theorem boundaryCapKernelEquiv_symm_val (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    ((boundaryCapKernelEquiv j n).symm a).val = boundaryPositiveCircleCross j n a := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

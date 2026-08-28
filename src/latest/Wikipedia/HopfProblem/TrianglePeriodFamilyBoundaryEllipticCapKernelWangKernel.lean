import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangRanges

/-!
# Wang maps on the literal kernels of the original cap coefficients

The maps below are restrictions of the actual Wang boundary, with no
coordinate choice in their definitions.  The proved cap-kernel
isomorphism identifies them with the computed positive-circle maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus MappingTorusHomology EllipticCapProduct

/-- Restrict the actual Wang boundary to the literal kernel of the actual filling map. -/
def capKernelWang (j : Kind) (n : ℕ) :
    LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1)) →ₗ[ℤ]
      SingularHomology RealTorus₄ n where
  toFun a := wangBoundary (flatTorusAffine j j.twist) n a.val
  map_add' a b := map_add _ a.val b.val
  map_smul' k a :=
    (map_zsmul
      ((wangBoundary (flatTorusAffine j j.twist) n).toAddMonoidHom.comp
        (LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1))).subtype.toAddMonoidHom)
      k a).trans
        (int_smul_eq_zsmul (SingularHomology RealTorus₄ n).isModule k
          (wangBoundary (flatTorusAffine j j.twist) n a.val)).symm

@[simp] theorem capKernelWang_apply (j : Kind) (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1))) :
    capKernelWang j n a = wangBoundary (flatTorusAffine j j.twist) n a.val := rfl

/-- The genuine cap-kernel equivalence gives the already computed native cross map. -/
theorem capKernelWang_eq_cross (j : Kind) (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1))) :
    capKernelWang j n a = crossWang j n (boundaryCapKernelEquiv j n a) := by
  have h := (boundaryCapKernelEquiv j n).symm_apply_apply a
  have hv := congrArg
    (fun b : LinearMap.ker (boundaryFillingHomologyMap (some j) (n + 1)) => b.val) h
  change boundaryPositiveCircleCross j n (boundaryCapKernelEquiv j n a) = a.val at hv
  change wangBoundary (flatTorusAffine j j.twist) n a.val =
    wangBoundary (flatTorusAffine j j.twist) n
      (boundaryPositiveCircleCross j n (boundaryCapKernelEquiv j n a))
  rw [hv]

/-- The actual degree-two Wang restriction to the actual cap kernel is injective. -/
theorem capKernelWang_one_injective (j : Kind) : Function.Injective (capKernelWang j 1) := by
  intro a b hab
  apply (boundaryCapKernelEquiv j 1).injective
  apply h1Coordinates_injective j
  rw [h1Coordinates_apply, h1Coordinates_apply, ← capKernelWang_eq_cross,
    ← capKernelWang_eq_cross, hab]

/-- The actual degree-three Wang restriction to the actual cap kernel is injective. -/
theorem capKernelWang_two_injective (j : Kind) : Function.Injective (capKernelWang j 2) := by
  intro a b hab
  apply (boundaryCapKernelEquiv j 2).injective
  apply h2Coordinates_injective j
  rw [h2Coordinates_apply, h2Coordinates_apply, ← capKernelWang_eq_cross,
    ← capKernelWang_eq_cross, hab]

/-- The original first marking carries the literal kernel map to exactly the computed image. -/
theorem capKernelWang_one_coordinate_range (j : Kind) :
    LinearMap.range (FlatTorus.singularH1Equiv.toLinearMap.comp (capKernelWang j 1)) =
      LinearMap.range (h1Coordinates j) := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨boundaryCapKernelEquiv j 1 a, ?_⟩
    exact congrArg FlatTorus.singularH1Equiv (capKernelWang_eq_cross j 1 a).symm
  · rintro ⟨a, rfl⟩
    refine ⟨(boundaryCapKernelEquiv j 1).symm a, ?_⟩
    rfl

/-- The original second marking carries the literal kernel map to exactly the computed image. -/
theorem capKernelWang_two_coordinate_range (j : Kind) :
    LinearMap.range (FlatTorus.singularH2Coordinates.toLinearMap.comp (capKernelWang j 2)) =
      LinearMap.range (h2Coordinates j) := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨boundaryCapKernelEquiv j 2 a, ?_⟩
    exact congrArg FlatTorus.singularH2Coordinates (capKernelWang_eq_cross j 2 a).symm
  · rintro ⟨a, rfl⟩
    refine ⟨(boundaryCapKernelEquiv j 2).symm a, ?_⟩
    rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

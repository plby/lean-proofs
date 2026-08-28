import Wikipedia.HopfProblem.CuspBoundaryGammaZeroTorus
import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductFibreCoordinates

/-!
# The actual top class of the gamma-zero cusp mapping torus

The derived three-dimensional shear has determinant one. The actual
positive third-homology marking therefore proves identity monodromy.
The genuine Wang sequence, together with vanishing above the three-torus
dimension, makes its signed boundary an integral equivalence in degree
four. Its positive inverse class is normalized by the original ordered
`uwδ` fibre coordinate, without any claim about its image in a filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open SingularMayerVietoris PeriodTorusHigherHomology Elliptic.HigherHomology
open MappingTorus MappingTorusHomology
open TrianglePeriodFamily

/-- The literal zero-head fibre map is exactly the already marked coordinate subtorus. -/
theorem fibreMap_eq_capSectionFibre (j : Elliptic.Kind) :
    fibreMap = TrianglePeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j 0 := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := coordinateProjection_surjective 3 y
  rw [fibreMap_coordinateProjection,
    TrianglePeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_coordinateProjection]

/-- Every actual third-homology class maps to the positively ordered `uwδ` coordinate. -/
theorem fibreMap_h3_coordinates (a : SingularHomology (ProductTorus 3) 3) :
    FlatTorus.singularH3Coordinates (singularHomologyMap fibreMap 3 a) =
      Pi.single (3 : Fin 4) (torusH3Coordinates a) := by
  rw [fibreMap_eq_capSectionFibre .three]
  exact TrianglePeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_h3 .three a

/-- The literal top fibre class maps to the source's positive fourth cubic basis vector. -/
theorem fibreMap_h3_top :
    FlatTorus.singularH3Coordinates
      (singularHomologyMap fibreMap 3 (torusH3Coordinates.symm 1)) = Pi.single (3 : Fin 4) 1 := by
  rw [fibreMap_h3_coordinates, LinearEquiv.apply_symm_apply]

/-- Identity top monodromy is derived from the actual matrix map and its computed determinant. -/
theorem restrictedMonodromy_h3_identity :
    monodromyHomologyMap restrictedMonodromy 3 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply torusH3Coordinates.injective
  change torusH3Coordinates (singularHomologyMap (torusMatrixMap restrictedMatrix) 3 a) =
    torusH3Coordinates a
  rw [torusH3Coordinates_matrix_natural, restrictedMatrix_det, one_mul]

/-- Vanishing of the actual fourth homology of the three-torus gives Wang injectivity. -/
theorem topWang_injective : Function.Injective (wangBoundary restrictedMonodromy 3) := by
  let : Subsingleton (SingularHomology (ProductTorus 3) 4) :=
    productTorus_homology_subsingleton_of_lt (by decide : 3 < 4)
  have hzero : fibreHomologyMap restrictedMonodromy 4 = 0 := by
    apply LinearMap.ext
    intro a
    exact (congrArg (fibreHomologyMap restrictedMonodromy 4) (Subsingleton.elim a 0)).trans
      (map_zero (fibreHomologyMap restrictedMonodromy 4))
  apply LinearMap.ker_eq_bot.mp
  rw [← wang_exact_at_mappingTorus restrictedMonodromy 3, hzero, LinearMap.range_zero]

/-- The computed actual identity monodromy makes the same Wang map surjective. -/
theorem topWang_surjective : Function.Surjective (wangBoundary restrictedMonodromy 3) := by
  intro a
  have ha : a ∈ LinearMap.ker (wangDifference restrictedMonodromy 3) := by
    change a - monodromyHomologyMap restrictedMonodromy 3 a = 0
    rw [restrictedMonodromy_h3_identity, LinearMap.id_apply, sub_self]
  rw [← wangBoundary_range restrictedMonodromy 3] at ha
  exact ha

/-- The genuine signed Wang boundary itself is the top integral homology equivalence. -/
def topWangEquiv :
    SingularHomology (Torus restrictedMonodromy) 4 ≃ₗ[ℤ]
      SingularHomology (ProductTorus 3) 3 :=
  LinearEquiv.ofBijective (wangBoundary restrictedMonodromy 3)
    ⟨topWang_injective, topWang_surjective⟩

@[simp] theorem topWangEquiv_toLinearMap :
    topWangEquiv.toLinearMap = wangBoundary restrictedMonodromy 3 := rfl

@[simp] theorem topWangEquiv_apply (a : SingularHomology (Torus restrictedMonodromy) 4) :
    topWangEquiv a = wangBoundary restrictedMonodromy 3 a := rfl

/-- The actual fourth homology has its positive integer coordinate fixed by Wang. -/
def H4Coordinates : SingularHomology (Torus restrictedMonodromy) 4 ≃ₗ[ℤ] ℤ :=
  topWangEquiv.trans torusH3Coordinates

@[simp] theorem H4Coordinates_apply (a : SingularHomology (Torus restrictedMonodromy) 4) :
    H4Coordinates a = torusH3Coordinates (wangBoundary restrictedMonodromy 3 a) := rfl

/-- The canonical source class is the inverse of the positive actual Wang coordinate. -/
def fundamentalClass : SingularHomology (Torus restrictedMonodromy) 4 := H4Coordinates.symm 1

@[simp] theorem H4Coordinates_fundamentalClass : H4Coordinates fundamentalClass = 1 :=
  H4Coordinates.apply_symm_apply 1

/-- The actual boundary of this class is the positive orientation of the three-torus fibre. -/
theorem wangBoundary_fundamentalClass :
    wangBoundary restrictedMonodromy 3 fundamentalClass = torusH3Coordinates.symm 1 := by
  apply torusH3Coordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  exact H4Coordinates_fundamentalClass

/-- Every actual source class is its integer Wang coordinate times the canonical class. -/
theorem eq_smul_fundamentalClass (a : SingularHomology (Torus restrictedMonodromy) 4) :
    a = H4Coordinates a • fundamentalClass := by
  apply H4Coordinates.injective
  rw [map_zsmul, H4Coordinates_fundamentalClass]
  simp

end Wikipedia.HopfProblem.CuspBoundaryGammaZero

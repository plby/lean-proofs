import Wikipedia.HopfProblem.ThreefoldHomologyFourthWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductMarked
import Wikipedia.HopfProblem.CuspBoundaryGammaZero

/-!
# Actual boundary representatives of a fifth homology class

The original star connecting map is transported through the actual three
overlap equivalences.  Each native boundary component has the same Wang
integer.  Subtracting that integer times a genuine geometric reference
class gives a literal Wang fibre image.  No boundary matrix or regular
homology splitting is chosen.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open TrianglePeriodFamily TrianglePeriodFamily.Boundary.EllipticCapProduct
open FourthWang

/-- The original connecting class in each actual native mapping-torus overlap. -/
def nativeFifthBoundary (a : SingularHomology Space 5) (i : Puncture) :
    SingularHomology (Boundary i) 4 :=
  overlapHomologyEquiv i 4 (starConnectingHomomorphism 4 a i)

/-- Its actual Wang coordinate is the unchanged common fifth-degree integer. -/
theorem nativeFifthBoundary_wang_coordinates (a : SingularHomology Space 5) (i : Puncture) :
    FlatTorus.singularH3Coordinates (wangBoundary (monodromy i) 3 (nativeFifthBoundary a i)) =
      Pi.single 3 (fifthWangCoordinate a) :=
  fifthWangCoordinate_coordinates a i

/-- Each native connecting component has zero image in its original filling. -/
theorem nativeFifthBoundary_cap_zero (a : SingularHomology Space 5) (i : Puncture) :
    boundaryFillingHomologyMap i 4 (nativeFifthBoundary a i) = 0 := by
  have h := LinearMap.congr_fun (boundaryFillingHomologyMap_retraction i 4)
    (starConnectingHomomorphism 4 a i)
  exact h.trans (connecting_four_cap_zero a i)

/-- The sum of the actual regular-family images is zero. -/
theorem nativeFifthBoundary_regular_sum_zero (a : SingularHomology Space 5) :
    (∑ i : Puncture, boundaryRegularHomologyMap i 4 (nativeFifthBoundary a i)) = 0 := by
  calc
    _ = ∑ i : Puncture,
        singularHomologyMap (overlapToRegularFamily i) 4 (starConnectingHomomorphism 4 a i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact LinearMap.congr_fun (boundaryRegularHomologyMap_retraction i 4) _
    _ = 0 := connecting_four_regular_zero a

/-- Genuine reference classes, all with positive unit `uwδ` Wang coordinate. -/
def fifthReferenceBoundary : (i : Puncture) → SingularHomology (Boundary i) 4
  | none => CuspBoundaryGammaZero.nativeClass
  | some j => -unitCapSectionClass j

@[simp] theorem fifthReferenceBoundary_cusp :
    fifthReferenceBoundary none = CuspBoundaryGammaZero.nativeClass := rfl

@[simp] theorem fifthReferenceBoundary_elliptic (j : Elliptic.Kind) :
    fifthReferenceBoundary (some j) = -unitCapSectionClass j := rfl

/-- The reference classes use the actual native signed Wang maps. -/
theorem fifthReferenceBoundary_wang_coordinates (i : Puncture) :
    FlatTorus.singularH3Coordinates (wangBoundary (monodromy i) 3 (fifthReferenceBoundary i)) =
      Pi.single (3 : Fin 4) 1 := by
  cases i with
  | none => exact CuspBoundaryGammaZero.nativeClass_wang_coordinates
  | some j =>
    change FlatTorus.singularH3Coordinates
      (wangBoundary (Elliptic.flatTorusAffine j j.twist) 3 (-unitCapSectionClass j)) = _
    rw [map_neg, map_neg, unitCapSectionClass_wang, neg_neg]

/-- After its genuine reference class is subtracted, each native component
has zero actual Wang image. -/
theorem nativeFifthBoundary_sub_reference_wang_zero
    (a : SingularHomology Space 5) (i : Puncture) :
    wangBoundary (monodromy i) 3
      (nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i) = 0 := by
  apply FlatTorus.singularH3Coordinates.injective
  rw [map_sub, map_zsmul, map_sub, map_zsmul,
    nativeFifthBoundary_wang_coordinates, fifthReferenceBoundary_wang_coordinates, map_zero]
  ext j
  by_cases hj : j = 3
  · subst j
    simp
  · simp [Pi.single_eq_of_ne hj]

/-- Actual Wang exactness gives original real-period fibre classes, with
the displayed equality in each native boundary group. -/
theorem exists_fifth_boundary_fibres (a : SingularHomology Space 5) :
    ∃ b : Puncture → SingularHomology RealTorus₄ 4, ∀ i,
      fibreHomologyMap (monodromy i) 4 (b i) =
        nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i := by
  have h (i : Puncture) :
      nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i ∈
        LinearMap.range (fibreHomologyMap (monodromy i) 4) := by
    rw [wang_exact_at_mappingTorus (monodromy i) 3]
    exact nativeFifthBoundary_sub_reference_wang_zero a i
  choose b hb using h
  exact ⟨b, hb⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

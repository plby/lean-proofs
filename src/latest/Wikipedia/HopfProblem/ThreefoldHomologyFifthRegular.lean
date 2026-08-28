import Wikipedia.HopfProblem.ThreefoldHomologyFifthBoundary
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCommonFibre
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFourthRelation

/-!
# The full actual regular equation for fifth homology

The three geometric reference classes have zero total image in the whole
regular family's fourth homology, including its fibre term.  Every
boundary fibre map is the same literal positive normalized fibre map.
Its proved injectivity therefore forces the sum of the three original
fibre classes in a fifth-degree decomposition to be zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open TrianglePeriodFamily TrianglePeriodFamily.Boundary
open TrianglePeriodFamily.Boundary.EllipticCapProduct FourthWang

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The complete regular relation for the actual reference classes,
not just equality after taking source-kernel or Wang coordinates. -/
theorem fifthReferenceBoundary_regular_sum_zero :
    (∑ i : Puncture, boundaryRegularHomologyMap i 4 (fifthReferenceBoundary i)) = 0 := by
  classical
  have he (j : Elliptic.Kind) :
      boundaryRegularHomologyMap (some j) 4 (fifthReferenceBoundary (some j)) =
        -boundaryRegularHomologyMap (some j) 4 (unitCapSectionClass j) :=
    map_neg (boundaryRegularHomologyMap (some j) 4) (unitCapSectionClass j)
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  rw [fifthReferenceBoundary_cusp, he, he]
  rw [FourthRelation.nativeClass_regular_eq_capSections]
  abel

/-- The full original regular map forces the sum of the genuine fibre classes to vanish. -/
theorem fifth_boundary_fibres_sum_zero (a : SingularHomology Space 5)
    (b : Puncture → SingularHomology RealTorus₄ 4)
    (hb : ∀ i, fibreHomologyMap (monodromy i) 4 (b i) =
      nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i) :
    (∑ i : Puncture, b i) = 0 := by
  apply normalizedFamilyFibreHomologyFour_injective Dsp
  rw [map_sum, map_zero]
  calc
    _ = ∑ i : Puncture,
        boundaryRegularHomologyMap i 4 (fibreHomologyMap (monodromy i) 4 (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (boundaryRegularHomologyMap_common_fibre_apply i 4 (b i)).symm
    _ = ∑ i : Puncture, boundaryRegularHomologyMap i 4
        (nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i]
    _ = (∑ i : Puncture, boundaryRegularHomologyMap i 4 (nativeFifthBoundary a i)) -
        fifthWangCoordinate a •
          ∑ i : Puncture, boundaryRegularHomologyMap i 4 (fifthReferenceBoundary i) := by
      have hs (i : Puncture) :
          boundaryRegularHomologyMap i 4 (fifthWangCoordinate a • fifthReferenceBoundary i) =
            fifthWangCoordinate a • boundaryRegularHomologyMap i 4 (fifthReferenceBoundary i) :=
        map_zsmul (boundaryRegularHomologyMap i 4)
          (fifthWangCoordinate a) (fifthReferenceBoundary i)
      simp only [map_sub, hs, Finset.sum_sub_distrib]
      congr 1
      exact (map_sum
        (zsmulAddGroupHom (α := SingularHomology SpecialRegularFamily 4) (fifthWangCoordinate a))
        (fun i : Puncture => boundaryRegularHomologyMap i 4 (fifthReferenceBoundary i))
        Finset.univ).symm
    _ = 0 := by
      rw [nativeFifthBoundary_regular_sum_zero, fifthReferenceBoundary_regular_sum_zero]
      have hz := @zsmul_zero (SingularHomology SpecialRegularFamily 4) _ (fifthWangCoordinate a)
      exact (congrArg (fun x : SingularHomology SpecialRegularFamily 4 => 0 - x) hz).trans
        (sub_self 0)

/-- The equation is in the original common positive ordered torus coordinates. -/
theorem fifth_boundary_fibre_coordinates_sum_zero (a : SingularHomology Space 5)
    (b : Puncture → SingularHomology RealTorus₄ 4)
    (hb : ∀ i, fibreHomologyMap (monodromy i) 4 (b i) =
      nativeFifthBoundary a i - fifthWangCoordinate a • fifthReferenceBoundary i) :
    PeriodTorusHigherHomology.realTorusH4Equiv (b (some .three)) +
        PeriodTorusHigherHomology.realTorusH4Equiv (b (some .four)) +
        PeriodTorusHigherHomology.realTorusH4Equiv (b none) = 0 := by
  have h := congrArg PeriodTorusHigherHomology.realTorusH4Equiv
    (fifth_boundary_fibres_sum_zero a b hb)
  rw [map_sum, map_zero, Fintype.sum_option] at h
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)] at h
  omega

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

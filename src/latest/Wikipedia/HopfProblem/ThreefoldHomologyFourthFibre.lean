import Wikipedia.HopfProblem.ThreefoldHomologyFourthFibreBoundary
import Wikipedia.HopfProblem.CuspBoundaryTopVanishing
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCommonFibre
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFourthRelation

/-!
# The positive regular fourth-fibre class is a genuine cap-kernel relation

The original gamma-zero cusp class dies in the original cusp cap.  Its
complete regular image is the sum of the two actual elliptic cap sections.
Combining twelve copies of this class with four and three copies of the
two first elliptic cap-kernel axes leaves precisely one positive regular
fibre class.  Integral multiples give every actual fourth-fibre class.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthFibre

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldOverlapMappingTorus TrianglePeriodFamily TrianglePeriodFamily.Boundary
open TrianglePeriodFamily.Homology
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open CapElimination

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The original gamma-zero boundary class, in the kernel of its actual cusp cap map. -/
def cuspClass : NativeCapKernel none 4 :=
  ⟨CuspBoundaryGammaZero.nativeClass,
    CuspBoundaryTopVanishing.boundaryFillingHomologyMap_nativeClass_eq_zero⟩

@[simp] theorem cuspClass_val : cuspClass.val = CuspBoundaryGammaZero.nativeClass := rfl

/-- The literal native cap-kernel tuple producing one positive regular fibre. -/
def nativeFibrePreimage : ∀ i : Puncture, NativeCapKernel i 4
  | none => (12 : ℤ) • cuspClass
  | some .three => (4 : ℤ) • ellipticThreeClass .three ![1, 0]
  | some .four => (3 : ℤ) • ellipticThreeClass .four ![1, 0]

/-- The full actual regular image of the first order-three cap-kernel axis. -/
theorem ellipticThreeFirstAxis_regular :
    boundaryRegularHomologyMap (some Elliptic.Kind.three) 4
        (ellipticThreeClass .three ![1, 0]).val =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4
          positiveFibreClass -
        (3 : ℤ) • boundaryRegularHomologyMap (some Elliptic.Kind.three) 4
          (unitCapSectionClass .three) := by
  have h := congrArg (boundaryRegularHomologyMap (some Elliptic.Kind.three) 4)
    ellipticThreeFirstAxis_eq
  rw [map_sub, map_zsmul, boundaryRegularHomologyMap_common_fibre_apply] at h
  exact h

/-- The full actual regular image of the first order-four cap-kernel axis. -/
theorem ellipticFourFirstAxis_regular :
    boundaryRegularHomologyMap (some Elliptic.Kind.four) 4
        (ellipticThreeClass .four ![1, 0]).val =
      -singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4
          positiveFibreClass -
        (4 : ℤ) • boundaryRegularHomologyMap (some Elliptic.Kind.four) 4
          (unitCapSectionClass .four) := by
  have h := congrArg (boundaryRegularHomologyMap (some Elliptic.Kind.four) 4)
    ellipticFourFirstAxis_eq
  rw [map_sub, map_neg, map_zsmul, boundaryRegularHomologyMap_common_fibre_apply] at h
  exact h

/-- The signed integral combination has exactly the primitive positive fibre image. -/
theorem nativeFibrePreimage_map :
    nativeCapKernelRegularMap 4 nativeFibrePreimage =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4
        positiveFibreClass := by
  classical
  rw [nativeCapKernelRegularMap_apply, Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  have hc : boundaryRegularHomologyMap none 4 cuspClass.val =
      boundaryRegularHomologyMap (some Elliptic.Kind.three) 4 (unitCapSectionClass .three) +
        boundaryRegularHomologyMap (some Elliptic.Kind.four) 4 (unitCapSectionClass .four) :=
    FourthRelation.nativeClass_regular_eq_capSections
  change boundaryRegularHomologyMap none 4 ((12 : ℤ) • cuspClass.val) +
      (boundaryRegularHomologyMap (some Elliptic.Kind.three) 4
          ((4 : ℤ) • (ellipticThreeClass .three ![1, 0]).val) +
        boundaryRegularHomologyMap (some Elliptic.Kind.four) 4
          ((3 : ℤ) • (ellipticThreeClass .four ![1, 0]).val)) = _
  rw [map_zsmul, map_zsmul, map_zsmul, hc,
    ellipticThreeFirstAxis_regular, ellipticFourFirstAxis_regular]
  abel

/-- The same explicit native tuple scaled by the actual integral top marking. -/
def nativeFibrePreimageOf (a : SingularHomology RealTorus₄ 4) :
    ∀ i : Puncture, NativeCapKernel i 4 :=
  realTorusH4Equiv a • nativeFibrePreimage

/-- Every actual fourth-torus class is its marked integral multiple of the positive class. -/
theorem positiveFibreClass_spans (a : SingularHomology RealTorus₄ 4) :
    realTorusH4Equiv a • positiveFibreClass = a := by
  apply realTorusH4Equiv.injective
  rw [map_zsmul, positiveFibreClass_coordinates]
  simp

/-- The explicit preimage retains the actual normalized regular-fibre map on every class. -/
theorem nativeFibrePreimageOf_map (a : SingularHomology RealTorus₄ 4) :
    nativeCapKernelRegularMap 4 (nativeFibrePreimageOf a) =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4 a := by
  calc
    nativeCapKernelRegularMap 4 (nativeFibrePreimageOf a) =
        realTorusH4Equiv a • nativeCapKernelRegularMap 4 nativeFibrePreimage :=
      map_zsmul (nativeCapKernelRegularMap 4) (realTorusH4Equiv a) nativeFibrePreimage
    _ = realTorusH4Equiv a •
        singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4
          positiveFibreClass := congrArg (fun b => realTorusH4Equiv a • b) nativeFibrePreimage_map
    _ = singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4
        (realTorusH4Equiv a • positiveFibreClass) :=
      (map_zsmul (singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4)
        (realTorusH4Equiv a) positiveFibreClass).symm
    _ = singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4 a :=
      congrArg (singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4)
        (positiveFibreClass_spans a)

/-- All original regular fourth-fibre classes lie in the actual native cap-kernel image. -/
theorem fibre_mem_range (a : SingularHomology RealTorus₄ 4) :
    singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4 a ∈
      LinearMap.range (nativeCapKernelRegularMap 4) :=
  ⟨nativeFibrePreimageOf a, nativeFibrePreimageOf_map a⟩

/-- Image inclusion for the literal common fibre map and the original native relation map. -/
theorem fibre_range_le :
    LinearMap.range (singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 4) ≤
      LinearMap.range (nativeCapKernelRegularMap 4) := by
  rintro _ ⟨a, rfl⟩
  exact fibre_mem_range a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthFibre

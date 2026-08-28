import Wikipedia.HopfProblem.ThreefoldHomologyThirdSource

/-!
# The exact native third-degree source kernel

The actual source-zero tuples are precisely the integer multiples of
the original positive reference tuple.  The proof uses the exact
integral coordinate kernel and injectivity of the original Wang map on
each actual cap kernel.  It does not evaluate the remaining regular
fibre coefficient or assume a relation in global homology.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

open SingularMayerVietoris ThreefoldOverlapMappingTorus MappingTorusHomology
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior TrianglePeriodFamily
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open ThreefoldHomologyCuspFibre CapElimination ThirdDegree

local notation "c₃" => sourceShearTwo Kind.three
local notation "k₄" => DeltaSweep.centralSweepShearCorrection Kind.four

/-- The original degree-two Wang coordinates on one actual degree-three cap kernel. -/
def capKernelWangCoordinates (i : Puncture) : NativeCapKernel i 3 →ₗ[ℤ] (Fin 6 → ℤ) :=
  intLinearMapOfAddHom
    { toFun a := FlatTorus.singularH2Coordinates (wangBoundary (monodromy i) 2 a.val)
      map_zero' := by rw [Submodule.coe_zero, map_zero, map_zero]
      map_add' a b := by rw [Submodule.coe_add, map_add, map_add] }

@[simp] theorem capKernelWangCoordinates_apply (i : Puncture) (a : NativeCapKernel i 3) :
    capKernelWangCoordinates i a =
      FlatTorus.singularH2Coordinates (wangBoundary (monodromy i) 2 a.val) := rfl

/-- Each actual cap-kernel class is determined by its genuine Wang coordinates. -/
theorem capKernelWangCoordinates_injective (i : Puncture) :
    Function.Injective (capKernelWangCoordinates i) := by
  cases i with
  | none =>
    intro a b h
    apply (cuspCapKernelWangEquivDegree 2).injective
    apply Subtype.ext
    exact FlatTorus.singularH2Coordinates.injective h
  | some j =>
    intro a b h
    apply capKernelWang_two_injective j
    exact FlatTorus.singularH2Coordinates.injective h

/-- The original surface coordinates parametrize every actual elliptic cap-kernel class. -/
theorem ellipticTwoClass_surjective (j : Kind) : Function.Surjective (ellipticTwoClass j) := by
  intro a
  refine ⟨surfaceH2Equiv j (specialLocalData j).centralPeriod (boundaryCapKernelEquiv j 2 a), ?_⟩
  simp only [ellipticTwoClass, LinearEquiv.symm_apply_apply]

/-- The reference tuple keeps its original positive common Wang vector. -/
theorem capKernelWangCoordinates_reference (i : Puncture) :
    capKernelWangCoordinates i (referenceClasses i) = commonWangVector :=
  referenceClasses_wang i

/-- The exact integral coordinate relation has this same common Wang vector in every component. -/
theorem kernelCoordinates_wang_values (c3 k4 k : ℤ) :
    threeWangVector c3 (kernelThreeCoordinates c3 k) = k • commonWangVector ∧
      fourWangVector (2 * k4) (kernelFourCoordinates k4 k) = k • commonWangVector ∧
      kernelCuspCoordinates k = k • commonWangVector := by
  constructor
  · rw [threeWangVector_apply]
    ext i
    fin_cases i <;> simp [kernelThreeCoordinates, commonWangVector] <;> ring
  constructor
  · rw [fourWangVector_apply]
    ext i
    fin_cases i <;> simp [kernelFourCoordinates, commonWangVector] <;> ring
  · ext i
    fin_cases i <;> simp [kernelCuspCoordinates, cuspVector, commonWangVector] <;> ring

/-- Every genuine source-zero tuple is an integer multiple of the original reference tuple. -/
theorem nativeCapKernelSourceMap_two_eq_zero_exists
    (a : ∀ i : Puncture, NativeCapKernel i 3) (ha : nativeCapKernelSourceMap 2 a = 0) :
    ∃ k : ℤ, a = k • referenceClasses := by
  obtain ⟨b3, hb3⟩ := ellipticTwoClass_surjective .three (a (some .three))
  obtain ⟨b4, hb4⟩ := ellipticTwoClass_surjective .four (a (some .four))
  let v := capKernelWangCoordinates none (a none)
  have h₃ : capKernelWangCoordinates (some .three) (a (some .three)) =
      threeWangVector c₃ b3 := by
    rw [← hb3]
    exact ellipticTwoClass_wang_three b3
  have h₄ : capKernelWangCoordinates (some .four) (a (some .four)) =
      fourWangVector (2 * k₄) b4 := by
    rw [← hb4]
    exact ellipticTwoClass_wang_four b4
  have hpair : sourcePair c₃ (2 * k₄) b3 b4 v = 0 := by
    have hz :
        (FlatTorus.singularH2Coordinates (nativeCapKernelSourceMap 2 a).val.1,
          FlatTorus.singularH2Coordinates (nativeCapKernelSourceMap 2 a).val.2) = (0, 0) := by
      rw [ha]
      exact Prod.ext (map_zero _) (map_zero _)
    have hs := (nativeCapKernelSourceMap_two_coordinates a).symm.trans hz
    change (capKernelWangCoordinates (some .three) (a (some .three)) - squareA₂ *ᵥ v,
      capKernelWangCoordinates (some .four) (a (some .four)) - v) = 0 at hs
    rw [h₃, h₄] at hs
    exact hs
  obtain ⟨k, hk₃, hk₄, hkv⟩ := (sourcePair_eq_zero_iff c₃ k₄ b3 b4 v).mp hpair
  have hw := kernelCoordinates_wang_values c₃ k₄ k
  have hvalues : ∀ i : Puncture, capKernelWangCoordinates i (a i) = k • commonWangVector := by
    intro i
    cases i with
    | none => exact hkv.trans hw.2.2
    | some j =>
      cases j with
      | three => exact h₃.trans ((congrArg (threeWangVector c₃) hk₃).trans hw.1)
      | four => exact h₄.trans ((congrArg (fourWangVector (2 * k₄)) hk₄).trans hw.2.1)
  refine ⟨k, ?_⟩
  funext i
  apply capKernelWangCoordinates_injective i
  rw [Pi.smul_apply, map_smul, capKernelWangCoordinates_reference]
  exact hvalues i

/-- Exact classification of the actual source kernel, with no residual-map premise. -/
theorem nativeCapKernelSourceMap_two_eq_zero_iff (a : ∀ i : Puncture, NativeCapKernel i 3) :
    nativeCapKernelSourceMap 2 a = 0 ↔ ∃ k : ℤ, a = k • referenceClasses := by
  constructor
  · exact nativeCapKernelSourceMap_two_eq_zero_exists a
  · rintro ⟨k, rfl⟩
    rw [map_smul, referenceClasses_source_eq_zero, smul_zero]

/-- The original reference tuple has infinite order, detected by its actual Wang coordinate. -/
theorem referenceClasses_smul_injective :
    Function.Injective (fun k : ℤ => k • referenceClasses) := by
  intro k l h
  have hw := congrArg
    (fun a : ∀ i : Puncture, NativeCapKernel i 3 => capKernelWangCoordinates none (a none)) h
  simp only [Pi.smul_apply, map_smul, capKernelWangCoordinates_reference] at hw
  have h₂ : k * 2 = l * 2 := by
    simpa [commonWangVector] using congrFun hw (2 : Fin 6)
  omega

/-- Every actual source-zero tuple has a unique integer reference coefficient. -/
theorem nativeCapKernelSourceMap_two_eq_zero_existsUnique
    (a : ∀ i : Puncture, NativeCapKernel i 3) (ha : nativeCapKernelSourceMap 2 a = 0) :
    ∃! k : ℤ, a = k • referenceClasses := by
  obtain ⟨k, hk⟩ := nativeCapKernelSourceMap_two_eq_zero_exists a ha
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact referenceClasses_smul_injective (hl.symm.trans hk)

/-- The literal native source kernel is the span of the original positive reference tuple. -/
theorem nativeCapKernelSourceMap_two_ker :
    LinearMap.ker (nativeCapKernelSourceMap 2) = Submodule.span ℤ {referenceClasses} := by
  ext a
  rw [LinearMap.mem_ker, nativeCapKernelSourceMap_two_eq_zero_iff, Submodule.mem_span_singleton]
  exact exists_congr fun k => eq_comm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

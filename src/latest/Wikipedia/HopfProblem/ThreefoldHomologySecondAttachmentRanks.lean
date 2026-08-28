import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationClasses
import Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts

/-!
# Integral ranks of the actual second-degree cap kernels

Each elliptic kernel retains its actual positive-circle cross-product
coordinates.  The cusp kernel retains its genuine Wang map, whose native
first-homology invariants are exactly the original `w, δ` plane.  Thus
each original cap kernel is free of rank two, and their native product
is free of rank six.  No boundary attachment matrix is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open TrianglePeriodFamily ThreefoldHomologyCuspFibre ThreefoldHomologyFreeProducts
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open Elliptic.HigherHomology EllipticFilling CapElimination

/-- The actual cusp Wang invariant has zero first and second lattice coordinates. -/
theorem cuspWangOne_first_two_zero
    (a : LinearMap.ker (wangDifference (monodromy none) 1)) :
    FlatTorus.singularH1Equiv a.val 0 = 0 ∧ FlatTorus.singularH1Equiv a.val 1 = 0 := by
  have ha : wangDifference (monodromy none) 1 a.val = 0 := a.property
  have h := (BoundaryFirst.boundaryWangDifference_one_coordinates none a.val).symm.trans
    ((congrArg FlatTorus.singularH1Equiv ha).trans FlatTorus.singularH1Equiv.map_zero)
  change -((M₀ - 1) *ᵥ FlatTorus.singularH1Equiv a.val) = 0 at h
  exact (M₀_sub_one_kernel _).mp (neg_eq_zero.mp h)

private theorem cuspPlane_fixed (a : Fin 2 → ℤ) :
    M₀ *ᵥ ![0, 0, a 0, a 1] = ![0, 0, a 0, a 1] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Native Wang invariants in the actual unchanged two-coordinate fixed plane. -/
def cuspWangOneEquiv :
    LinearMap.ker (wangDifference (monodromy none) 1) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({ toFun a := ![FlatTorus.singularH1Equiv a.val 2, FlatTorus.singularH1Equiv a.val 3]
     invFun a := cuspOneInvariant ![0, 0, a 0, a 1] (cuspPlane_fixed a)
     left_inv a := by
       apply Subtype.ext
       apply FlatTorus.singularH1Equiv.injective
       change FlatTorus.singularH1Equiv (FlatTorus.singularH1Equiv.symm
         ![0, 0, FlatTorus.singularH1Equiv a.val 2, FlatTorus.singularH1Equiv a.val 3]) =
           FlatTorus.singularH1Equiv a.val
       rw [LinearEquiv.apply_symm_apply]
       obtain ⟨h₀, h₁⟩ := cuspWangOne_first_two_zero a
       ext i
       fin_cases i <;> simp [h₀, h₁]
     right_inv a := by
       change ![FlatTorus.singularH1Equiv (FlatTorus.singularH1Equiv.symm
           ![0, 0, a 0, a 1]) 2,
         FlatTorus.singularH1Equiv (FlatTorus.singularH1Equiv.symm
           ![0, 0, a 0, a 1]) 3] = a
       rw [LinearEquiv.apply_symm_apply]
       ext i
       fin_cases i <;> rfl
     map_add' a b := by
       ext i
       fin_cases i <;> simp [map_add] } :
    LinearMap.ker (wangDifference (monodromy none) 1) ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

@[simp] theorem cuspWangOneEquiv_apply
    (a : LinearMap.ker (wangDifference (monodromy none) 1)) :
    cuspWangOneEquiv a =
      ![FlatTorus.singularH1Equiv a.val 2, FlatTorus.singularH1Equiv a.val 3] := rfl

/-- Each actual cap kernel has two integral coordinates from its original geometric maps. -/
def nativeCapKernelTwoEquiv (i : Puncture) : NativeCapKernel i 2 ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  cases i with
  | none =>
      exact ((cuspCapKernelWangEquivDegree 1).toAddEquiv.trans
        cuspWangOneEquiv.toAddEquiv).toIntLinearEquiv
  | some j =>
      exact ((boundaryCapKernelEquiv j 1).toAddEquiv.trans
        (surfaceH1Equiv j (specialLocalData j).centralPeriod).toAddEquiv).toIntLinearEquiv

@[simp] theorem nativeCapKernelTwoEquiv_cusp_apply (a : NativeCapKernel none 2) :
    nativeCapKernelTwoEquiv none a =
      ![FlatTorus.singularH1Equiv (wangBoundary (monodromy none) 1 a.val) 2,
        FlatTorus.singularH1Equiv (wangBoundary (monodromy none) 1 a.val) 3] := rfl

@[simp] theorem nativeCapKernelTwoEquiv_elliptic_apply (j : Elliptic.Kind)
    (a : NativeCapKernel (some j) 2) :
    nativeCapKernelTwoEquiv (some j) a =
      surfaceH1Equiv j (specialLocalData j).centralPeriod (boundaryCapKernelEquiv j 1 a) := rfl

theorem nativeCapKernelTwo_free (i : Puncture) : Module.Free ℤ (NativeCapKernel i 2) :=
  Module.Free.of_equiv (nativeCapKernelTwoEquiv i).symm

theorem nativeCapKernelTwo_finite (i : Puncture) : Module.Finite ℤ (NativeCapKernel i 2) :=
  Module.Finite.of_surjective (nativeCapKernelTwoEquiv i).symm.toLinearMap
    (nativeCapKernelTwoEquiv i).symm.surjective

theorem nativeCapKernelTwo_finrank (i : Puncture) :
    Module.finrank ℤ (NativeCapKernel i 2) = 2 := by
  rw [(nativeCapKernelTwoEquiv i).finrank_eq]
  simp

/-- Freeness of the product, with its native integer action unchanged. -/
theorem nativeCapKernelsTwo_free :
    Module.Free ℤ (∀ i : Puncture, NativeCapKernel i 2) := by
  have : ∀ i : Puncture, Module.Free ℤ (NativeCapKernel i 2) := nativeCapKernelTwo_free
  exact free_pi_int (fun i : Puncture => NativeCapKernel i 2)

theorem nativeCapKernelsTwo_finite :
    Module.Finite ℤ (∀ i : Puncture, NativeCapKernel i 2) := by
  have : ∀ i : Puncture, Module.Finite ℤ (NativeCapKernel i 2) := nativeCapKernelTwo_finite
  exact Finiteness.finite_pi_int (fun i : Puncture => NativeCapKernel i 2)

theorem nativeCapKernelsTwo_finrank :
    Module.finrank ℤ (∀ i : Puncture, NativeCapKernel i 2) = 6 := by
  have : ∀ i : Puncture, Module.Free ℤ (NativeCapKernel i 2) := nativeCapKernelTwo_free
  have : ∀ i : Puncture, Module.Finite ℤ (NativeCapKernel i 2) := nativeCapKernelTwo_finite
  rw [finrank_pi_int (fun i : Puncture => NativeCapKernel i 2)]
  simp only [nativeCapKernelTwo_finrank, Finset.sum_const, Finset.card_univ, puncture_card]
  decide

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

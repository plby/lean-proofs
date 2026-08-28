import Wikipedia.HopfProblem.EllipticHigherHomologyData
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integral kernels and cokernels in exterior degree two

The difference of each actual exterior-square elliptic matrix and the
identity has a primitive rank-one kernel.  Its image is exactly the
first-coordinate-zero lattice, with explicit integral preimages.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The degree-two elliptic action minus the identity, over the integers. -/
def fibreSquareDifference (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreSquareMatrix j - 1).mulVecLin

@[simp] theorem fibreSquareDifference_three_apply (v : FibreLattice) :
    fibreSquareDifference .three v = ![0, -v 0 - v 1 + v 2, v 0 - v 1 - 2 * v 2] := by
  ext i
  fin_cases i <;>
    simp [fibreSquareDifference, fibreSquareMatrix, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg]
  all_goals ring

@[simp] theorem fibreSquareDifference_four_apply (v : FibreLattice) :
    fibreSquareDifference .four v = ![0, -v 1 - v 2, v 0 + v 1 - v 2] := by
  ext i
  fin_cases i <;>
    simp [fibreSquareDifference, fibreSquareMatrix, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg]
  ring

@[simp] theorem fibreSquareDifference_apply_zero (j : Kind) (v : FibreLattice) :
    fibreSquareDifference j v 0 = 0 := by
  cases j <;> simp

/-- The primitive integral generator of the degree-two invariant lattice. -/
def fibreSquareKernelVector : Kind → FibreLattice
  | .three => ![3, -1, 2]
  | .four => ![2, -1, 1]

@[simp] theorem fibreSquareKernelVector_three :
    fibreSquareKernelVector .three = ![3, -1, 2] := rfl

@[simp] theorem fibreSquareKernelVector_four :
    fibreSquareKernelVector .four = ![2, -1, 1] := rfl

@[simp] theorem fibreSquareKernelVector_one (j : Kind) :
    fibreSquareKernelVector j 1 = -1 := by
  cases j <;> rfl

@[simp] theorem fibreSquareDifference_kernelVector (j : Kind) :
    fibreSquareDifference j (fibreSquareKernelVector j) = 0 := by
  cases j <;> ext i <;> fin_cases i <;> simp

/-- A kernel element has the unique coefficient given by minus its second coordinate. -/
theorem fibreSquareDifference_mem_ker_iff (j : Kind) (v : FibreLattice) :
    v ∈ LinearMap.ker (fibreSquareDifference j) ↔
      v = (-v 1) • fibreSquareKernelVector j := by
  constructor
  · intro hv
    have h : fibreSquareDifference j v = 0 := hv
    cases j
    · have h₁ : -v 0 - v 1 + v 2 = 0 := by
        simpa using congrFun h 1
      have h₂ : v 0 - v 1 - 2 * v 2 = 0 := by
        simpa using congrFun h 2
      ext i
      fin_cases i <;> simp <;> omega
    · have h₁ : -v 1 - v 2 = 0 := by
        simpa using congrFun h 1
      have h₂ : v 0 + v 1 - v 2 = 0 := by
        simpa using congrFun h 2
      ext i
      fin_cases i <;> simp <;> omega
  · intro hv
    rw [LinearMap.mem_ker, hv, map_smul, fibreSquareDifference_kernelVector, smul_zero]

theorem fibreSquareDifference_ker_eq_span (j : Kind) :
    LinearMap.ker (fibreSquareDifference j) =
      Submodule.span ℤ {fibreSquareKernelVector j} := by
  ext v
  constructor
  · intro hv
    exact Submodule.mem_span_singleton.mpr
      ⟨-v 1, ((fibreSquareDifference_mem_ker_iff j v).mp hv).symm⟩
  · intro hv
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [LinearMap.mem_ker, map_smul, fibreSquareDifference_kernelVector, smul_zero]

/-- The actual integral kernel, with coordinate minus the second entry. -/
def fibreSquareKernelEquivInt (j : Kind) :
    LinearMap.ker (fibreSquareDifference j) ≃ₗ[ℤ] ℤ where
  toFun v := -(v : FibreLattice) 1
  invFun k := ⟨k • fibreSquareKernelVector j, by
    rw [LinearMap.mem_ker, map_smul, fibreSquareDifference_kernelVector, smul_zero]⟩
  left_inv v := by
    apply Subtype.ext
    exact ((fibreSquareDifference_mem_ker_iff j v).mp v.property).symm
  right_inv k := by
    change -(k • fibreSquareKernelVector j) 1 = k
    simp
  map_add' v w := by
    change -((v : FibreLattice) 1 + (w : FibreLattice) 1) =
      -(v : FibreLattice) 1 + -(w : FibreLattice) 1
    exact neg_add _ _
  map_smul' k v := by
    change -(k * (v : FibreLattice) 1) = k * (-(v : FibreLattice) 1)
    ring

@[simp] theorem fibreSquareKernelEquivInt_apply (j : Kind)
    (v : LinearMap.ker (fibreSquareDifference j)) :
    fibreSquareKernelEquivInt j v = -(v : FibreLattice) 1 := rfl

@[simp] theorem fibreSquareKernelEquivInt_symm_apply_coe (j : Kind) (k : ℤ) :
    ((fibreSquareKernelEquivInt j).symm k : FibreLattice) =
      k • fibreSquareKernelVector j := rfl

/-- An explicit integral preimage for a vector with first coordinate zero. -/
def fibreSquareRangePreimage (j : Kind) (w : FibreLattice) : FibreLattice :=
  match j with
  | .three => ![-2 * w 1 - w 2, 0, -w 1 - w 2]
  | .four => ![w 1 + w 2, -w 1, 0]

theorem fibreSquareDifference_rangePreimage (j : Kind) (w : FibreLattice)
    (hw : w 0 = 0) :
    fibreSquareDifference j (fibreSquareRangePreimage j w) = w := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreSquareRangePreimage, hw] <;> ring

/-- There are no hidden index or divisibility conditions on the image. -/
theorem fibreSquareDifference_range_iff (j : Kind) (w : FibreLattice) :
    w ∈ LinearMap.range (fibreSquareDifference j) ↔ w 0 = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact fibreSquareDifference_apply_zero j v
  · intro hw
    exact ⟨fibreSquareRangePreimage j w, fibreSquareDifference_rangePreimage j w hw⟩

theorem fibreSquareDifference_range_eq_span (j : Kind) :
    LinearMap.range (fibreSquareDifference j) =
      Submodule.span ℤ {(![0, 1, 0] : FibreLattice), ![0, 0, 1]} := by
  ext w
  rw [fibreSquareDifference_range_iff, Submodule.mem_span_pair]
  constructor
  · intro hw
    refine ⟨w 1, w 2, ?_⟩
    ext i
    fin_cases i <;> simp [hw]
  · rintro ⟨a, b, rfl⟩
    simp

/-- The primitive functional descending to the degree-two coinvariants. -/
def fibreSquareFirstCoordinate : FibreLattice →ₗ[ℤ] ℤ := LinearMap.proj 0

@[simp] theorem fibreSquareFirstCoordinate_apply (w : FibreLattice) :
    fibreSquareFirstCoordinate w = w 0 := rfl

theorem fibreSquareFirstCoordinate_surjective :
    Function.Surjective fibreSquareFirstCoordinate := by
  intro k
  exact ⟨![k, 0, 0], rfl⟩

theorem fibreSquareDifference_range_eq_ker (j : Kind) :
    LinearMap.range (fibreSquareDifference j) =
      LinearMap.ker fibreSquareFirstCoordinate := by
  ext w
  rw [fibreSquareDifference_range_iff, LinearMap.mem_ker, fibreSquareFirstCoordinate_apply]

/-- The actual degree-two coinvariants are infinite cyclic, with first-coordinate generator. -/
def fibreSquareCokernelEquivInt (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreSquareDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreSquareDifference_range_eq_ker j)).trans
    (fibreSquareFirstCoordinate.quotKerEquivOfSurjective fibreSquareFirstCoordinate_surjective)

@[simp] theorem fibreSquareCokernelEquivInt_apply_mk (j : Kind) (w : FibreLattice) :
    fibreSquareCokernelEquivInt j (Submodule.Quotient.mk w) = w 0 := by
  simp [fibreSquareCokernelEquivInt]

@[simp] theorem fibreSquareCokernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    (fibreSquareCokernelEquivInt j).symm k = Submodule.Quotient.mk ![k, 0, 0] := by
  apply (fibreSquareCokernelEquivInt j).injective
  rw [LinearEquiv.apply_symm_apply, fibreSquareCokernelEquivInt_apply_mk]
  rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology

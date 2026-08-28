import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraReduction
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The degree-two integral monodromy-difference cokernel

This calculation uses the actual exterior-square lattice matrices `squareA₁`
and `squareA₂`, not the contragredient cohomology matrices. Their combined
difference map has image exactly the kernel of the primitive functional
`x ↦ 6 * x 2 + x 3`. An explicit integral linear lift proves equality of
these lattices, including the absence of any finite-index discrepancy.

Consequently the literal quotient by the difference image is isomorphic
to the integers, with the specified coordinate functional as quotient map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior
  TrianglePeriodFamilyHomologyAlgebra

open scoped Matrix

/-- The combined degree-two difference map for the actual lattice monodromies. -/
def deltaTwo : ((Fin 6 → ℤ) × (Fin 6 → ℤ)) →ₗ[ℤ] (Fin 6 → ℤ) :=
  delta squareA₁.mulVecLin squareA₂.mulVecLin

/-- The six coordinates of the literal difference of the homology matrices. -/
theorem deltaTwo_apply (b c : Fin 6 → ℤ) :
    deltaTwo (b, c) =
      ![-b 0 + b 1 - c 0 - c 1,
        -b 0 - 2 * b 1 + c 0 - c 1,
        b 0 + c 1,
        -6 * b 0 - 6 * c 1,
        6 * b 0 + 2 * b 1 + 6 * b 2 - b 3 - b 4 + b 5 + 3 * c 1 - c 4 - c 5,
        -8 * b 0 - 2 * b 1 - 6 * b 2 + b 3 - b 4 - 2 * b 5 -
          3 * c 0 - 6 * c 1 - 6 * c 2 + c 3 + c 4 - c 5] := by
  change (squareA₁.mulVecLin b - b) + (squareA₂.mulVecLin c - c) = _
  rw [squareA₁_eq, squareA₂_eq]
  ext i
  fin_cases i <;>
    simp [dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The primitive integral functional defining the image relation. -/
def functionalTwo : (Fin 6 → ℤ) →ₗ[ℤ] ℤ where
  toFun x := 6 * x 2 + x 3
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

@[simp] theorem functionalTwo_apply (x : Fin 6 → ℤ) :
    functionalTwo x = 6 * x 2 + x 3 := rfl

/-- The fourth coordinate vector maps to the given integer. -/
@[simp] theorem functionalTwo_single_three (z : ℤ) :
    functionalTwo ![0, 0, 0, z, 0, 0] = z := by
  simp

/-- The coefficient one in the fourth coordinate makes the functional surjective. -/
theorem functionalTwo_surjective : Function.Surjective functionalTwo := by
  intro z
  exact ⟨![0, 0, 0, z, 0, 0], functionalTwo_single_three z⟩

/-- A literal integral linear lift of the projection onto the relation lattice. -/
def deltaTwoLift : (Fin 6 → ℤ) →ₗ[ℤ] ((Fin 6 → ℤ) × (Fin 6 → ℤ)) :=
  intLinearMapOfAddHom
    { toFun x :=
        (![0, -x 0 - x 1 - 2 * x 2, 0, -2 * x 0 - 2 * x 1 - x 2 - x 4, 0, 0],
         ![-2 * x 0 - x 1 - 3 * x 2, x 2, 0,
           -6 * x 0 - 3 * x 1 - 6 * x 2 + x 4 + x 5, 0, 0])
      map_zero' := by
        apply Prod.ext <;> funext i <;> fin_cases i <;> simp
      map_add' x y := by
        apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring }

@[simp] theorem deltaTwoLift_apply (x : Fin 6 → ℤ) :
    deltaTwoLift x =
      (![0, -x 0 - x 1 - 2 * x 2, 0, -2 * x 0 - 2 * x 1 - x 2 - x 4, 0, 0],
       ![-2 * x 0 - x 1 - 3 * x 2, x 2, 0,
         -6 * x 0 - 3 * x 1 - 6 * x 2 + x 4 + x 5, 0, 0]) := rfl

/-- The lift recovers every coordinate except for replacing the fourth by
the value forced by the relation equation. -/
theorem deltaTwo_deltaTwoLift (x : Fin 6 → ℤ) :
    deltaTwo (deltaTwoLift x) = ![x 0, x 1, x 2, -6 * x 2, x 4, x 5] := by
  rw [deltaTwoLift_apply, deltaTwo_apply]
  ext i
  fin_cases i <;> simp <;> ring

/-- Every vector in the functional's kernel has the displayed integral preimage. -/
theorem deltaTwo_lift (x : Fin 6 → ℤ) (hx : functionalTwo x = 0) :
    deltaTwo (deltaTwoLift x) = x := by
  rw [deltaTwo_deltaTwoLift]
  have hx3 : -6 * x 2 = x 3 := by
    change 6 * x 2 + x 3 = 0 at hx
    omega
  ext i
  fin_cases i <;> simp [hx3]

/-- Every image vector satisfies the primitive relation equation. -/
@[simp] theorem functionalTwo_deltaTwo (x : (Fin 6 → ℤ) × (Fin 6 → ℤ)) :
    functionalTwo (deltaTwo x) = 0 := by
  rcases x with ⟨b, c⟩
  rw [deltaTwo_apply, functionalTwo_apply]
  simp
  ring

/-- Equality of the actual integral relation image and the primitive kernel. -/
theorem deltaTwo_range_eq_ker : LinearMap.range deltaTwo = LinearMap.ker functionalTwo := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact functionalTwo_deltaTwo y
  · intro hx
    exact ⟨deltaTwoLift x, deltaTwo_lift x hx⟩

/-- The integral lift restricted to the actual kernel submodule. -/
def deltaTwoKernelSection :
    LinearMap.ker functionalTwo →ₗ[ℤ] ((Fin 6 → ℤ) × (Fin 6 → ℤ)) :=
  intLinearMapOfAddHom
    (deltaTwoLift.toAddMonoidHom.comp (LinearMap.ker functionalTwo).subtype.toAddMonoidHom)

/-- The kernel section is a literal right inverse of the difference map
on the underlying kernel vectors. -/
@[simp] theorem deltaTwo_deltaTwoKernelSection (x : LinearMap.ker functionalTwo) :
    deltaTwo (deltaTwoKernelSection x) = x.val :=
  deltaTwo_lift x.val x.property

/-- The actual degree-two difference cokernel is infinite cyclic, with no torsion. -/
def cokernelTwoEquiv : ((Fin 6 → ℤ) ⧸ LinearMap.range deltaTwo) ≃ₗ[ℤ] ℤ :=
  ((Submodule.quotEquivOfEq _ _ deltaTwo_range_eq_ker).toAddEquiv.trans
    (functionalTwo.quotKerEquivOfSurjective functionalTwo_surjective).toAddEquiv).toIntLinearEquiv

/-- On an actual quotient class, the equivalence is the primitive functional. -/
@[simp] theorem cokernelTwoEquiv_mk (x : Fin 6 → ℤ) :
    cokernelTwoEquiv (Submodule.Quotient.mk x) = functionalTwo x := by
  change functionalTwo.quotKerEquivOfSurjective functionalTwo_surjective
    (Submodule.quotEquivOfEq _ _ deltaTwo_range_eq_ker (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The inverse sends an integer to the corresponding fourth-coordinate class. -/
@[simp] theorem cokernelTwoEquiv_symm_apply (z : ℤ) :
    cokernelTwoEquiv.symm z = Submodule.Quotient.mk ![0, 0, 0, z, 0, 0] := by
  apply cokernelTwoEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelTwoEquiv_mk, functionalTwo_single_three]

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

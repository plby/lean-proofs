import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraReduction
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Integral difference-map images in degrees one and three

The degree-three operators are the actual exterior-cube matrices of the
lattice monodromies, not the dual cohomology matrices. Explicit integral
preimages show that both difference-map images are exactly the kernel of
the first coordinate. Thus their actual quotient cokernels are infinite
cyclic, with the first coordinate as the quotient map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

open TrianglePeriodFamilyHomologyAlgebra PeriodTorusHigherHomologyExterior
open scoped Matrix

/-- The combined degree-one lattice-monodromy difference map. -/
def deltaOne : (Lattice × Lattice) →ₗ[ℤ] Lattice :=
  delta A₁.mulVecLin A₂.mulVecLin

/-- The combined degree-three difference map on the actual exterior lattice. -/
def deltaThree : (Lattice × Lattice) →ₗ[ℤ] Lattice :=
  delta cubeA₁.mulVecLin cubeA₂.mulVecLin

/-- The shared primitive coordinate on the odd-degree cokernels. -/
def functionalOdd : Lattice →ₗ[ℤ] ℤ := LinearMap.proj 0

@[simp] theorem functionalOdd_apply (x : Lattice) : functionalOdd x = x 0 := rfl

theorem functionalOdd_surjective : Function.Surjective functionalOdd := by
  intro a
  exact ⟨![a, 0, 0, 0], rfl⟩

/-- Literal degree-one coordinates of the sum of the two variations. -/
theorem deltaOne_apply (b c : Lattice) :
    deltaOne (b, c) =
      ![0,
        6 * b 0 - b 1 + b 2 - c 1 - c 2,
        -6 * b 0 - b 1 - 2 * b 2 - 6 * c 0 + c 1 - c 2,
        -2 * b 0 + b 1 + 3 * c 0 + c 2] := by
  change (A₁ *ᵥ b - b) + (A₂ *ᵥ c - c) = _
  ext i
  fin_cases i <;>
    simp [A₁, A₂, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Literal degree-three coordinates in the ordered exterior-cube basis. -/
theorem deltaThree_apply (b c : Lattice) :
    deltaThree (b, c) =
      ![0,
        -b 0 - b 1 + b 2 - c 1 - c 2,
        b 0 - b 1 - 2 * b 2 + c 0 + c 1 - c 2,
        -2 * b 0 - 6 * b 1 + 3 * c 0 - 6 * c 2] := by
  change (cubeA₁ *ᵥ b - b) + (cubeA₂ *ᵥ c - c) = _
  rw [cubeA₁_eq, cubeA₂_eq]
  ext i
  fin_cases i <;>
    simp [dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- An integral preimage for the last three degree-one coordinates. -/
def preimageOne (x : Lattice) : Lattice × Lattice :=
  (![0, x 3, -x 1 - x 2 - 2 * x 3, 0],
    ![0, -2 * x 1 - x 2 - 3 * x 3, 0, 0])

/-- An integral preimage for the last three degree-three coordinates. -/
def preimageThree (x : Lattice) : Lattice × Lattice :=
  (![x 3, 0, x 3 - x 1 - x 2, 0], ![x 3, -2 * x 1 - x 2, 0, 0])

theorem deltaOne_preimage (x : Lattice) :
    deltaOne (preimageOne x) = ![0, x 1, x 2, x 3] := by
  rw [preimageOne, deltaOne_apply]
  ext i
  fin_cases i <;> simp <;> ring

theorem deltaThree_preimage (x : Lattice) :
    deltaThree (preimageThree x) = ![0, x 1, x 2, x 3] := by
  rw [preimageThree, deltaThree_apply]
  ext i
  fin_cases i <;> simp <;> ring

/-- The degree-one image is the full integral kernel of the first coordinate. -/
theorem deltaOne_range : LinearMap.range deltaOne = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaOne (b, c)) = 0
    rw [deltaOne_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageOne x, ?_⟩
    rw [deltaOne_preimage]
    ext i
    fin_cases i <;> simp [hx0]

/-- The degree-three image is the full integral kernel of the first coordinate. -/
theorem deltaThree_range : LinearMap.range deltaThree = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaThree (b, c)) = 0
    rw [deltaThree_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageThree x, ?_⟩
    rw [deltaThree_preimage]
    ext i
    fin_cases i <;> simp [hx0]

theorem deltaOne_range_eq_ker : LinearMap.range deltaOne = LinearMap.ker functionalOdd :=
  deltaOne_range

theorem deltaThree_range_eq_ker : LinearMap.range deltaThree = LinearMap.ker functionalOdd :=
  deltaThree_range

/-- The actual degree-one quotient cokernel, with its primitive coordinate. -/
def cokernelOneEquiv : (Lattice ⧸ LinearMap.range deltaOne) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaOne_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

/-- The actual degree-three quotient cokernel, with its primitive coordinate. -/
def cokernelThreeEquiv : (Lattice ⧸ LinearMap.range deltaThree) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaThree_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

@[simp] theorem cokernelOneEquiv_mk (x : Lattice) :
    cokernelOneEquiv (Submodule.Quotient.mk x) = x 0 := by
  simp [cokernelOneEquiv]

@[simp] theorem cokernelThreeEquiv_mk (x : Lattice) :
    cokernelThreeEquiv (Submodule.Quotient.mk x) = x 0 := by
  simp [cokernelThreeEquiv]

@[simp] theorem cokernelOneEquiv_symm_apply (a : ℤ) :
    cokernelOneEquiv.symm a = Submodule.Quotient.mk ![a, 0, 0, 0] := by
  apply cokernelOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelOneEquiv_mk]
  rfl

@[simp] theorem cokernelThreeEquiv_symm_apply (a : ℤ) :
    cokernelThreeEquiv.symm a = Submodule.Quotient.mk ![a, 0, 0, 0] := by
  apply cokernelThreeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelThreeEquiv_mk]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

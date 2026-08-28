import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeOdd

/-!
# Integral reconstruction in the degree-two source kernel

The actual degree-one variation matrices determine three coordinates of their
combined kernel.  The remaining coordinates have explicit integral preimages
under the two elliptic Wang columns and the cusp column.  Both elliptic shear
parameters remain arbitrary integers throughout the calculation.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondSource

open TrianglePeriodFamilyHomologyLattice
open scoped Matrix

/-- The three coordinate constraints imposed by the actual variation map. -/
theorem kernel_coordinates (x y : Lattice) (h : deltaOne (x, y) = 0) :
    x 2 = -4 * x 0 ∧ y 1 = 3 * y 0 ∧
      y 2 = 2 * x 0 - x 1 - 3 * y 0 := by
  rw [deltaOne_apply] at h
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  have h₃ := congrFun h 3
  change 6 * x 0 - x 1 + x 2 - y 1 - y 2 = 0 at h₁
  change -6 * x 0 - x 1 - 2 * x 2 - 6 * y 0 + y 1 - y 2 = 0 at h₂
  change -2 * x 0 + x 1 + 3 * y 0 + y 2 = 0 at h₃
  omega

/-- The fourth standard lattice vector. -/
def deltaVector : Lattice := ![0, 0, 0, 1]

/-- Coordinates for the order-three elliptic cap-kernel column. -/
def threeCoordinates (κ₃ κ₄ : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![x 3 + (x 1 - 2 * x 0) + (κ₄ * y 0 - y 3) + κ₃ * x 0, x 0]

/-- Coordinates for the order-four elliptic cap-kernel column. -/
def fourCoordinates (_x y : Lattice) : Fin 2 → ℤ := ![0, -y 0]

/-- An integral cusp-fixed vector, with the required fourth-coordinate shear. -/
def cuspCoordinates (κ₄ : ℤ) (x y : Lattice) : Lattice :=
  ![0, 0, x 1 - 2 * x 0, κ₄ * y 0 - y 3]

/-- The order-three Wang vector with an arbitrary integral covering shear. -/
def threeWangVector (κ₃ : ℤ) (a : Fin 2 → ℤ) : Lattice :=
  a 1 • ε + (a 0 - κ₃ * a 1) • deltaVector

/-- The order-four Wang vector, including the sign of the actual twist. -/
def fourWangVector (κ₄ : ℤ) (a : Fin 2 → ℤ) : Lattice :=
  a 1 • (-ε') + (2 * a 0 - κ₄ * a 1) • deltaVector

/-- The first source coordinate is reconstructed with the actual `A₂` transport. -/
theorem threeCoordinates_reconstruct (κ₃ κ₄ : ℤ) (x y : Lattice)
    (h : deltaOne (x, y) = 0) :
    threeWangVector κ₃ (threeCoordinates κ₃ κ₄ x y) -
      A₂ *ᵥ cuspCoordinates κ₄ x y = x := by
  have hx₂ := (kernel_coordinates x y h).1
  ext i
  fin_cases i <;>
    simp [threeWangVector, threeCoordinates, cuspCoordinates, deltaVector, ε, A₂, hx₂] <;>
      ring

/-- The second source coordinate is reconstructed without cusp transport. -/
theorem fourCoordinates_reconstruct (κ₄ : ℤ) (x y : Lattice)
    (h : deltaOne (x, y) = 0) :
    fourWangVector κ₄ (fourCoordinates x y) - cuspCoordinates κ₄ x y = y := by
  have hy₁ := (kernel_coordinates x y h).2.1
  have hy₂ := (kernel_coordinates x y h).2.2
  ext i
  fin_cases i <;>
    simp [fourWangVector, fourCoordinates, cuspCoordinates, deltaVector, ε', hy₁, hy₂] <;>
      ring

/-- The cusp vector lies in the fixed lattice of the actual cusp monodromy. -/
theorem cuspCoordinates_fixed (κ₄ : ℤ) (x y : Lattice) :
    M₀ *ᵥ cuspCoordinates κ₄ x y = cuspCoordinates κ₄ x y := by
  ext i
  fin_cases i <;>
    simp [cuspCoordinates, M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondSource

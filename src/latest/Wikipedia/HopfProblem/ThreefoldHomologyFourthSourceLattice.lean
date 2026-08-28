import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeOdd
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopLattice

/-!
# Integral preimages for the actual fourth-degree source columns

The two original top Wang matrices and the original exterior-cube cusp
action generate the entire kernel of the actual degree-three difference
map.  The formulas retain arbitrary integral surface shears.  In the top
coordinate the coprime coefficients three and four give an explicit
integral preimage, so no shear value or divisibility premise is needed.
-/

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthSource

open TrianglePeriodFamilyHomologyLattice PeriodTorusHigherHomologyExterior
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang

/-- The three relations forced by the literal degree-three difference map. -/
theorem deltaThree_kernel_coordinates (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    y 0 = -2 * y 1 ∧
      x 0 = -3 * (x 1 + y 1 + y 2) ∧
      x 2 = -2 * (x 1 + y 1 + y 2) := by
  have h := LinearMap.mem_ker.mp hxy
  rw [deltaThree_apply] at h
  have h₁ := congrFun h (1 : Fin 4)
  have h₂ := congrFun h (2 : Fin 4)
  have h₃ := congrFun h (3 : Fin 4)
  change -x 0 - x 1 + x 2 - y 1 - y 2 = 0 at h₁
  change x 0 - x 1 - 2 * x 2 + y 0 + y 1 - y 2 = 0 at h₂
  change -2 * x 0 - 6 * x 1 + 3 * y 0 - 6 * y 2 = 0 at h₃
  omega

/-- The original second cube sends the cusp plane to this literal vector. -/
theorem cubeA₂_cuspVector (c d : ℤ) :
    cubeA₂ *ᵥ ![0, 0, c, d] = ![0, -c, 0, d - 6 * c] := by
  rw [cubeA₂_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Every vector in this cusp plane is fixed by the actual cusp cube. -/
theorem cubeM₀_cuspVector (c d : ℤ) :
    cubeM₀ *ᵥ ![0, 0, c, d] = ![0, 0, c, d] := by
  rw [cubeM₀_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private def sourceU (c3 : ℤ) (x y : Lattice) : ℤ :=
  x 3 + 3 * c3 * (-x 1 - y 1 - y 2) - 6 * (-y 2 - y 1)

private def sourceV (c4 : ℤ) (y : Lattice) : ℤ :=
  y 3 + 2 * c4 * y 1

/-- Explicit original order-three surface coordinates, with arbitrary shear. -/
def threeCoordinates (c3 c4 : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![sourceV c4 y - sourceU c3 x y, -x 1 - y 1 - y 2]

/-- Explicit original order-four surface coordinates, with arbitrary shear. -/
def fourCoordinates (c3 c4 : ℤ) (x y : Lattice) : Fin 2 → ℤ :=
  ![sourceV c4 y - sourceU c3 x y, y 1]

/-- The simultaneous cusp correction in its unchanged exterior-cube marking. -/
def cuspCoordinates (c3 c4 : ℤ) (x y : Lattice) : Lattice :=
  ![0, 0, -y 2 - y 1, 3 * sourceV c4 y - 4 * sourceU c3 x y]

/-- The chosen cusp correction is always a genuine cusp invariant. -/
theorem cuspCoordinates_fixed (c3 c4 : ℤ) (x y : Lattice) :
    cubeM₀ *ᵥ cuspCoordinates c3 c4 x y = cuspCoordinates c3 c4 x y :=
  cubeM₀_cuspVector _ _

/-- The original order-three column, with the original cusp transport, is `x`. -/
theorem threeCoordinates_source (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    topWangMatrix .three c3 *ᵥ threeCoordinates c3 c4 x y -
      cubeA₂ *ᵥ cuspCoordinates c3 c4 x y = x := by
  obtain ⟨_, hx₀, hx₂⟩ := deltaThree_kernel_coordinates x y hxy
  rw [topWangMatrix_mulVec_three, cuspCoordinates, cubeA₂_cuspVector]
  ext i
  fin_cases i <;> simp [threeCoordinates, sourceU, sourceV, hx₀, hx₂] <;> ring

/-- The original order-four column, with the same cusp correction, is `y`. -/
theorem fourCoordinates_source (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    topWangMatrix .four c4 *ᵥ fourCoordinates c3 c4 x y -
      cuspCoordinates c3 c4 x y = y := by
  have hy₀ := (deltaThree_kernel_coordinates x y hxy).1
  rw [topWangMatrix_mulVec_four, cuspCoordinates]
  ext i
  fin_cases i <;> simp [fourCoordinates, sourceU, sourceV, hy₀] <;> ring

/-- Explicit simultaneous preimages of every actual degree-three kernel pair. -/
theorem sourceCoordinates (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    (topWangMatrix .three c3 *ᵥ threeCoordinates c3 c4 x y -
        cubeA₂ *ᵥ cuspCoordinates c3 c4 x y = x) ∧
      (topWangMatrix .four c4 *ᵥ fourCoordinates c3 c4 x y -
        cuspCoordinates c3 c4 x y = y) ∧
      cubeM₀ *ᵥ cuspCoordinates c3 c4 x y = cuspCoordinates c3 c4 x y :=
  ⟨threeCoordinates_source c3 c4 x y hxy, fourCoordinates_source c3 c4 x y hxy,
    cuspCoordinates_fixed c3 c4 x y⟩

/-- The two actual elliptic columns and the actual cusp invariants cover the kernel. -/
theorem exists_sourceCoordinates (c3 c4 : ℤ) (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    ∃ (a3 a4 : Fin 2 → ℤ) (w0 : Lattice),
      (topWangMatrix .three c3 *ᵥ a3 - cubeA₂ *ᵥ w0 = x) ∧
        (topWangMatrix .four c4 *ᵥ a4 - w0 = y) ∧ cubeM₀ *ᵥ w0 = w0 :=
  ⟨threeCoordinates c3 c4 x y, fourCoordinates c3 c4 x y,
    cuspCoordinates c3 c4 x y, sourceCoordinates c3 c4 x y hxy⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthSource

import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeTwo

/-!
# Integral reconstruction in the degree-three source kernel

The original exterior-square difference map and the original two Wang
columns admit explicit simultaneous integral preimages when the
order-four shear is written as `2 * k4`.  This is the even-shear algebra
calculation; no parity assertion about the geometric shear is made here.
The order-three shear remains an arbitrary integer throughout.
-/

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

open TrianglePeriodFamilyHomologyLattice PeriodTorusHigherHomologyExterior

/-- The original order-three Wang column with its retained integral shear. -/
def threeWangVector (c3 : ℤ) (a : Fin 2 → ℤ) : Fin 6 → ℤ :=
  (a 0 - c3 * a 1) • ![0, 0, 0, 3, -1, 2] + a 1 • ![0, 0, 1, 0, 2, -4]

/-- The original order-four column, before imposing an even shear. -/
def fourWangVector (c4 : ℤ) (a : Fin 2 → ℤ) : Fin 6 → ℤ :=
  (2 * a 0 - c4 * a 1) • ![0, 0, 0, 2, -1, 1] + a 1 • ![0, 0, -1, 0, -3, 3]

theorem threeWangVector_apply (c3 : ℤ) (a : Fin 2 → ℤ) :
    threeWangVector c3 a =
      ![0, 0, a 1, 3 * (a 0 - c3 * a 1),
        -(a 0 - c3 * a 1) + 2 * a 1, 2 * (a 0 - c3 * a 1) - 4 * a 1] := by
  ext i
  fin_cases i <;> simp [threeWangVector] <;> ring

theorem fourWangVector_apply (c4 : ℤ) (a : Fin 2 → ℤ) :
    fourWangVector c4 a =
      ![0, 0, -a 1, 2 * (2 * a 0 - c4 * a 1),
        -(2 * a 0 - c4 * a 1) - 3 * a 1, (2 * a 0 - c4 * a 1) + 3 * a 1] := by
  ext i
  fin_cases i <;> simp [fourWangVector] <;> ring

theorem threeWangVector_fixed (c3 : ℤ) (a : Fin 2 → ℤ) :
    squareA₁ *ᵥ threeWangVector c3 a = threeWangVector c3 a := by
  rw [threeWangVector_apply, squareA₁_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem fourWangVector_fixed (c4 : ℤ) (a : Fin 2 → ℤ) :
    squareA₂ *ᵥ fourWangVector c4 a = fourWangVector c4 a := by
  rw [fourWangVector_apply, squareA₂_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The literal fixed-plane coordinates of the original cusp square. -/
def cuspVector (b c d e : ℤ) : Fin 6 → ℤ := ![0, b, c, d, -b, e]

theorem squareM₀_fixed_iff (v : Fin 6 → ℤ) :
    squareM₀ *ᵥ v = v ↔ v 0 = 0 ∧ v 4 = -v 1 := by
  constructor
  · intro h
    have h₁ := congrFun h (1 : Fin 6)
    have h₅ := congrFun h (5 : Fin 6)
    simp [squareM₀_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₅
    omega
  · rintro ⟨h₀, h₄⟩
    ext i
    fin_cases i <;>
      simp [squareM₀_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₀, h₄]

theorem cuspVector_fixed (b c d e : ℤ) :
    squareM₀ *ᵥ cuspVector b c d e = cuspVector b c d e := by
  apply (squareM₀_fixed_iff _).mpr
  exact ⟨rfl, rfl⟩

/-- The actual second-generator transport of every cusp invariant. -/
theorem squareA₂_cuspVector (b c d e : ℤ) :
    squareA₂ *ᵥ cuspVector b c d e =
      ![-b, 0, b + c, d - 6 * b, 3 * b - e, d - 7 * b - 6 * c] := by
  rw [squareA₂_eq]
  ext i
  fin_cases i <;> simp [cuspVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The unchanged signed pair of source columns. -/
def sourcePair (c3 c4 : ℤ) (a3 a4 : Fin 2 → ℤ) (v : Fin 6 → ℤ) :
    (Fin 6 → ℤ) × (Fin 6 → ℤ) :=
  (threeWangVector c3 a3 - squareA₂ *ᵥ v, fourWangVector c4 a4 - v)

/-- These actual columns land in the actual difference kernel on cusp invariants. -/
theorem sourcePair_mem_ker (c3 c4 : ℤ) (a3 a4 : Fin 2 → ℤ) (v : Fin 6 → ℤ)
    (hv : squareM₀ *ᵥ v = v) : sourcePair c3 c4 a3 a4 v ∈ LinearMap.ker deltaTwo := by
  obtain ⟨h₀, h₄⟩ := (squareM₀_fixed_iff v).mp hv
  change deltaTwo (threeWangVector c3 a3 - squareA₂ *ᵥ v, fourWangVector c4 a4 - v) = 0
  rw [deltaTwo_apply]
  ext i
  fin_cases i <;>
    simp [threeWangVector, fourWangVector, squareA₂_eq,
      dotProduct, Fin.sum_univ_succ, h₀, h₄] <;> ring

/-- The five dependent coordinates forced by the actual exterior-square difference map. -/
theorem kernel_coordinates (x y : Fin 6 → ℤ) (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    x 1 = 0 ∧ y 0 = 0 ∧ y 1 = -x 0 ∧
      y 3 = 5 * x 0 + 12 * x 2 - 2 * x 3 + 3 * x 5 + 6 * y 2 - 2 * y 4 ∧
      y 5 = 3 * x 0 + 6 * x 2 - x 3 - x 4 + x 5 - y 4 := by
  have h := LinearMap.mem_ker.mp hxy
  rw [deltaTwo_apply] at h
  have h₀ := congrFun h (0 : Fin 6)
  have h₁ := congrFun h (1 : Fin 6)
  have h₂ := congrFun h (2 : Fin 6)
  have h₄ := congrFun h (4 : Fin 6)
  have h₅ := congrFun h (5 : Fin 6)
  change -x 0 + x 1 - y 0 - y 1 = 0 at h₀
  change -x 0 - 2 * x 1 + y 0 - y 1 = 0 at h₁
  change x 0 + y 1 = 0 at h₂
  change 6 * x 0 + 2 * x 1 + 6 * x 2 - x 3 - x 4 + x 5 +
    3 * y 1 - y 4 - y 5 = 0 at h₄
  change -8 * x 0 - 2 * x 1 - 6 * x 2 + x 3 - x 4 - 2 * x 5 -
    3 * y 0 - 6 * y 1 - 6 * y 2 + y 3 + y 4 - y 5 = 0 at h₅
  omega

private def sourceC (x y : Fin 6 → ℤ) : ℤ := x 0 - y 4 - y 2

private def sourceBThree (x y : Fin 6 → ℤ) : ℤ := x 2 + x 0 + sourceC x y

private def sourceBFour (x y : Fin 6 → ℤ) : ℤ := -y 2 - sourceC x y

private def sourceAlpha (x y : Fin 6 → ℤ) : ℤ :=
  x 3 - x 5 - 4 * x 2 - 3 * x 0 + 2 * sourceC x y

/-- The original order-three surface coordinates of an integral preimage. -/
def threeCoordinates (c3 : ℤ) (x y : Fin 6 → ℤ) : Fin 2 → ℤ :=
  ![sourceAlpha x y + c3 * sourceBThree x y, sourceBThree x y]

/-- Integral order-four coordinates for the shear `2 * k4`. -/
def fourCoordinates (k4 : ℤ) (x y : Fin 6 → ℤ) : Fin 2 → ℤ :=
  ![(2 - k4) * (x 0 - y 4), sourceBFour x y]

/-- The common cusp correction in the original six-minor marking. -/
def cuspCoordinates (x y : Fin 6 → ℤ) : Fin 6 → ℤ :=
  cuspVector (x 0) (sourceC x y) (3 * sourceAlpha x y + 6 * x 0 - x 3)
    (x 4 + sourceAlpha x y - 2 * sourceBThree x y + 3 * x 0)

theorem cuspCoordinates_fixed (x y : Fin 6 → ℤ) :
    squareM₀ *ᵥ cuspCoordinates x y = cuspCoordinates x y :=
  cuspVector_fixed _ _ _ _

theorem threeCoordinates_source (c3 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    threeWangVector c3 (threeCoordinates c3 x y) - squareA₂ *ᵥ cuspCoordinates x y = x := by
  have hx₁ := (kernel_coordinates x y hxy).1
  rw [threeWangVector_apply, cuspCoordinates, squareA₂_cuspVector]
  ext i
  fin_cases i <;>
    simp [threeCoordinates, sourceAlpha, sourceBThree, sourceC, hx₁] <;> ring

theorem fourCoordinates_source (k4 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    fourWangVector (2 * k4) (fourCoordinates k4 x y) - cuspCoordinates x y = y := by
  obtain ⟨_, hy₀, hy₁, hy₃, hy₅⟩ := kernel_coordinates x y hxy
  rw [fourWangVector_apply, cuspCoordinates]
  ext i
  fin_cases i <;>
    simp [fourCoordinates, cuspVector, sourceAlpha, sourceBThree, sourceBFour, sourceC,
      hy₀, hy₁, hy₃, hy₅] <;> ring

/-- Explicit simultaneous integral reconstruction with the actual cusp invariant. -/
theorem sourceCoordinates (c3 k4 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    (threeWangVector c3 (threeCoordinates c3 x y) - squareA₂ *ᵥ cuspCoordinates x y = x) ∧
      (fourWangVector (2 * k4) (fourCoordinates k4 x y) - cuspCoordinates x y = y) ∧
      squareM₀ *ᵥ cuspCoordinates x y = cuspCoordinates x y :=
  ⟨threeCoordinates_source c3 x y hxy, fourCoordinates_source k4 x y hxy,
    cuspCoordinates_fixed x y⟩

/-- The original columns with even order-four shear cover the actual difference kernel. -/
theorem exists_sourceCoordinates (c3 k4 : ℤ) (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    ∃ (a3 a4 : Fin 2 → ℤ) (v : Fin 6 → ℤ),
      sourcePair c3 (2 * k4) a3 a4 v = (x, y) ∧ squareM₀ *ᵥ v = v :=
  ⟨threeCoordinates c3 x y, fourCoordinates k4 x y, cuspCoordinates x y,
    Prod.ext (threeCoordinates_source c3 x y hxy) (fourCoordinates_source k4 x y hxy),
    cuspCoordinates_fixed x y⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

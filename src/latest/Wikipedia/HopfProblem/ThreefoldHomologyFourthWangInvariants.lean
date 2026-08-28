import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceCoordinates

/-!
# The common third-homology invariant in the original source marking

The actual exterior-cube matrices of the two source generators have
exactly one common integral invariant direction, the ordered `uwδ`
coordinate.  This is proved on the original integral lattice and then
transported through the genuine marked third homology of the real torus.
The dual cohomology matrices are not substituted for these homology maps.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang

open SingularMayerVietoris TrianglePeriodFamily
open TrianglePeriodFamily.Homology TrianglePeriodFamily.HomologyDifference
open PeriodTorusHigherHomologyExterior

/-- The literal common invariant lattice of the two exterior-cube matrices. -/
theorem commonCubeInvariant_iff (v : Fin 4 → ℤ) :
    (cubeA₁ *ᵥ v = v ∧ cubeA₂ *ᵥ v = v) ↔ v = Pi.single 3 (v 3) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have h11 := congrFun h₁ 1
    have h13 := congrFun h₁ 3
    have h21 := congrFun h₂ 1
    simp [cubeA₁_eq, cubeA₂_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      at h11 h13 h21
    have hz : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by omega
    ext i
    fin_cases i <;> simp [hz.1, hz.2.1, hz.2.2]
  · intro h
    rw [h]
    constructor <;> ext i <;> fin_cases i <;>
      simp [cubeA₁_eq, cubeA₂_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- In native third homology the common invariants are precisely the actual `uwδ` classes. -/
theorem commonThirdInvariant_iff (a : SingularHomology RealTorus₄ 3) :
    (generatorHomologyEquiv false 3 a = a ∧ generatorHomologyEquiv true 3 a = a) ↔
      FlatTorus.singularH3Coordinates a =
        Pi.single 3 (FlatTorus.singularH3Coordinates a 3) := by
  rw [← commonCubeInvariant_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h := congrArg FlatTorus.singularH3Coordinates h₁
      simpa only [generatorHomologyThree_coordinates, Bool.false_eq_true, if_false] using h
    · have h := congrArg FlatTorus.singularH3Coordinates h₂
      simpa only [generatorHomologyThree_coordinates, if_true] using h
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply FlatTorus.singularH3Coordinates.injective
      simpa only [generatorHomologyThree_coordinates, Bool.false_eq_true, if_false] using h₁
    · apply FlatTorus.singularH3Coordinates.injective
      simpa only [generatorHomologyThree_coordinates, if_true] using h₂

/-- The common invariant class is specified in the original ordered homology coordinates. -/
def commonThirdClass (k : ℤ) : SingularHomology RealTorus₄ 3 :=
  FlatTorus.singularH3Coordinates.symm (Pi.single 3 k)

@[simp] theorem commonThirdClass_coordinates (k : ℤ) :
    FlatTorus.singularH3Coordinates (commonThirdClass k) = Pi.single 3 k :=
  LinearEquiv.apply_symm_apply _ _

theorem commonThirdClass_fixed (k : ℤ) :
    generatorHomologyEquiv false 3 (commonThirdClass k) = commonThirdClass k ∧
      generatorHomologyEquiv true 3 (commonThirdClass k) = commonThirdClass k := by
  apply (commonThirdInvariant_iff _).mpr
  rw [commonThirdClass_coordinates]
  simp

theorem eq_commonThirdClass_of_fixed (a : SingularHomology RealTorus₄ 3)
    (h₁ : generatorHomologyEquiv false 3 a = a)
    (h₂ : generatorHomologyEquiv true 3 a = a) :
    a = commonThirdClass (FlatTorus.singularH3Coordinates a 3) := by
  apply FlatTorus.singularH3Coordinates.injective
  rw [commonThirdClass_coordinates]
  exact (commonThirdInvariant_iff a).mp ⟨h₁, h₂⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang

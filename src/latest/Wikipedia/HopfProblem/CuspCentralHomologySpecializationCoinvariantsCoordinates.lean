import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Integral coordinates for the single cusp-monodromy coinvariants

These are the coinvariants of the actual lattice matrix `M₀` and its ordered
exterior-square and exterior-cube matrices. Explicit integral sections prove
that the quotients have respectively two, four, and two free coordinates.
Only the single cusp action is used, not the joint relations of other
monodromy matrices or their dual actions.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

open PeriodTorusHigherHomologyExterior

/-- The degree-one difference for the actual cusp lattice monodromy. -/
def oneDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := (M₀ - 1).mulVecLin

/-- The difference of the actual ordered exterior-square matrix from identity. -/
def squareDifference : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) := (squareM₀ - 1).mulVecLin

/-- The difference of the actual ordered exterior-cube matrix from identity. -/
def cubeDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := (cubeM₀ - 1).mulVecLin

@[simp] theorem oneDifference_apply (v : Fin 4 → ℤ) :
    oneDifference v = ![0, 0, v 1, -v 0] := M₀_sub_one_mulVec v

@[simp] theorem squareDifference_apply (v : Fin 6 → ℤ) :
    squareDifference v = ![0, v 0, 0, 0, v 0, v 0 + v 1 + v 4] := by
  ext i
  fin_cases i <;>
    simp [squareDifference, squareM₀_eq, dotProduct, Fin.sum_univ_succ]
  ring

theorem cubeM₀_eq_M₀ : cubeM₀ = M₀ := by
  rw [cubeM₀_eq]
  rfl

theorem cubeDifference_eq_oneDifference : cubeDifference = oneDifference := by
  rw [cubeDifference, oneDifference, cubeM₀_eq_M₀]

@[simp] theorem cubeDifference_apply (v : Fin 4 → ℤ) :
    cubeDifference v = ![0, 0, v 1, -v 0] := by
  rw [cubeDifference_eq_oneDifference, oneDifference_apply]

/-! ## Four integral quotient coordinates in degree two -/

/-- The exact four coordinates surviving the exterior-square cusp action. -/
def squareProjection : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun v := ![v 0, v 2, v 3, v 4 - v 1]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp
    ring

@[simp] theorem squareProjection_apply (v : Fin 6 → ℤ) :
    squareProjection v = ![v 0, v 2, v 3, v 4 - v 1] := rfl

/-- An explicit integral representative of each exterior-square coinvariant. -/
def squareSection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun z := ![z 0, 0, z 1, z 2, z 3, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

@[simp] theorem squareSection_apply (z : Fin 4 → ℤ) :
    squareSection z = ![z 0, 0, z 1, z 2, z 3, 0] := rfl

@[simp] theorem squareProjection_section (z : Fin 4 → ℤ) :
    squareProjection (squareSection z) = z := by
  ext i
  fin_cases i <;> simp [squareProjection, squareSection]

theorem squareProjection_surjective : Function.Surjective squareProjection :=
  fun z => ⟨squareSection z, squareProjection_section z⟩

theorem squareDifference_eq_zero_iff (v : Fin 6 → ℤ) :
    squareDifference v = 0 ↔ v 0 = 0 ∧ v 1 + v 4 = 0 := by
  rw [squareDifference_apply]
  constructor
  · intro h
    have h0 := congrFun h 1
    have h5 := congrFun h 5
    change v 0 = 0 at h0
    change v 0 + v 1 + v 4 = 0 at h5
    exact ⟨h0, by omega⟩
  · rintro ⟨h0, h14⟩
    ext i
    fin_cases i <;> simp [h0, h14]

/-- Exact range membership, with an integral preimage for every allowed vector. -/
theorem squareDifference_range_iff (v : Fin 6 → ℤ) :
    v ∈ LinearMap.range squareDifference ↔
      v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  change (∃ w, squareDifference w = v) ↔ _
  constructor
  · rintro ⟨w, rfl⟩
    simp
  · rintro ⟨h0, h2, h3, h41⟩
    refine ⟨![v 1, v 5 - v 1, 0, 0, 0, 0], ?_⟩
    rw [squareDifference_apply]
    ext i
    fin_cases i <;> simp [h0, h2, h3, h41]

theorem squareProjection_eq_zero_iff (v : Fin 6 → ℤ) :
    squareProjection v = 0 ↔
      v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    change v 0 = 0 at h0
    change v 2 = 0 at h1
    change v 3 = 0 at h2
    change v 4 - v 1 = 0 at h3
    exact ⟨h0, h1, h2, sub_eq_zero.mp h3⟩
  · rintro ⟨h0, h2, h3, h41⟩
    ext i
    fin_cases i <;> simp [squareProjection, h0, h2, h3, h41]

theorem squareProjection_ker_eq_range :
    LinearMap.ker squareProjection = LinearMap.range squareDifference := by
  ext v
  rw [LinearMap.mem_ker, squareProjection_eq_zero_iff, squareDifference_range_iff]

/-- The actual single-action exterior-square coinvariants, with four free coordinates. -/
def squareCoinvariantEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range squareDifference) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ squareProjection_ker_eq_range.symm).trans
    (squareProjection.quotKerEquivOfSurjective squareProjection_surjective)

@[simp] theorem squareCoinvariantEquiv_mk (v : Fin 6 → ℤ) :
    squareCoinvariantEquiv (Submodule.Quotient.mk v) = ![v 0, v 2, v 3, v 4 - v 1] := by
  simp [squareCoinvariantEquiv]

@[simp] theorem squareCoinvariantEquiv_symm_apply (z : Fin 4 → ℤ) :
    squareCoinvariantEquiv.symm z = Submodule.Quotient.mk (squareSection z) := by
  apply squareCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, squareCoinvariantEquiv_mk]
  exact (squareProjection_section z).symm

/-! ## Two integral quotient coordinates in degrees one and three -/

/-- The first two lattice coordinates survive the single degree-one cusp action. -/
def oneProjection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v 0, v 1]
  map_add' v w := by
    ext i
    fin_cases i <;> rfl
  map_smul' c v := by
    ext i
    fin_cases i <;> rfl

@[simp] theorem oneProjection_apply (v : Fin 4 → ℤ) :
    oneProjection v = ![v 0, v 1] := rfl

/-- The representative with its last two coordinates set to zero. -/
def oneSection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun z := ![z 0, z 1, 0, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

@[simp] theorem oneSection_apply (z : Fin 2 → ℤ) :
    oneSection z = ![z 0, z 1, 0, 0] := rfl

@[simp] theorem oneProjection_section (z : Fin 2 → ℤ) :
    oneProjection (oneSection z) = z := by
  ext i
  fin_cases i <;> rfl

theorem oneProjection_surjective : Function.Surjective oneProjection :=
  fun z => ⟨oneSection z, oneProjection_section z⟩

theorem oneDifference_eq_zero_iff (v : Fin 4 → ℤ) :
    oneDifference v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := M₀_sub_one_kernel v

theorem oneDifference_range_iff (v : Fin 4 → ℤ) :
    v ∈ LinearMap.range oneDifference ↔ v 0 = 0 ∧ v 1 = 0 := M₀_sub_one_range v

theorem oneProjection_eq_zero_iff (v : Fin 4 → ℤ) :
    oneProjection v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [oneProjection, h0, h1]

theorem oneProjection_ker_eq_range :
    LinearMap.ker oneProjection = LinearMap.range oneDifference := by
  ext v
  rw [LinearMap.mem_ker, oneProjection_eq_zero_iff, oneDifference_range_iff]

/-- The actual single-action degree-one coinvariants. -/
def oneCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range oneDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ oneProjection_ker_eq_range.symm).trans
    (oneProjection.quotKerEquivOfSurjective oneProjection_surjective)

@[simp] theorem oneCoinvariantEquiv_mk (v : Fin 4 → ℤ) :
    oneCoinvariantEquiv (Submodule.Quotient.mk v) = ![v 0, v 1] := by
  simp [oneCoinvariantEquiv]

@[simp] theorem oneCoinvariantEquiv_symm_apply (z : Fin 2 → ℤ) :
    oneCoinvariantEquiv.symm z = Submodule.Quotient.mk (oneSection z) := by
  apply oneCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, oneCoinvariantEquiv_mk]
  exact (oneProjection_section z).symm

/-- The cube matrix has the same literal quotient projection. -/
abbrev cubeProjection := oneProjection

/-- The same integral section in the ordered exterior-cube coordinates. -/
abbrev cubeSection := oneSection

@[simp] theorem cubeProjection_apply (v : Fin 4 → ℤ) :
    cubeProjection v = ![v 0, v 1] := rfl

@[simp] theorem cubeSection_apply (z : Fin 2 → ℤ) :
    cubeSection z = ![z 0, z 1, 0, 0] := rfl

@[simp] theorem cubeProjection_section (z : Fin 2 → ℤ) :
    cubeProjection (cubeSection z) = z := oneProjection_section z

theorem cubeProjection_surjective : Function.Surjective cubeProjection := oneProjection_surjective

theorem cubeDifference_eq_zero_iff (v : Fin 4 → ℤ) :
    cubeDifference v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [cubeDifference_eq_oneDifference, oneDifference_eq_zero_iff]

theorem cubeDifference_range_iff (v : Fin 4 → ℤ) :
    v ∈ LinearMap.range cubeDifference ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [cubeDifference_eq_oneDifference, oneDifference_range_iff]

theorem cubeProjection_eq_zero_iff (v : Fin 4 → ℤ) :
    cubeProjection v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := oneProjection_eq_zero_iff v

theorem cubeProjection_ker_eq_range :
    LinearMap.ker cubeProjection = LinearMap.range cubeDifference := by
  rw [cubeDifference_eq_oneDifference]
  exact oneProjection_ker_eq_range

/-- The actual single-action exterior-cube coinvariants, with two free coordinates. -/
def cubeCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range cubeDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ cubeProjection_ker_eq_range.symm).trans
    (cubeProjection.quotKerEquivOfSurjective cubeProjection_surjective)

@[simp] theorem cubeCoinvariantEquiv_mk (v : Fin 4 → ℤ) :
    cubeCoinvariantEquiv (Submodule.Quotient.mk v) = ![v 0, v 1] := by
  simp [cubeCoinvariantEquiv]

@[simp] theorem cubeCoinvariantEquiv_symm_apply (z : Fin 2 → ℤ) :
    cubeCoinvariantEquiv.symm z = Submodule.Quotient.mk (cubeSection z) := by
  apply cubeCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cubeCoinvariantEquiv_mk]
  exact (cubeProjection_section z).symm

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

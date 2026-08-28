import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Integral fixed vectors of the actual transpose matrices

These are algebraic computations for the transpose of the original cusp
matrix and its actual ordered exterior-minor matrices.  The degree-two
order is `γu, γw, γδ, uw, uδ, wδ`; the degree-three order is
`γuw, γuδ, γwδ, uwδ`.  The integral sections below parametrize the entire
fixed sublattices, not merely finite-index subgroups.

This file makes no identification with native cohomology.  In particular,
it does not identify these transpose maps with inverse-dual transport.
-/

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open PeriodTorusHigherHomologyExterior LocalSystemMatrices

/-- The literal transpose action of the original degree-one cusp matrix. -/
theorem transpose_M₀_mulVec (x : Fin 4 → ℤ) :
    M₀.transpose *ᵥ x = ![x 0 - x 3, x 1 + x 2, x 2, x 3] := by
  ext i
  fin_cases i <;>
    simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]

/-- Fixed degree-one vectors in the original ordered basis. -/
theorem transpose_M₀_fixed_iff (x : Fin 4 → ℤ) :
    M₀.transpose *ᵥ x = x ↔ x 2 = 0 ∧ x 3 = 0 := by
  rw [transpose_M₀_mulVec]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change x 0 - x 3 = x 0 at h0
    change x 1 + x 2 = x 1 at h1
    exact ⟨by omega, by omega⟩
  · rintro ⟨h2, h3⟩
    ext i
    fin_cases i <;> simp [h2, h3]

theorem transpose_M₀_fixed_iff_exists (x : Fin 4 → ℤ) :
    M₀.transpose *ᵥ x = x ↔ ∃ a b : ℤ, x = ![a, b, 0, 0] := by
  rw [transpose_M₀_fixed_iff]
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨x 0, x 1, ?_⟩
    ext i
    fin_cases i <;> simp [h2, h3]
  · rintro ⟨a, b, rfl⟩
    simp

/-- The literal transpose of the actual ordered exterior-square matrix. -/
theorem transpose_squareM₀_mulVec (x : Fin 6 → ℤ) :
    squareM₀.transpose *ᵥ x =
      ![x 0 + x 1 + x 4 + x 5, x 1 + x 5, x 2, x 3, x 4 + x 5, x 5] := by
  rw [squareM₀_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- Fixed degree-two vectors satisfy these two exact integral equations. -/
theorem transpose_squareM₀_fixed_iff (x : Fin 6 → ℤ) :
    squareM₀.transpose *ᵥ x = x ↔ x 4 = -x 1 ∧ x 5 = 0 := by
  rw [transpose_squareM₀_mulVec]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change x 0 + x 1 + x 4 + x 5 = x 0 at h0
    change x 1 + x 5 = x 1 at h1
    exact ⟨by omega, by omega⟩
  · rintro ⟨h4, h5⟩
    ext i
    fin_cases i <;> simp [h4, h5]

theorem transpose_squareM₀_fixed_iff_exists (x : Fin 6 → ℤ) :
    squareM₀.transpose *ᵥ x = x ↔
      ∃ a b c d : ℤ, x = ![a, b, c, d, -b, 0] := by
  rw [transpose_squareM₀_fixed_iff]
  constructor
  · rintro ⟨h4, h5⟩
    refine ⟨x 0, x 1, x 2, x 3, ?_⟩
    ext i
    fin_cases i <;> simp [h4, h5]
  · rintro ⟨a, b, c, d, rfl⟩
    simp

/-- The literal transpose of the actual ordered exterior-cube matrix. -/
theorem transpose_cubeM₀_mulVec (x : Fin 4 → ℤ) :
    cubeM₀.transpose *ᵥ x = ![x 0 - x 3, x 1 + x 2, x 2, x 3] := by
  rw [cubeM₀_eq]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]

/-- Fixed degree-three vectors in the original ordered minor basis. -/
theorem transpose_cubeM₀_fixed_iff (x : Fin 4 → ℤ) :
    cubeM₀.transpose *ᵥ x = x ↔ x 2 = 0 ∧ x 3 = 0 := by
  rw [transpose_cubeM₀_mulVec, ← transpose_M₀_mulVec, transpose_M₀_fixed_iff]

theorem transpose_cubeM₀_fixed_iff_exists (x : Fin 4 → ℤ) :
    cubeM₀.transpose *ᵥ x = x ↔ ∃ a b : ℤ, x = ![a, b, 0, 0] := by
  rw [transpose_cubeM₀_mulVec, ← transpose_M₀_mulVec, transpose_M₀_fixed_iff_exists]

/-! ## Explicit integral parametrizations -/

/-- The two free integral coordinates of the degree-one fixed sublattice. -/
def oneFixedSection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun z := ![z 0, z 1, 0, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

@[simp] theorem oneFixedSection_apply (z : Fin 2 → ℤ) :
    oneFixedSection z = ![z 0, z 1, 0, 0] := rfl

theorem oneFixedSection_injective : Function.Injective oneFixedSection := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

/-- The four free coordinates include the primitive combination `γw - uδ`. -/
def twoFixedSection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun z := ![z 0, z 1, z 2, z 3, -z 1, 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [neg_add_rev, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

@[simp] theorem twoFixedSection_apply (z : Fin 4 → ℤ) :
    twoFixedSection z = ![z 0, z 1, z 2, z 3, -z 1, 0] := rfl

theorem twoFixedSection_injective : Function.Injective twoFixedSection := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

/-- The same tuple shape, now in the ordered exterior-cube basis. -/
abbrev threeFixedSection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := oneFixedSection

@[simp] theorem threeFixedSection_apply (z : Fin 2 → ℤ) :
    threeFixedSection z = ![z 0, z 1, 0, 0] := rfl

theorem threeFixedSection_injective : Function.Injective threeFixedSection :=
  oneFixedSection_injective

theorem transpose_M₀_fixed_iff_mem_range (x : Fin 4 → ℤ) :
    M₀.transpose *ᵥ x = x ↔ x ∈ LinearMap.range oneFixedSection := by
  rw [transpose_M₀_fixed_iff_exists]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], h.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z 0, z 1, rfl⟩

theorem transpose_squareM₀_fixed_iff_mem_range (x : Fin 6 → ℤ) :
    squareM₀.transpose *ᵥ x = x ↔ x ∈ LinearMap.range twoFixedSection := by
  rw [transpose_squareM₀_fixed_iff_exists]
  constructor
  · rintro ⟨a, b, c, d, h⟩
    exact ⟨![a, b, c, d], h.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z 0, z 1, z 2, z 3, rfl⟩

theorem transpose_cubeM₀_fixed_iff_mem_range (x : Fin 4 → ℤ) :
    cubeM₀.transpose *ᵥ x = x ↔ x ∈ LinearMap.range threeFixedSection := by
  rw [transpose_cubeM₀_fixed_iff, ← transpose_M₀_fixed_iff]
  exact transpose_M₀_fixed_iff_mem_range x

@[simp] theorem transpose_M₀_fixedSection (z : Fin 2 → ℤ) :
    M₀.transpose *ᵥ oneFixedSection z = oneFixedSection z :=
  (transpose_M₀_fixed_iff_mem_range _).mpr ⟨z, rfl⟩

@[simp] theorem transpose_squareM₀_fixedSection (z : Fin 4 → ℤ) :
    squareM₀.transpose *ᵥ twoFixedSection z = twoFixedSection z :=
  (transpose_squareM₀_fixed_iff_mem_range _).mpr ⟨z, rfl⟩

@[simp] theorem transpose_cubeM₀_fixedSection (z : Fin 2 → ℤ) :
    cubeM₀.transpose *ᵥ threeFixedSection z = threeFixedSection z :=
  (transpose_cubeM₀_fixed_iff_mem_range _).mpr ⟨z, rfl⟩

/-! ## Literal submodules of fixed vectors -/

/-- The fixed submodule of a transpose matrix on the given integral coordinate module. -/
def transposeFixedSubmodule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Submodule ℤ (Fin n → ℤ) := LinearMap.ker (variation A.transpose)

@[simp] theorem mem_transposeFixedSubmodule {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    x ∈ transposeFixedSubmodule A ↔ A.transpose *ᵥ x = x :=
  variation_eq_zero_iff A.transpose x

/-- Every degree-one fixed vector has an integral section preimage. -/
theorem oneFixedSection_range :
    LinearMap.range oneFixedSection = transposeFixedSubmodule M₀ := by
  ext x
  rw [mem_transposeFixedSubmodule]
  exact (transpose_M₀_fixed_iff_mem_range x).symm

/-- Every degree-two fixed vector has an integral section preimage. -/
theorem twoFixedSection_range :
    LinearMap.range twoFixedSection = transposeFixedSubmodule squareM₀ := by
  ext x
  rw [mem_transposeFixedSubmodule]
  exact (transpose_squareM₀_fixed_iff_mem_range x).symm

/-- Every degree-three fixed vector has an integral section preimage. -/
theorem threeFixedSection_range :
    LinearMap.range threeFixedSection = transposeFixedSubmodule cubeM₀ := by
  ext x
  rw [mem_transposeFixedSubmodule]
  exact (transpose_cubeM₀_fixed_iff_mem_range x).symm

end Wikipedia.HopfProblem.CuspCentralCohomology

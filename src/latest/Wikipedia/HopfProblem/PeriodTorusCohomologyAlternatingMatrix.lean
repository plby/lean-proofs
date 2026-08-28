import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingPullback

/-!
# Exact pullback matrices and their common integral fixed line

The source coefficient order is `(γu,γw,γδ,uw,uδ,wδ)`.  Evaluation of
the actual coordinate form on the transformed lattice basis gives the
three displayed pullback formulas.  Their common fixed lattice is
exactly the integer multiples of `(0,0,6,1,0,0)`.

These statements concern pullback by the actual lattice matrices
`A₁,A₂,M₀`.  They do not replace this action by the distinct forward
dual-transport convention involving `T₁,T₂`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open PeriodTorusTypeOneOne

private theorem coefficientPullback_matrix_basis (A : LatticeMatrix)
    (E : Fin 6 → ℤ) (k : Fin 6) :
    coefficientPullback A.mulVecLin E k =
      coordinateValue E (fun i => A i (coefficientPair k).1)
        (fun i => A i (coefficientPair k).2) := by
  simp only [coefficientPullback_apply, coordinateForm_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one]
  rfl

/-- The first genuine lattice pullback, in the source's six coefficient positions. -/
theorem coefficientPullback_A₁ (E : Fin 6 → ℤ) :
    coefficientPullback A₁.mulVecLin E =
      ![-E 1 + E 2 - 6 * E 3 + 6 * E 4 - 8 * E 5,
        E 0 - E 1 + 2 * E 4 - 2 * E 5,
        E 2 + 6 * E 4 - 6 * E 5, E 3 - E 4 + E 5, -E 5, E 4 - E 5] := by
  funext k
  rw [coefficientPullback_matrix_basis]
  fin_cases k <;> simp [coefficientPair, coordinateValue, A₁] <;> ring

/-- The second genuine lattice pullback has the same source coefficient convention. -/
theorem coefficientPullback_A₂ (E : Fin 6 → ℤ) :
    coefficientPullback A₂.mulVecLin E =
      ![E 1 - 3 * E 5, -E 0 + E 2 - 6 * E 3 + 3 * E 4 - 6 * E 5,
        E 2 - 6 * E 5, E 3 + E 5, E 5, -E 4] := by
  funext k
  rw [coefficientPullback_matrix_basis]
  fin_cases k <;> simp [coefficientPair, coordinateValue, A₂] <;> ring

/-- The actual unipotent cusp lattice pullback. -/
theorem coefficientPullback_M₀ (E : Fin 6 → ℤ) :
    coefficientPullback M₀.mulVecLin E =
      ![E 0 + E 1 + E 4 + E 5, E 1 + E 5, E 2, E 3, E 4 + E 5, E 5] := by
  funext k
  rw [coefficientPullback_matrix_basis]
  fin_cases k <;> simp [coefficientPair, coordinateValue, M₀]

theorem coefficientPullback_A₁_eta :
    coefficientPullback A₁.mulVecLin ![0, 0, 6, 1, 0, 0] = ![0, 0, 6, 1, 0, 0] := by
  rw [coefficientPullback_A₁]
  decide

theorem coefficientPullback_A₂_eta :
    coefficientPullback A₂.mulVecLin ![0, 0, 6, 1, 0, 0] = ![0, 0, 6, 1, 0, 0] := by
  rw [coefficientPullback_A₂]
  decide

theorem coefficientPullback_M₀_eta :
    coefficientPullback M₀.mulVecLin ![0, 0, 6, 1, 0, 0] = ![0, 0, 6, 1, 0, 0] := by
  rw [coefficientPullback_M₀]
  decide

/-- Already the two elliptic lattice pullbacks determine the common fixed line. -/
theorem coefficientPullback_A₁_A₂_fixed_iff (E : Fin 6 → ℤ) :
    (coefficientPullback A₁.mulVecLin E = E ∧ coefficientPullback A₂.mulVecLin E = E) ↔
      E 0 = 0 ∧ E 1 = 0 ∧ E 4 = 0 ∧ E 5 = 0 ∧ E 2 = 6 * E 3 := by
  constructor
  · rintro ⟨hA₁, hA₂⟩
    rw [coefficientPullback_A₁] at hA₁
    rw [coefficientPullback_A₂] at hA₂
    have h₁₁ : E 0 - E 1 + 2 * E 4 - 2 * E 5 = E 1 := congrFun hA₁ 1
    have h₁₄ : -E 5 = E 4 := congrFun hA₁ 4
    have h₁₅ : E 4 - E 5 = E 5 := congrFun hA₁ 5
    have h₂₀ : E 1 - 3 * E 5 = E 0 := congrFun hA₂ 0
    have h₂₁ : -E 0 + E 2 - 6 * E 3 + 3 * E 4 - 6 * E 5 = E 1 := congrFun hA₂ 1
    have h5 : E 5 = 0 := by omega
    have h4 : E 4 = 0 := by omega
    have h0 : E 0 = 0 := by omega
    have h1 : E 1 = 0 := by omega
    exact ⟨h0, h1, h4, h5, by omega⟩
  · rintro ⟨h0, h1, h4, h5, h23⟩
    constructor
    · rw [coefficientPullback_A₁]
      funext k
      fin_cases k <;> simp [h0, h1, h4, h5, h23]
    · rw [coefficientPullback_A₂]
      funext k
      fin_cases k <;> simp [h0, h1, h4, h5, h23]

/-- The common integral fixed coefficients for all three actual lattice pullbacks. -/
theorem coefficientPullback_common_fixed_iff (E : Fin 6 → ℤ) :
    (coefficientPullback A₁.mulVecLin E = E ∧
      coefficientPullback A₂.mulVecLin E = E ∧ coefficientPullback M₀.mulVecLin E = E) ↔
        E 0 = 0 ∧ E 1 = 0 ∧ E 4 = 0 ∧ E 5 = 0 ∧ E 2 = 6 * E 3 := by
  constructor
  · rintro ⟨hA₁, hA₂, _⟩
    exact (coefficientPullback_A₁_A₂_fixed_iff E).mp ⟨hA₁, hA₂⟩
  · intro h
    obtain ⟨hA₁, hA₂⟩ := (coefficientPullback_A₁_A₂_fixed_iff E).mpr h
    refine ⟨hA₁, hA₂, ?_⟩
    obtain ⟨h0, h1, h4, h5, h23⟩ := h
    rw [coefficientPullback_M₀]
    funext k
    fin_cases k <;> simp [h0, h1, h4, h5, h23]

/-- Every common integral fixed vector is an integer multiple of the literal source generator. -/
theorem coefficientPullback_common_fixed_iff_multiple (E : Fin 6 → ℤ) :
    (coefficientPullback A₁.mulVecLin E = E ∧
      coefficientPullback A₂.mulVecLin E = E ∧ coefficientPullback M₀.mulVecLin E = E) ↔
        ∃ n : ℤ, E = n • (![0, 0, 6, 1, 0, 0] : Fin 6 → ℤ) := by
  rw [coefficientPullback_common_fixed_iff]
  constructor
  · rintro ⟨h0, h1, h4, h5, h23⟩
    refine ⟨E 3, ?_⟩
    funext k
    fin_cases k <;> simp [h0, h1, h4, h5, h23, mul_comm]
  · rintro ⟨n, rfl⟩
    simp [mul_comm]

/-- The multiple is unique because the fourth source coefficient of the generator is one. -/
theorem coefficientPullback_common_fixed_iff_unique_multiple (E : Fin 6 → ℤ) :
    (coefficientPullback A₁.mulVecLin E = E ∧
      coefficientPullback A₂.mulVecLin E = E ∧ coefficientPullback M₀.mulVecLin E = E) ↔
        ∃! n : ℤ, E = n • (![0, 0, 6, 1, 0, 0] : Fin 6 → ℤ) := by
  rw [coefficientPullback_common_fixed_iff_multiple]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, hn, ?_⟩
    intro m hm
    have h := congrFun (hm.symm.trans hn) 3
    simpa using h
  · rintro ⟨n, hn, _⟩
    exact ⟨n, hn⟩

end Wikipedia.HopfProblem.PeriodTorusCohomology

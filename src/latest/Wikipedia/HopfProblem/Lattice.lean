import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The integral matrices in `tex/s6.tex`, §2

The coordinates are `(γ, u, w, δ)` on `V` and the corresponding dual coordinates
on `Λ`. Matrices act on columns. All matrices below are explicit integral
matrices; no geometric existence statements are assumed.
-/

namespace Wikipedia.HopfProblem

open scoped Matrix

abbrev Lattice := Fin 4 → ℤ
abbrev LatticeMatrix := Matrix (Fin 4) (Fin 4) ℤ

/-- Definition 2.1: the order-three matrix on `V`. -/
def T₁ : LatticeMatrix :=
  !![1, 0, -6, 2; 0, -1, 1, 1; 0, -1, 0, 1; 0, 0, 0, 1]

/-- Definition 2.1: the order-four matrix on `V`. -/
def T₂ : LatticeMatrix :=
  !![1, 6, 0, -3; 0, 0, -1, 1; 0, 1, 0, 0; 0, 0, 0, 1]

/-- Lemma 2.2: the proposed cusp monodromy on `V`. -/
def T₀ : LatticeMatrix :=
  !![1, 0, 0, 1; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The nilpotent part of `T₀`. -/
def N : LatticeMatrix := T₀ - 1

/-- Lemma 2.4: contragredient of `T₁`. -/
def A₁ : LatticeMatrix :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

/-- Lemma 2.4: contragredient of `T₂`. -/
def A₂ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

/-- Lemma 2.4: contragredient of `T₀`. -/
def M₀ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1]

/-- The two invariant twist vectors of Definition 2.5. -/
def ε : Lattice := ![1, 2, -4, 0]

def ε' : Lattice := ![1, 3, -3, 0]

/-- The invariant functional on the dual lattice. -/
def γ (v : Lattice) : ℤ := v 0

/-- Lemma 2.6: the induced integral map at the cusp. -/
def B₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

theorem det_T₁ : T₁.det = 1 := by decide
theorem det_T₂ : T₂.det = 1 := by decide
theorem T₁_cube : T₁ ^ 3 = 1 := by decide
theorem T₁_ne_one : T₁ ≠ 1 := by decide
theorem T₂_fourth : T₂ ^ 4 = 1 := by decide
theorem T₂_sq_ne_one : T₂ ^ 2 ≠ 1 := by decide
theorem T₀_eq_one_add_N : T₀ = 1 + N := by decide
theorem N_sq : N ^ 2 = 0 := by decide
theorem T₁_mul_T₂_mul_T₀ : T₁ * T₂ * T₀ = 1 := by decide
theorem T₀_mul_T₁_mul_T₂ : T₀ * (T₁ * T₂) = 1 := by decide
theorem A₁_eq_transpose_sq : A₁ = (T₁ ^ 2).transpose := by decide
theorem A₂_eq_transpose_cube : A₂ = (T₂ ^ 3).transpose := by decide
theorem M₀_eq_one_sub_transpose : M₀ = 1 - N.transpose := by decide
theorem A₁_mul_A₂_mul_M₀ : A₁ * A₂ * M₀ = 1 := by decide
theorem A₁_fixes_ε : A₁ *ᵥ ε = ε := by decide
theorem A₂_fixes_ε' : A₂ *ᵥ ε' = ε' := by decide
theorem γ_ε : γ ε = 1 := rfl
theorem γ_ε' : γ ε' = 1 := rfl
theorem det_B₀ : B₀.det = 1 := by decide

/-- The coordinate formula for the nilpotent operator in Lemma 2.2. -/
theorem N_mulVec (v : Lattice) : N *ᵥ v = ![v 3, -v 2, 0, 0] := by
  ext i
  fin_cases i <;> simp [N, T₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem N_kernel (v : Lattice) : N *ᵥ v = 0 ↔ v 2 = 0 ∧ v 3 = 0 := by
  rw [N_mulVec]
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    change v 3 = 0 at h₀
    change -v 2 = 0 at h₁
    exact ⟨neg_eq_zero.mp h₁, h₀⟩
  · rintro ⟨h₂, h₃⟩
    simp [h₂, h₃]

/-- The image and kernel of `N` coincide, over the integers. -/
theorem N_range (v : Lattice) :
    (∃ w : Lattice, N *ᵥ w = v) ↔ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    simp [N_mulVec]
  · rintro ⟨h₂, h₃⟩
    refine ⟨![0, 0, -v 1, v 0], ?_⟩
    rw [N_mulVec]
    ext i
    fin_cases i <;> simp [h₂, h₃]

theorem M₀_sub_one_mulVec (v : Lattice) :
    (M₀ - 1) *ᵥ v = ![0, 0, v 1, -v 0] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem M₀_sub_one_kernel (v : Lattice) :
    (M₀ - 1) *ᵥ v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [M₀_sub_one_mulVec]
  constructor
  · intro h
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    change v 1 = 0 at h₂
    change -v 0 = 0 at h₃
    exact ⟨neg_eq_zero.mp h₃, h₂⟩
  · rintro ⟨h₀, h₁⟩
    simp [h₀, h₁]

theorem M₀_sub_one_range (v : Lattice) :
    (∃ w : Lattice, (M₀ - 1) *ᵥ w = v) ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    simp [M₀_sub_one_mulVec]
  · rintro ⟨h₀, h₁⟩
    refine ⟨![-v 3, v 2, 0, 0], ?_⟩
    rw [M₀_sub_one_mulVec]
    ext i
    fin_cases i <;> simp [h₀, h₁]

/-- The fixed sublattice of the first dual matrix (Lemma 2.6). -/
theorem A₁_fixed_iff (v : Lattice) :
    A₁ *ᵥ v = v ↔ v 1 = 2 * v 0 ∧ v 2 = -4 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂] <;>
      ring

/-- The fixed sublattice of the second dual matrix (Lemma 2.6). -/
theorem A₂_fixed_iff (v : Lattice) :
    A₂ *ᵥ v = v ↔ v 1 = 3 * v 0 ∧ v 2 = -3 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂]
    ring

/-- Lemma 2.7(ii): the common fixed lattice is the `δ̂`-axis. -/
theorem dual_common_fixed_iff (v : Lattice) :
    (A₁ *ᵥ v = v ∧ A₂ *ᵥ v = v) ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  rw [A₁_fixed_iff, A₂_fixed_iff]
  omega

theorem T₁_fixed_iff (v : Lattice) :
    T₁ *ᵥ v = v ↔ v 1 = 2 * v 2 ∧ v 3 = 3 * v 2 := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    simp [T₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂
    omega
  · rintro ⟨h₁, h₃⟩
    ext i
    fin_cases i <;> simp [T₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₃] <;>
      ring

theorem T₂_fixed_iff (v : Lattice) :
    T₂ *ᵥ v = v ↔ v 2 = v 1 ∧ v 3 = 2 * v 1 := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    simp [T₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂
    omega
  · rintro ⟨h₂, h₃⟩
    ext i
    fin_cases i <;> simp [T₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₂, h₃] <;>
      ring

/-- Lemma 2.7(i): the common fixed lattice on `V` is the `γ`-axis. -/
theorem common_fixed_iff (v : Lattice) :
    (T₁ *ᵥ v = v ∧ T₂ *ᵥ v = v) ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  rw [T₁_fixed_iff, T₂_fixed_iff]
  omega

end Wikipedia.HopfProblem

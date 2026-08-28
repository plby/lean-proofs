import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Injective linear families of symmetric trace-zero mixing matrices -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing

variable {N : Type*} [DecidableEq N] {r : ℕ}

def symmetricTraceZero (N : Type*) [Fintype N] : Submodule ℝ (Matrix N N ℝ) where
  carrier := {A | A.transpose = A ∧ A.trace = 0}
  zero_mem' := ⟨Matrix.transpose_zero, Matrix.trace_zero N ℝ⟩
  add_mem' := by
    intro A B hA hB
    constructor
    · rw [Matrix.transpose_add, hA.1, hB.1]
    · rw [Matrix.trace_add, hA.2, hB.2, add_zero]
  smul_mem' := by
    intro c A hA
    constructor
    · rw [Matrix.transpose_smul, hA.1]
    · rw [Matrix.trace_smul, hA.2, smul_zero]

abbrev DirectionSpace (N : Type*) [Fintype N] := ↥(symmetricTraceZero N)

def mixingLinear (b : N) (e : Fin r ↪ N) : (Fin r → ℝ) →ₗ[ℝ] Matrix N N ℝ :=
  ∑ j, ((Matrix.singleLinearMap ℝ b (e j) + Matrix.singleLinearMap ℝ (e j) b).comp
    (LinearMap.proj j : (Fin r → ℝ) →ₗ[ℝ] ℝ))

theorem mixingLinear_apply (b : N) (e : Fin r ↪ N) (c : Fin r → ℝ) :
    mixingLinear b e c = ∑ j, (Matrix.single b (e j) (c j) + Matrix.single (e j) b (c j)) := by
  simp [mixingLinear]

theorem mixingLinear_transpose (b : N) (e : Fin r ↪ N) (c : Fin r → ℝ) :
    (mixingLinear b e c).transpose = mixingLinear b e c := by
  simp only [mixingLinear_apply, Matrix.transpose_sum, Matrix.transpose_add,
    Matrix.transpose_single, add_comm]

theorem mixingLinear_trace [Fintype N]
    (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j) (c : Fin r → ℝ) :
    (mixingLinear b e c).trace = 0 := by
  simp only [mixingLinear_apply, Matrix.trace_sum, Matrix.trace_add]
  apply Finset.sum_eq_zero
  intro j _
  rw [Matrix.trace_single_eq_of_ne _ _ _ (he j),
    Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm (he j)), add_zero]

theorem mixingLinear_entry (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j)
    (c : Fin r → ℝ) (k : Fin r) : mixingLinear b e c b (e k) = c k := by
  have hne (j : Fin r) : e j ≠ b := (he j).symm
  simp [mixingLinear_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply,
    hne, e.injective.eq_iff]

theorem mixingLinear_injective (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j) :
    Function.Injective (mixingLinear b e) := by
  intro c d h
  funext k
  have hk := congrArg (fun A : Matrix N N ℝ ↦ A b (e k)) h
  simpa only [mixingLinear_entry b e he] using hk

theorem mixingLinear_support (b : N) (e : Fin r ↪ N) (c : Fin r → ℝ)
    (a d : N) (h : mixingLinear b e c a d ≠ 0) :
    ∃ j, (a = b ∧ d = e j) ∨ (a = e j ∧ d = b) := by
  by_contra hs
  apply h
  rw [mixingLinear_apply, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have h₁ : ¬(b = a ∧ e j = d) := by
    rintro ⟨hb, hj⟩
    exact hs ⟨j, Or.inl ⟨hb.symm, hj.symm⟩⟩
  have h₂ : ¬(e j = a ∧ b = d) := by
    rintro ⟨hj, hb⟩
    exact hs ⟨j, Or.inr ⟨hj.symm, hb.symm⟩⟩
  simp only [Matrix.add_apply, Matrix.single_apply, if_neg h₁, if_neg h₂, add_zero]

variable [Fintype N]

def mixingDirection (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j) :
    (Fin r → ℝ) →ₗ[ℝ] DirectionSpace N :=
  (mixingLinear b e).codRestrict (symmetricTraceZero N)
    (fun c ↦ ⟨mixingLinear_transpose b e c, mixingLinear_trace b e he c⟩)

theorem mixingDirection_injective (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j) :
    Function.Injective (mixingDirection b e he) := by
  intro c d h
  exact mixingLinear_injective b e he (congrArg Subtype.val h)

end Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing

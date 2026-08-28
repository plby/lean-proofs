import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic

/-! # The real linear subspace of operators anticommuting with a fixed operator -/

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {A : Type*} [Ring A] [Algebra ℝ A]

def anticommutingSubmodule (J : A) : Submodule ℝ A where
  carrier := {K | J * K = -(K * J)}
  zero_mem' := by simp
  add_mem' := by
    intro K L hK hL
    change J * (K + L) = -((K + L) * J)
    rw [mul_add, add_mul, hK, hL, neg_add]
  smul_mem' := by
    intro c K hK
    change J * (c • K) = -((c • K) * J)
    rw [mul_smul_comm, smul_mul_assoc, hK, smul_neg]

theorem mem_anticommutingSubmodule (J K : A) :
    K ∈ anticommutingSubmodule J ↔ J * K = -(K * J) := Iff.rfl

end Wikipedia.HomotopyGroupsOfSpheres

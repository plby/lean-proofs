/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Density definitions: copyright (c) 2025 The Formal Conjectures Authors.
Released under the Apache 2.0 license. This file has been modified.
-/
import Mathlib

open Filter

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos330

def twoFold (A : Set ℕ) : Set ℕ :=
  {n | ∃ x ∈ A, ∃ y ∈ A, x + y = n}

def IsAsymptoticBasisTwo (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ∈ twoFold A

def privateSet (A : Set ℕ) (a : ℕ) : Set ℕ :=
  twoFold A \ twoFold (A \ {a})

theorem erdos_330 :
    ∃ A : Set ℕ, IsAsymptoticBasisTwo A ∧ 0 < A.upperDensity ∧
      ∀ a ∈ A, 0 < (privateSet A a).upperDensity := by
  sorry

end Erdos330

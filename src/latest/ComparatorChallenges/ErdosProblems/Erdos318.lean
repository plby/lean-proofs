/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 318

This file uses the exact `P₁` predicate from the Formal Conjectures statement.
The theorem `not_contain_single_even_as_stated` records a boundary defect in
one auxiliary statement from that file: `A = {2}` has exactly one even member,
but has `P₁` vacuously because it admits no nonconstant signing.
-/

open Filter Set Real
open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

end Set

namespace Erdos253

def Set.IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, Set.IsAPOfLengthWith s l a d

end Erdos253

namespace Erdos318

/-- Local alias of the shared arithmetic-progression predicate used by nearby files. -/
abbrev Set.IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop := Erdos253.Set.IsAPOfLength s l

/-- The exact property `P₁` used by the upstream statement. -/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

/-! ## The malformed auxiliary statement -/

/-- A singleton has `P₁` vacuously: every `{±1}`-valued signing is constant. -/

theorem erdos_318.parts.i : ∃ A : Set ℕ, A.HasPosDensity ∧ ¬ P₁ A := by
  sorry

theorem erdos_318.variants.infinite_AP {A : Set ℕ}
    (hA : Set.IsAPOfLength A ⊤) : P₁ A := by
  sorry

theorem erdos_318.variants.univ : P₁ Set.univ := by
  sorry

theorem erdos_318.variants.odd : P₁ {n : ℕ | Odd n} := by
  sorry

theorem erdos_318.variants.squares : ¬ P₁ ({n | IsSquare n}) := by
  sorry

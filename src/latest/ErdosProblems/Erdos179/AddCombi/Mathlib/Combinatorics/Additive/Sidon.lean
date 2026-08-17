/-
Copyright (c) 2026 David B. Hulak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David B. Hulak
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Insert

/-!
# Sidon sets

This file defines the multiplicative predicate `IsMulSidon` for sets in
commutative monoids, and the additive predicate `IsAddSidon` generated from it.
A set is multiplicatively Sidon if whenever `a * b = c * d` for elements `a`,
`b`, `c`, `d` of the set, then either `a = c` and `b = d`, or `a = d` and
`b = c`. Additively, products are replaced by sums. The two elements in each
pair are not required to be distinct.

## Main declarations

* `IsMulSidon`/`IsAddSidon`: Predicates for a set to be Sidon.

## Tags

Sidon set, additive combinatorics
-/

public section

variable {G : Type*}

/-- A set `A` is multiplicatively Sidon if whenever `a * b = c * d` for elements
`a`, `b`, `c`, `d` of `A`, then either `a = c` and `b = d`, or `a = d` and
`b = c`. The two elements in each pair are not required to be distinct. -/
@[to_additive
/-- A set `A` is additively Sidon if whenever `a + b = c + d` for elements
`a`, `b`, `c`, `d` of `A`, then either `a = c` and `b = d`, or `a = d` and
`b = c`. The two elements in each pair are not required to be distinct. -/]
def IsMulSidon [CommMonoid G] (A : Set G) : Prop :=
  ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃c : G⦄, c ∈ A → ∀ ⦃d : G⦄,
    d ∈ A → a * b = c * d → a = c ∧ b = d ∨ a = d ∧ b = c

section CommMonoid

variable [CommMonoid G] {A B : Set G}

/-- A subset of a Sidon set is Sidon. -/
@[to_additive (attr := gcongr) /-- A subset of an additively Sidon set is additively Sidon. -/]
theorem IsMulSidon.mono (hAB : A ⊆ B) (hB : IsMulSidon B) : IsMulSidon A := by
  intro a ha b hb c hc d hd hprod
  exact hB (hAB ha) (hAB hb) (hAB hc) (hAB hd) hprod

/-- The empty set is Sidon. -/
@[to_additive (attr := simp) /-- The empty set is additively Sidon. -/]
protected theorem IsMulSidon.empty : IsMulSidon (∅ : Set G) := by
  simp [IsMulSidon]

/-- A subsingleton set is Sidon. -/
@[to_additive /-- A subsingleton set is additively Sidon. -/]
protected theorem IsMulSidon.of_subsingleton (hA : A.Subsingleton) : IsMulSidon A := by
  intro a ha b hb c hc d hd _
  exact .inl ⟨hA ha hc, hA hb hd⟩

/-- A singleton is Sidon. -/
@[to_additive (attr := simp) /-- A singleton is additively Sidon. -/]
protected theorem IsMulSidon.singleton (a : G) : IsMulSidon ({a} : Set G) := by
  simp [IsMulSidon]

/-- A directed union of Sidon sets is Sidon. -/
@[to_additive /-- A directed union of additively Sidon sets is additively Sidon. -/]
protected theorem IsMulSidon.iUnion {ι : Sort*} {A : ι → Set G} (hA : Directed (· ⊆ ·) A)
    (h : ∀ i, IsMulSidon (A i)) : IsMulSidon (⋃ i, A i) := by
  simp only [IsMulSidon, Set.mem_iUnion]
  rintro a ⟨i, hai⟩ b ⟨j, hbj⟩ c ⟨k, hck⟩ d ⟨l, hdl⟩ hprod
  obtain ⟨ij, hiij, hjij⟩ := hA i j
  obtain ⟨ijk, hijijk, hkijk⟩ := hA ij k
  obtain ⟨ijkl, hijkijkl, hlijkl⟩ := hA ijk l
  exact h ijkl (hijkijkl (hijijk (hiij hai))) (hijkijkl (hijijk (hjij hbj)))
    (hijkijkl (hkijk hck)) (hlijkl hdl) hprod

/-- A directed union of Sidon sets is Sidon. -/
@[to_additive /-- A directed union of additively Sidon sets is additively Sidon. -/]
protected theorem IsMulSidon.sUnion {S : Set (Set G)} (hS : DirectedOn (· ⊆ ·) S)
    (h : ∀ A ∈ S, IsMulSidon A) : IsMulSidon (⋃₀ S) := by
  rw [Set.sUnion_eq_iUnion]
  exact .iUnion hS.directed_val fun A ↦ h A.1 A.2

end CommMonoid

section CommGroup

variable [CommGroup G] [IsMulTorsionFree G]

/-- A pair in a torsion-free group is Sidon. -/
@[to_additive /-- A pair in a torsion-free group is additively Sidon. -/]
protected theorem IsMulSidon.pair (a b : G) : IsMulSidon ({a, b} : Set G) := by
  intro x hx y hy z hz w hw hprod
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz hw
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  all_goals
    simp_all only [and_self, or_self, true_or, or_true, mul_left_cancel_iff,
      mul_right_cancel_iff]
  all_goals exact (pow_left_inj (show (2 : ℕ) ≠ 0 by decide)).1 (by simpa [sq] using hprod)

end CommGroup

/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 363.
https://www.erdosproblems.com/forum/thread/363

Informal authors:
- Maciej Ulas

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/363#post-4709
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem363.lean
-/
/-
Solving Erdős Problem #363 (https://www.erdosproblems.com/363) in the negative, Ulas proved that there are infinitely many collections of disjoint intervals $I_1, \ldots, I_n$ of fixed size $\ge 4$ such that the product of all elements in the intervals is a square.

Ulas, Maciej, On products of disjoint blocks of consecutive integers. Enseign. Math. (2) (2005), 331-334.

Below you can find a formalization of this result, obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

-/

import Mathlib

set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos363

/-
Definitions of the starting points of the four intervals.
-/
def x₁ (n : ℕ) : ℕ := 4*n - 1
def x₂ (n : ℕ) : ℕ := 4*n + 3
def x₃ (n : ℕ) : ℕ := 4*n^2 + 7*n - 1
def x₄ (n : ℕ) : ℕ := 8*n^2 + 14*n + 1

/-
Definitions of the four intervals and the root term.
-/
open Finset

def I₁ (n : ℕ) : Finset ℕ := Icc (x₁ n + 1) (x₁ n + 4)
def I₂ (n : ℕ) : Finset ℕ := Icc (x₂ n + 1) (x₂ n + 4)
def I₃ (n : ℕ) : Finset ℕ := Icc (x₃ n + 1) (x₃ n + 4)
def I₄ (n : ℕ) : Finset ℕ := Icc (x₄ n + 1) (x₄ n + 4)

def root_term (n : ℕ) : ℕ :=
  16 * n * (n + 1) * (2 * n + 1) * (2 * n + 3) * (4 * n + 1) * (4 * n + 3) * (4 * n + 5) * (4 * n + 7) * (4 * n^2 + 7 * n + 1) * (4 * n^2 + 7 * n + 2)

/-
Evaluation of the product over the first interval for n > 0.
-/
theorem prod_I₁ (n : ℕ) (h : n > 0) : ∏ m ∈ I₁ n, m = (4*n) * (4*n+1) * (4*n+2) * (4*n+3) := by
  -- By definition of $I₁$, we have $I₁ n = \{4n, 4n+1, 4n+2, 4n+3\}$.
  have h_I1_def : I₁ n = {4 * n, 4 * n + 1, 4 * n + 2, 4 * n + 3} := by
    ext m
    simp [I₁, x₁];
    omega;
  simp +decide [ h_I1_def, mul_assoc ]

/-
Evaluation of the product over the second interval.
-/
theorem prod_I₂ (n : ℕ) : ∏ m ∈ I₂ n, m = (4*n+4) * (4*n+5) * (4*n+6) * (4*n+7) := by
  erw [ Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top ] <;> norm_num [ Finset.prod_Ico_succ_top ] ; ring_nf!;
  unfold x₂; ring;

/-
Evaluation of the product over the third interval for n > 0.
-/
theorem prod_I₃ (n : ℕ) (h : n > 0) : ∏ m ∈ I₃ n, m = (4*n^2+7*n) * (4*n^2+7*n+1) * (4*n^2+7*n+2) * (4*n^2+7*n+3) := by
  erw [ Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top ] <;> norm_num [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), x₃ ] ; ring_nf;
  zify ; ring_nf;
  grind

/-
Evaluation of the product over the fourth interval.
-/
theorem prod_I₄ (n : ℕ) : ∏ m ∈ I₄ n, m = (8*n^2+14*n+2) * (8*n^2+14*n+3) * (8*n^2+14*n+4) * (8*n^2+14*n+5) := by
  erw [ Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top, Finset.prod_Ico_succ_top ] <;> norm_num [ Finset.prod_Ico_succ_top ] ; ring_nf;
  unfold x₄; ring;

/-
The product of the elements in the four intervals is the square of the root term for n > 1.
-/
theorem product_is_square (n : ℕ) (h : n > 1) :
  (∏ m ∈ I₁ n, m) * (∏ m ∈ I₂ n, m) * (∏ m ∈ I₃ n, m) * (∏ m ∈ I₄ n, m) = (root_term n)^2 := by
  rw [ prod_I₁, prod_I₂, prod_I₃, prod_I₄ ] <;> try linarith;
  unfold root_term; ring;

/-
The four intervals are pairwise disjoint for n > 1.
-/
theorem intervals_disjoint (n : ℕ) (h : n > 1) :
  Disjoint (I₁ n) (I₂ n) ∧ Disjoint (I₁ n) (I₃ n) ∧ Disjoint (I₁ n) (I₄ n) ∧
  Disjoint (I₂ n) (I₃ n) ∧ Disjoint (I₂ n) (I₄ n) ∧
  Disjoint (I₃ n) (I₄ n) := by
  norm_num [ Finset.disjoint_left, I₁, I₂, I₃, I₄ ];
  unfold x₁ x₂ x₃ x₄; simp +arith +decide;
  refine' ⟨ _, _, _, _, _ ⟩;
  · intros; omega;
  · grind;
  · grind;
  · intro a _ ha_le ha_lt
    exfalso
    have hgap : 4 * n + 7 < 7 * n + 4 * n ^ 2 - 1 := by
      have hpos : 1 ≤ 7 * n + 4 * n ^ 2 := by nlinarith
      nlinarith [Nat.sub_add_cancel hpos]
    omega
  · constructor <;> intros <;> nlinarith [ Nat.sub_add_cancel ( by nlinarith : 1 ≤ 7 * n + 4 * n ^ 2 ) ]

/-
Definition of the collection of intervals and the validity property.
-/
def collection (n : ℕ) : List (Finset ℕ) := [I₁ n, I₂ n, I₃ n, I₄ n]

/-
The map n -> collection (n+2) is injective.
-/
theorem collection_injective : Function.Injective (fun n => collection (n + 2)) := by
  intro n m hnm;
  unfold collection at hnm; simp_all +arith +decide [ I₁, I₂, I₃, I₄ ] ;
  simp_all +arith +decide [ Finset.ext_iff, x₁, x₂, x₃, x₄ ];
  have := hnm.1 ( 4 * n + 8 ) ; have := hnm.1 ( 4 * m + 8 ) ; norm_num at * ; linarith;

/-
A finset is an interval if it is of the form Icc a b.
-/
def is_interval (s : Finset ℕ) : Prop := ∃ a b, s = Icc a b

/-
A collection of intervals is valid if all elements are intervals, they all have the same size k >= 4, they are pairwise disjoint, and the product of all elements in all intervals is a square.
-/
def is_valid_collection (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, is_interval I) ∧
  (∃ k, 4 ≤ k ∧ ∀ I ∈ S, I.card = k) ∧
  (S.Pairwise Disjoint) ∧
  IsSquare ((S.map (fun I => ∏ m ∈ I, m)).prod)

/-
The constructed collection is a valid collection for n > 1.
-/
theorem collection_is_valid (n : ℕ) (h : n > 1) : is_valid_collection (collection n) := by
  constructor <;> norm_num [ collection, intervals_disjoint n h ];
  · exact ⟨ ⟨ _, _, rfl ⟩, ⟨ _, _, rfl ⟩, ⟨ _, _, rfl ⟩, ⟨ _, _, rfl ⟩ ⟩;
  · constructor;
    · unfold I₁ I₂ I₃ I₄; aesop;
    · exact ⟨ root_term n, by linarith [ product_is_square n h ] ⟩

/-
It is not true that there are only finitely many collections of disjoint intervals I_1,...,I_n of size |I_i| >= 4 such that the product of their elements is a square.
-/
theorem erdos_363 : ¬ Set.Finite { S | is_valid_collection S } := by
  -- Let's construct the map $f : \mathbb{N} \to \text{Finset } \mathbb{N}$ by $f(n) = \text{collection } (n + 2)$.
  set f : ℕ → List (Finset ℕ) := fun n => collection (n + 2);
  -- We'll use that $f$ is injective to show that the set of valid collections is infinite.
  have h_inj : Function.Injective f := by
    exact collection_injective;
  exact Set.infinite_of_injective_forall_mem h_inj fun n => collection_is_valid _ ( by linarith )

end Erdos363

#print axioms Erdos363.erdos_363
-- 'Erdos363.erdos_363' depends on axioms: [propext, Classical.choice, Quot.sound]

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Auxiliary results for Erdős Problem 477.

Informal source: Lemma 1.7 of the paper at
https://github.com/Pengbinghui/pipeline-math/blob/main/papers/tiling-complement.pdf
Formal author: Codex.

These are general tiling lemmas, not a solution of Problem 477. In particular,
this file does not assert the avoidance hypothesis for a polynomial value set.
-/

import Mathlib

namespace Erdos477

/-- Uniqueness refers to the pair of summand values, not polynomial inputs. -/
def IsTiling (A B : Set ℤ) : Prop :=
  ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n

/-- The translates of `B` with centers in `A` do not overlap. -/
def IsPacking (A B : Set ℤ) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, a + b = a' + b' → a = a'

/-- The integer `n` lies in one of the translates. -/
def Covers (A B : Set ℤ) (n : ℤ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, a + b = n

/-- The difference set of the set of values. -/
def DifferenceSet (B : Set ℤ) : Set ℤ :=
  {z | ∃ u ∈ B, ∃ v ∈ B, z = u - v}

lemma isTiling_iff (A B : Set ℤ) :
    IsTiling A B ↔ IsPacking A B ∧ ∀ n, Covers A B n := by
  constructor
  · intro h
    constructor
    · intro a ha a' ha' b hb b' hb' heq
      obtain ⟨p, _, hp⟩ := h (a + b)
      have h₁ := hp (a, b) ⟨ha, hb, rfl⟩
      have h₂ := hp (a', b') ⟨ha', hb', heq.symm⟩
      exact congrArg Prod.fst (h₁.trans h₂.symm)
    · intro n
      obtain ⟨⟨a, b⟩, ⟨ha, hb, heq⟩, _⟩ := h n
      exact ⟨a, ha, b, hb, heq⟩
  · rintro ⟨hp, hc⟩ n
    obtain ⟨a, ha, b, hb, heq⟩ := hc n
    refine ⟨(a, b), ⟨ha, hb, heq⟩, ?_⟩
    rintro ⟨a', b'⟩ ⟨ha', hb', heq'⟩
    have haa := hp a' ha' a ha b' hb' b hb (heq'.trans heq.symm)
    apply Prod.ext haa
    dsimp at haa heq' ⊢
    omega

lemma IsPacking.mono {A A' B : Set ℤ} (h : IsPacking A B) (hsub : A' ⊆ A) :
    IsPacking A' B := by
  intro a ha a' ha' b hb b' hb' heq
  exact h a (hsub ha) a' (hsub ha') b hb b' hb' heq

lemma Covers.mono {A A' B : Set ℤ} {n : ℤ} (h : Covers A B n) (hsub : A ⊆ A') :
    Covers A' B n := by
  obtain ⟨a, ha, b, hb, heq⟩ := h
  exact ⟨a, hsub ha, b, hb, heq⟩

/-- The finite avoidance condition in the greedy criterion. -/
def FiniteAvoidance (B : Set ℤ) : Prop :=
  ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
    ∃ b ∈ B, ∀ c ∈ C, c - b ∉ DifferenceSet B

lemma extend_finite_packing {B : Set ℤ} (hB : FiniteAvoidance B)
    (A : Finset ℤ) (hA : IsPacking (A : Set ℤ) B) (n : ℤ) :
    ∃ A' : Finset ℤ, A ⊆ A' ∧ IsPacking (A' : Set ℤ) B ∧ Covers (A' : Set ℤ) B n := by
  classical
  by_cases hc : Covers (A : Set ℤ) B n
  · exact ⟨A, Finset.Subset.refl A, hA, hc⟩
  let C := A.image (fun a => n - a)
  have hC : ∀ c ∈ C, c ∉ B := by
    intro c hcC hcB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcC
    exact hc ⟨a, ha, n - a, hcB, by omega⟩
  obtain ⟨b, hb, havoid⟩ := hB C hC
  have hnew : ∀ a ∈ A, n - b - a ∉ DifferenceSet B := by
    intro a ha
    have h := havoid (n - a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rwa [show n - b - a = n - a - b by ring]
  refine ⟨insert (n - b) A, Finset.subset_insert _ _, ?_, ?_⟩
  · intro a ha a' ha' u hu v hv heq
    simp only [Finset.mem_coe, Finset.mem_insert] at ha ha'
    rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
    · rfl
    · exact False.elim (hnew a' ha' ⟨v, hv, u, hu, by omega⟩)
    · exact False.elim (hnew a ha ⟨u, hu, v, hv, by omega⟩)
    · exact hA a ha a' ha' u hu v hv heq
  · exact ⟨n - b, Finset.mem_insert_self _ _, b, hb, by omega⟩

/-- A countable increasing sequence of finite packings covers every integer.
This is the general greedy criterion; its hypothesis still has to be established
for any particular proposed tile. -/
theorem exists_tiling_of_finiteAvoidance {B : Set ℤ} (hB : FiniteAvoidance B) :
    ∃ A : Set ℤ, IsTiling A B := by
  classical
  let State := {A : Finset ℤ // IsPacking (A : Set ℤ) B}
  have step : ∀ A : State, ∀ n : ℤ,
      ∃ A' : State, A.val ⊆ A'.val ∧ Covers (A'.val : Set ℤ) B n := by
    intro A n
    obtain ⟨A', hsub, hpack, hcover⟩ := extend_finite_packing hB A.val A.property n
    exact ⟨⟨A', hpack⟩, hsub, hcover⟩
  choose next hnext using step
  let initial : State := ⟨∅, by simp [IsPacking]⟩
  let s : ℕ → State := fun k =>
    Nat.rec initial (fun k A => next A (Equiv.intEquivNat.symm k)) k
  have hs (k : ℕ) : (s k).val ⊆ (s (k + 1)).val ∧
      Covers ((s (k + 1)).val : Set ℤ) B (Equiv.intEquivNat.symm k) :=
    hnext (s k) (Equiv.intEquivNat.symm k)
  have hmono : Monotone (fun k => (s k).val) :=
    monotone_nat_of_le_succ (fun k => (hs k).1)
  let A : Set ℤ := {a | ∃ k, a ∈ (s k).val}
  refine ⟨A, (isTiling_iff A B).mpr ⟨?_, ?_⟩⟩
  · rintro a ⟨i, hi⟩ a' ⟨j, hj⟩ b hb b' hb' heq
    exact (s (max i j)).property a (hmono (le_max_left i j) hi)
      a' (hmono (le_max_right i j) hj) b hb b' hb' heq
  · intro n
    obtain ⟨k, rfl⟩ := Equiv.intEquivNat.symm.surjective n
    exact (hs k).2.mono (fun a ha => ⟨k + 1, ha⟩)

#print axioms exists_tiling_of_finiteAvoidance
-- 'Erdos477.exists_tiling_of_finiteAvoidance' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportBankExtensionCount

/-!
# Uniform triangle weights and fixed-size extension classes

For a family whose members all have the same number of triangles, a uniform
product weight turns every rooted extension sum into a cardinality times one
power.  This is the algebraic bridge from the exact `(r,K)` counts to the
moment bounds.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- Constant weight on ambient triples. -/
def constantTripleWeight
    {V : Type*} [DecidableEq V] (p : ℝ≥0) : TripleOn V → ℝ≥0 :=
  fun _ ↦ p

@[simp]
lemma setWeight_constantTripleWeight
    {V : Type*} [DecidableEq V] (p : ℝ≥0)
    (S : TripleSystemOn V) :
    setWeight (constantTripleWeight p) S = p ^ S.card := by
  simp [setWeight, constantTripleWeight]

/-- Members of `F` containing a prescribed root. -/
def familyExtensions
    {W : Type*} [DecidableEq W]
    (F : Finset (Finset W)) (R : Finset W) : Finset (Finset W) :=
  F.filter fun S ↦ R ⊆ S

@[simp]
lemma mem_familyExtensions_iff
    {W : Type*} [DecidableEq W]
    {F : Finset (Finset W)} {R S : Finset W} :
    S ∈ familyExtensions F R ↔ S ∈ F ∧ R ⊆ S := by
  simp [familyExtensions]

/-- Exact uniform-weight formula for a fixed-size finite family. -/
theorem extensionWeight_constant_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (m : ℕ)
    (hcard : ∀ S ∈ F, S.card = m)
    (p : ℝ≥0) (R : Finset W) :
    extensionWeight (fun S : F ↦ S.1) (fun _ ↦ p) R =
      ((familyExtensions F R).card : ℝ≥0) * p ^ (m - R.card) := by
  classical
  unfold extensionWeight
  calc
    (∑ S : F, if R ⊆ S.1 then
        setWeight (fun _ : W ↦ p) (S.1 \ R) else 0) =
        ∑ S ∈ F, if R ⊆ S then
          setWeight (fun _ : W ↦ p) (S \ R) else 0 := by
      exact (Finset.sum_subtype F (by simp)
        (fun S ↦ if R ⊆ S then
          setWeight (fun _ : W ↦ p) (S \ R) else 0)).symm
    _ = ∑ S ∈ F, (if R ⊆ S then
          p ^ (m - R.card) else 0) := by
      apply sum_congr rfl
      intro S hSF
      by_cases hRS : R ⊆ S
      · rw [if_pos hRS, if_pos hRS]
        unfold setWeight
        rw [prod_const, card_sdiff_of_subset hRS, hcard S hSF]
      · simp [hRS]
    _ = ∑ S ∈ familyExtensions F R, p ^ (m - R.card) := by
      rw [familyExtensions, sum_filter]
    _ = ((familyExtensions F R).card : ℝ≥0) *
        p ^ (m - R.card) := by simp

/-- Cardinal domination immediately yields a uniform-weight extension
bound for one prescribed root. -/
theorem extensionWeight_constant_le_of_card
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (m : ℕ)
    (hcard : ∀ S ∈ F, S.card = m)
    (p : ℝ≥0) (R : Finset W) (C : ℕ)
    (hC : (familyExtensions F R).card ≤ C) :
    extensionWeight (fun S : F ↦ S.1) (fun _ ↦ p) R ≤
      C * p ^ (m - R.card) := by
  rw [extensionWeight_constant_eq F m hcard p R]
  exact mul_le_mul_left (by exact_mod_cast hC) _

/-- Every exact bank class has the fixed outside size `j-2`. -/
lemma exactBankOutsideExtensions_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} :
    ∀ S ∈ exactBankOutsideExtensions r j B R K, S.card = j - 2 := by
  intro S hS
  exact (mem_exactBankOutsideExtensions_iff.mp hS).1

/-- Every distinguished-triangle exact class has the same fixed outside
size. -/
lemma exactBankOutsideExtensionsThrough_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V} :
    ∀ S ∈ exactBankOutsideExtensionsThrough r j B R K T,
      S.card = j - 2 := by
  intro S hS
  exact exactBankOutsideExtensions_fixed_card S
    (mem_exactBankOutsideExtensionsThrough_iff.mp hS).1

/-- Uniform-weight formula for an exact bank class. -/
theorem extensionWeight_exactBankOutsideExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K : TripleSystemOn V)
    (p : ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
      (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
      (constantTripleWeight p) A =
      ((familyExtensions (exactBankOutsideExtensions r j B R K) A).card :
        ℝ≥0) * p ^ (j - 2 - A.card) := by
  exact extensionWeight_constant_eq _ (j - 2)
    exactBankOutsideExtensions_fixed_card p A

end Erdos207

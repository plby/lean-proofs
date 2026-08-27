/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteLawKernelCalculus
import Mathlib.Logic.Function.Basic

/-! # Restricting independent bits along an injective coordinate map -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem independentBits_restrict
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J ↪ I) (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    map (fun x j ↦ x (e j)) (independentBits p hp) =
      independentBits (fun j ↦ p (e j)) (fun j ↦ hp (e j)) := by
  classical
  apply FiniteLaw.ext
  intro y
  rw [← probability_eq_mass, probability_map]
  let assignment : I → Bool := Function.extend e y (fun _ ↦ false)
  have hext (j : J) : assignment (e j) = y j := e.injective.extend_apply y _ j
  have hevent : (fun x : I → Bool ↦ (fun j ↦ x (e j)) = y) =
      (fun x ↦ ∀ i ∈ univ.map e, x i = assignment i) := by
    funext x
    apply propext
    constructor
    · intro h i hi
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      rw [hext, congrFun h j]
    · intro h
      funext j
      exact (h (e j) (mem_map.mpr ⟨j, mem_univ j, rfl⟩)).trans (hext j)
  rw [hevent, independentBits_probability_agrees, prod_map]
  change (∏ j, bernoulliBitMass (p (e j)) (assignment (e j))) =
    ∏ j, bernoulliBitMass (p (e j)) (y j)
  apply prod_congr rfl
  intro j _
  rw [hext]

def extendBitProbability
    {J I : Type*} (e : J ↪ I) (p : J → ℝ≥0) : I → ℝ≥0 :=
  Function.extend e p (fun _ ↦ 0)

theorem extendBitProbability_apply
    {J I : Type*} (e : J ↪ I) (p : J → ℝ≥0) (j : J) :
    extendBitProbability e p (e j) = p j := e.injective.extend_apply p _ j

theorem extendBitProbability_le
    {J I : Type*} (e : J ↪ I) (p : J → ℝ≥0) (q : I → ℝ≥0)
    (hpq : ∀ j, p j ≤ q (e j)) (i : I) : extendBitProbability e p i ≤ q i := by
  classical
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [extendBitProbability_apply]
    exact hpq j
  · rw [extendBitProbability, Function.extend_apply' _ _ _ hi]
    exact zero_le

theorem independentBits_restrict_extension
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J ↪ I) (p : J → ℝ≥0)
    (hp : ∀ j, p j ≤ 1) (he : ∀ i, extendBitProbability e p i ≤ 1) :
    map (fun x j ↦ x (e j)) (independentBits (extendBitProbability e p) he) =
      independentBits p hp := by
  rw [independentBits_restrict]
  apply FiniteLaw.ext
  intro y
  simp only [independentBits_mass, extendBitProbability_apply]

end

end Erdos207.FiniteLaw

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Exact product laws and coordinatewise finite pushforwards -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def productCoordinates
    {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] (K : I → FiniteLaw Ω) : FiniteLaw (I → Ω) where
  mass x := ∏ i, (K i).mass (x i)
  sum_mass := by
    classical
    rw [← Fintype.prod_sum]
    simp only [sum_mass, prod_const_one]

theorem map_productCoordinates
    {I Ω Ξ : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (K : I → FiniteLaw Ω) (f : I → Ω → Ξ) :
    map (fun x i ↦ f i (x i)) (productCoordinates K) =
      productCoordinates (fun i ↦ map (f i) (K i)) := by
  classical
  apply FiniteLaw.ext
  intro z
  change (∑ x : I → Ω, if (fun i ↦ f i (x i)) = z then ∏ i, (K i).mass (x i) else 0) =
    ∏ i, ∑ a : Ω, if f i a = z i then (K i).mass a else 0
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _hx
  rw [Fintype.prod_ite_zero]
  have heq : ((fun i ↦ f i (x i)) = z) ↔ ∀ i, f i (x i) = z i := funext_iff
  simp only [heq]

theorem productCoordinates_supported
    {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (K : I → FiniteLaw Ω) (P : I → Ω → Prop) (hK : ∀ i, (K i).SupportedOn (P i)) :
    (productCoordinates K).SupportedOn (fun x ↦ ∀ i, P i (x i)) := by
  classical
  intro x hx i
  apply hK i (x i)
  have hnonzero : (∏ a, (K a).mass (x a)) ≠ 0 := ne_of_gt hx
  have hi : (K i).mass (x i) ≠ 0 := (prod_ne_zero_iff.mp hnonzero) i (mem_univ i)
  exact pos_iff_ne_zero.mpr hi

end

end Erdos207.FiniteLaw

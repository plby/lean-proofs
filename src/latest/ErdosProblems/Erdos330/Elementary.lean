/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib
import Util.Density

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Elementary inequalities for Erdős Problem 330

These lemmas are independent of the main additive construction.  They support
the finite reciprocal-budget replacement for the informal infinite product
argument.
-/

namespace Erdos330

open scoped BigOperators

theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - s.sum x ≤ s.prod fun i => 1 - x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hs0 : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hxa0 : 0 ≤ x a := h0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have hprod_le_one : s.prod (fun i => 1 - x i) ≤ 1 := by
        exact Finset.prod_le_one
          (fun i hi => sub_nonneg.mpr (hs1 i hi))
          (fun i hi => sub_le_self 1 (hs0 i hi))
      have hmul_le : s.prod (fun i => 1 - x i) * x a ≤ x a := by
        simpa using mul_le_mul_of_nonneg_right hprod_le_one hxa0
      calc
        1 - (x a + s.sum x)
            = (1 - s.sum x) - x a := by ring
        _ ≤ s.prod (fun i => 1 - x i) - x a := sub_le_sub_right (ih hs0 hs1) (x a)
        _ ≤ s.prod (fun i => 1 - x i) - s.prod (fun i => 1 - x i) * x a :=
          sub_le_sub_left hmul_le (s.prod fun i => 1 - x i)
        _ = (1 - x a) * s.prod (fun i => 1 - x i) := by ring

end Erdos330

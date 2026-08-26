import ErdosProblems.Erdos67.StationarySubgroupDivergence

/-!
# Stabilizers of finite real functions

The squared translation cost vanishes exactly on the stabilizer subgroup.
Finiteness gives a strictly positive cost outside a proper stabilizer.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

variable {G : Type*} [Group G]

def translationStabilizer (w : G → ℝ) : Subgroup G where
  carrier := {u | ∀ a, w (u * a) = w a}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv a
    rw [mul_assoc, hu, hv]
  inv_mem' := by
    intro u hu a
    have he := hu (u⁻¹ * a)
    simpa only [mul_inv_cancel_left] using he.symm

variable [Fintype G]

noncomputable def translationCost (w : G → ℝ) (u : G) : ℝ :=
  ∑ a, (w a - w (u⁻¹ * a)) ^ 2

theorem translationCost_nonneg (w : G → ℝ) (u : G) : 0 ≤ translationCost w u :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

theorem translationCost_eq_zero_iff (w : G → ℝ) (u : G) :
    translationCost w u = 0 ↔ u ∈ translationStabilizer w := by
  constructor
  · intro hz a
    have he := (sum_eq_zero_iff_of_nonneg (fun a _ ↦ sq_nonneg (w a - w (u⁻¹ * a)))).mp hz
    have ha := he (u * a) (mem_univ _)
    simpa only [inv_mul_cancel_left, sq_eq_zero_iff, sub_eq_zero] using ha
  · intro hu
    apply sum_eq_zero
    intro a _
    have he := hu (u⁻¹ * a)
    simp only [mul_inv_cancel_left] at he
    rw [he, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

theorem translationCost_pos_of_not_mem (w : G → ℝ) (u : G) (hu : u ∉ translationStabilizer w) :
    0 < translationCost w u :=
  lt_of_le_of_ne (translationCost_nonneg w u) (Ne.symm (mt (translationCost_eq_zero_iff w u).mp hu))

theorem exists_uniform_translationCost_gap (w : G → ℝ) (u : G)
    (hu : u ∉ translationStabilizer w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : G, v ∉ translationStabilizer w → ε ≤ translationCost w v := by
  classical
  let S := univ.filter (fun v ↦ v ∉ translationStabilizer w)
  have hS : S.Nonempty := ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩⟩
  obtain ⟨v, hv, hmin⟩ := exists_min_image S (translationCost w) hS
  refine ⟨translationCost w v, translationCost_pos_of_not_mem w v (mem_filter.mp hv).2, ?_⟩
  intro a ha
  exact hmin a (mem_filter.mpr ⟨mem_univ _, ha⟩)

omit [Fintype G] in
theorem constant_of_translationStabilizer_eq_top (w : G → ℝ)
    (h : translationStabilizer w = ⊤) (a b : G) : w a = w b := by
  have hu : a * b⁻¹ ∈ translationStabilizer w := by rw [h]; trivial
  have he := hu b
  simpa only [inv_mul_cancel_right] using he

end Erdos67.StationaryModel

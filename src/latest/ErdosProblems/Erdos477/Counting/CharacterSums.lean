/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Character-sum ingredients for counting diagonal sextic points over finite fields.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The square-root size of a nontrivial Gauss sum, derived from Mathlib's
product formula and complex conjugation identity. -/
theorem norm_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, ← pow_two, norm_natCast] at hn
  calc
    _ = Real.sqrt (‖gaussSum χ ψ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hn

/-- The characters that are trivial on a specified subgroup of the unit
group. They are used to detect power residues. -/
noncomputable def annihilator (H : Subgroup Fˣ) : Subgroup (MulChar F ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual

lemma mem_annihilator (H : Subgroup Fˣ) (χ : MulChar F ℂ) :
    χ ∈ annihilator H ↔ ∀ x ∈ H, χ x = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

/-- The annihilator separates every unit outside the original subgroup. -/
lemma exists_annihilator_ne_one (H : Subgroup Fˣ) (x : Fˣ) (hx : x ∉ H) :
    ∃ χ : annihilator H, (χ.val : MulChar F ℂ) x ≠ 1 := by
  by_contra h
  push Not at h
  have hmem : x ∈ (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ).symm
      (OrderDual.toDual (annihilator H)) := by
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff]
    intro χ hχ
    exact h ⟨χ, hχ⟩
  have hx' : x ∈ H := by
    simpa only [annihilator, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hmem
  exact hx hx'

/-- Orthogonality on a subgroup of multiplicative characters. -/
theorem sum_annihilator (H : Subgroup Fˣ) [Fintype (annihilator H)]
    [DecidablePred (· ∈ H)] (x : Fˣ) :
    (∑ χ : annihilator H, (χ.val : MulChar F ℂ) x) =
      if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 := by
  classical
  by_cases hx : x ∈ H
  · rw [if_pos hx]
    have hχ (χ : annihilator H) : (χ.val : MulChar F ℂ) x = 1 :=
      (mem_annihilator H χ.val).mp χ.property x hx
    simp only [hχ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg hx]
    obtain ⟨χ, hχ⟩ := exists_annihilator_ne_one H x hx
    have hmul : (χ.val : MulChar F ℂ) x *
        (∑ η : annihilator H, (η.val : MulChar F ℂ) x) =
        ∑ η : annihilator H, (η.val : MulChar F ℂ) x := by
      simp only [Finset.mul_sum, ← MulChar.mul_apply]
      exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ (fun _ => rfl)
    have hzero : ((χ.val : MulChar F ℂ) x - 1) *
        (∑ η : annihilator H, (η.val : MulChar F ℂ) x) = 0 := by
      linear_combination hmul
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hχ)

#print axioms norm_gaussSum
-- 'Erdos477.Counting.norm_gaussSum' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms sum_annihilator
-- 'Erdos477.Counting.sum_annihilator' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting

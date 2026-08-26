/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Multiplicative characters detecting power residues in a finite field.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CharacterSums

namespace Erdos477.Counting

open scoped BigOperators

variable (F : Type*) [Field F] [Fintype F]

/-- The subgroup of nonzero `d`th powers. -/
def powerResidueSubgroup (d : ℕ) : Subgroup Fˣ := (powMonoidHom d : Fˣ →* Fˣ).range

/-- Characters trivial on `d`th powers. -/
noncomputable def powerCharacters (d : ℕ) : Subgroup (MulChar F ℂ) :=
  annihilator (powerResidueSubgroup F d)

noncomputable instance powerCharactersFintype (d : ℕ) : Fintype (powerCharacters F d) :=
  Fintype.ofFinite _

lemma card_powerCharacters_eq_card_ker (d : ℕ) :
    Nat.card (powerCharacters F d) = Nat.card (powMonoidHom d : Fˣ →* Fˣ).ker := by
  rw [powerCharacters, annihilator, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  change (powerResidueSubgroup F d).index = _
  exact Subgroup.index_range

/-- There are at most `d` characters needed to detect `d`th powers. -/
theorem card_powerCharacters_le (d : ℕ) [NeZero d] :
    Fintype.card (powerCharacters F d) ≤ d := by
  rw [← Nat.card_eq_fintype_card, card_powerCharacters_eq_card_ker]
  have hker : (powMonoidHom d : Fˣ →* Fˣ).ker = rootsOfUnity d F := by
    ext x
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, mem_rootsOfUnity]
  rw [hker]
  exact card_rootsOfUnity F d

variable {F}

/-- The number of roots in the unit group is constant on power residues. -/
lemma card_powerFiber [DecidableEq F] (d : ℕ) (x : Fˣ)
    [Decidable (x ∈ powerResidueSubgroup F d)] :
    (Finset.univ.filter (fun u : Fˣ => u ^ d = x)).card =
      if x ∈ powerResidueSubgroup F d then Fintype.card (powerCharacters F d) else 0 := by
  classical
  have hk : (Finset.univ.filter (fun u : Fˣ => u ^ d = 1)).card =
      Nat.card (powMonoidHom d : Fˣ →* Fˣ).ker := by
    let e : (powMonoidHom d : Fˣ →* Fˣ).ker ≃ {u : Fˣ // u ^ d = 1} :=
      Equiv.subtypeEquivRight (fun u => by simp)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    simp only [Fintype.card_subtype]
  by_cases hx : x ∈ powerResidueSubgroup F d
  · rw [if_pos hx, ← Nat.card_eq_fintype_card, card_powerCharacters_eq_card_ker, ← hk]
    exact MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom d : Fˣ →* Fˣ)
      hx ⟨1, one_pow d⟩
  · rw [if_neg hx, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).2
    exact hx ⟨u, hu'⟩

/-- Orthogonality expresses the number of `d`th roots as a character sum. -/
theorem sum_powerCharacters_eq_card_powerFiber [DecidableEq F] (d : ℕ) (x : Fˣ) :
    (∑ χ : powerCharacters F d, (χ.val : MulChar F ℂ) x) =
      ((Finset.univ.filter (fun u : Fˣ => u ^ d = x)).card : ℂ) := by
  classical
  let : Fintype (annihilator (powerResidueSubgroup F d)) := powerCharactersFintype F d
  rw [card_powerFiber]
  change (∑ χ : annihilator (powerResidueSubgroup F d), (χ.val : MulChar F ℂ) x) = _
  rw [sum_annihilator]
  split_ifs
  · rfl
  · simp only [Nat.cast_zero]

#print axioms card_powerCharacters_le
-- 'Erdos477.Counting.card_powerCharacters_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms sum_powerCharacters_eq_card_powerFiber
-- 'Erdos477.Counting.sum_powerCharacters_eq_card_powerFiber' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting

import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Enumerating a finite full cycle with its exact cyclic successor. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv Finset

variable {D : Type*} [Fintype D] (ρ : Perm D) (hρ : ρ.IsCycleOn Set.univ)
    (a : D) (n : ℕ) (hcard : Fintype.card D = n)

def cycleEnumeration : Fin n ≃ D :=
  Equiv.ofBijective (fun i => (ρ ^ i.val) a) (by
    have hcyc : ρ.IsCycleOn (univ : Finset D) := by simpa only [coe_univ] using hρ
    constructor
    · intro i j he
      apply Fin.ext
      have hm := (hcyc.pow_apply_eq_pow_apply (mem_univ a)).mp he
      simp only [card_univ, hcard] at hm
      exact hm.eq_of_lt_of_lt i.isLt j.isLt
    · intro b
      obtain ⟨m, hm, he⟩ := hcyc.exists_pow_eq (mem_univ a) (mem_univ b)
      refine ⟨⟨m, ?_⟩, he⟩
      simpa only [card_univ, hcard] using hm)

theorem cycleEnumeration_apply (i : Fin n) :
    cycleEnumeration ρ hρ a n hcard i = (ρ ^ i.val) a := rfl

theorem cycleEnumeration_succ (i j : Fin n) (hij : i.val + 1 = j.val) :
    cycleEnumeration ρ hρ a n hcard j = ρ (cycleEnumeration ρ hρ a n hcard i) := by
  simp only [cycleEnumeration_apply, ← hij, pow_succ', Perm.mul_apply]

theorem cycleEnumeration_rotate (i : Fin n) :
    cycleEnumeration ρ hρ a n hcard (finRotate n i) =
      ρ (cycleEnumeration ρ hρ a n hcard i) := by
  have hcyc : ρ.IsCycleOn (univ : Finset D) := by simpa only [coe_univ] using hρ
  rw [cycleEnumeration_apply, cycleEnumeration_apply, ← Perm.mul_apply, ← pow_succ']
  apply (hcyc.pow_apply_eq_pow_apply (mem_univ a)).mpr
  simp only [card_univ, hcard]
  change (finRotate n i).val % n = (i.val + 1) % n
  rw [finRotate_apply]
  simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod, Nat.mod_mod]

end
end Erdos73

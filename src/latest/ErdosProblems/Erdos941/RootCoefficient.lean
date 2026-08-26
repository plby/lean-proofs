import ErdosProblems.Erdos941.RootCount
import ErdosProblems.Erdos941.ModularRoots
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # The multiplicative function counting squarefree root data -/

namespace Erdos941

noncomputable def rootResiduesEquivModularRoots {n a : ℕ}
    (ha : 0 < a) (hsq : Squarefree a) (hcop : a.Coprime (2 * n)) :
    {b // b ∈ squarefreeRootResidues n a} ≃ ModularRoots n a := by
  letI : NeZero a := ⟨ha.ne'⟩
  refine
    { toFun := fun b => ⟨(b.val : ZMod a), ?_⟩
      invFun := fun x => ⟨x.val.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hd := (mem_squarefreeRootResidues.mp b.property).2.2.2
    have hz := (ZMod.natCast_eq_zero_iff (b.val ^ 2 + n) a).mpr hd
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  · apply mem_squarefreeRootResidues.mpr
    refine ⟨ZMod.val_lt x.val, hsq, hcop, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ a).mp
    push_cast
    rw [ZMod.natCast_zmod_val, x.property, neg_add_cancel]
  · intro b
    apply Subtype.ext
    exact (ZMod.val_natCast a b.val).trans
      (Nat.mod_eq_of_lt (mem_squarefreeRootResidues.mp b.property).1)
  · intro x
    apply Subtype.ext
    exact ZMod.natCast_zmod_val x.val

theorem squarefreeRootResidues_card_eq {n a : ℕ}
    (ha : 0 < a) (hsq : Squarefree a) (hcop : a.Coprime (2 * n)) :
    (squarefreeRootResidues n a).card = Nat.card (ModularRoots n a) := by
  classical
  rw [← Nat.card_congr (rootResiduesEquivModularRoots ha hsq hcop),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem squarefreeRootResidues_card_formula (n a : ℕ) :
    (squarefreeRootResidues n a).card =
      if Squarefree a ∧ a.Coprime (2 * n) then Nat.card (ModularRoots n a) else 0 := by
  classical
  split_ifs with h
  · exact squarefreeRootResidues_card_eq (Nat.pos_of_ne_zero h.1.ne_zero) h.1 h.2
  · have he : squarefreeRootResidues n a = ∅ := by
      ext b
      simp only [mem_squarefreeRootResidues, Finset.notMem_empty, iff_false]
      rintro ⟨_, hsq, hcop, _⟩
      exact h ⟨hsq, hcop⟩
    rw [he, Finset.card_empty]

noncomputable def squarefreeRootCoefficient (n : ℕ) : ArithmeticFunction ℕ where
  toFun a := (squarefreeRootResidues n a).card
  map_zero' := by simp [squarefreeRootResidues]

@[simp] theorem squarefreeRootCoefficient_apply (n a : ℕ) :
    squarefreeRootCoefficient n a = (squarefreeRootResidues n a).card := rfl

theorem squarefreeRootCoefficient_multiplicative (n : ℕ) :
    (squarefreeRootCoefficient n).IsMultiplicative := by
  classical
  constructor
  · change (squarefreeRootResidues n 1).card = 1
    simp [squarefreeRootResidues]
  · intro a b hab
    simp only [squarefreeRootCoefficient_apply, squarefreeRootResidues_card_formula,
      Nat.squarefree_mul hab, Nat.coprime_mul_iff_left]
    by_cases ha : Squarefree a ∧ a.Coprime (2 * n)
    · by_cases hb : Squarefree b ∧ b.Coprime (2 * n)
      · rw [if_pos ⟨⟨ha.1, hb.1⟩, ha.2, hb.2⟩, if_pos ha, if_pos hb]
        exact modularRoots_card_mul n hab
      · have hh : ¬((Squarefree a ∧ Squarefree b) ∧
            a.Coprime (2 * n) ∧ b.Coprime (2 * n)) := by tauto
        rw [if_neg hh, if_pos ha, if_neg hb, mul_zero]
    · have hh : ¬((Squarefree a ∧ Squarefree b) ∧
          a.Coprime (2 * n) ∧ b.Coprime (2 * n)) := by tauto
      rw [if_neg hh, if_neg ha, zero_mul]

theorem squarefreeRootCoefficient_prime (n : ℕ) {p : ℕ} [Fact p.Prime]
    (hcop : p.Coprime (2 * n)) :
    (squarefreeRootCoefficient n p : ℤ) = legendreSym p (-(n : ℤ)) + 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    have hh := hcop.of_dvd_right (dvd_mul_right 2 n)
    norm_num at hh
  rw [squarefreeRootCoefficient_apply,
    squarefreeRootResidues_card_eq hp.pos hp.squarefree hcop]
  exact modularRoots_card_prime n hp2

end Erdos941

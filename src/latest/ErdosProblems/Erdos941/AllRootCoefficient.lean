import ErdosProblems.Erdos941.AllRootCount
import ErdosProblems.Erdos941.RootHensel
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # The multiplicative function counting root data at coprime moduli -/

namespace Erdos941

noncomputable def allRootResiduesEquivModularRoots {n a : ℕ}
    (ha : 0 < a) (hcop : a.Coprime (2 * n)) :
    {b // b ∈ allRootResidues n a} ≃ ModularRoots n a := by
  letI : NeZero a := ⟨ha.ne'⟩
  refine
    { toFun := fun b => ⟨(b.val : ZMod a), ?_⟩
      invFun := fun x => ⟨x.val.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hd := (mem_allRootResidues.mp b.property).2.2
    have hz := (ZMod.natCast_eq_zero_iff (b.val ^ 2 + n) a).mpr hd
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  · apply mem_allRootResidues.mpr
    refine ⟨ZMod.val_lt x.val, hcop, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ a).mp
    push_cast
    rw [ZMod.natCast_zmod_val, x.property, neg_add_cancel]
  · intro b
    apply Subtype.ext
    exact (ZMod.val_natCast a b.val).trans
      (Nat.mod_eq_of_lt (mem_allRootResidues.mp b.property).1)
  · intro x
    apply Subtype.ext
    exact ZMod.natCast_zmod_val x.val

theorem allRootResidues_card_eq {n a : ℕ}
    (ha : 0 < a) (hcop : a.Coprime (2 * n)) :
    (allRootResidues n a).card = Nat.card (ModularRoots n a) := by
  classical
  rw [← Nat.card_congr (allRootResiduesEquivModularRoots ha hcop),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem allRootResidues_card_formula (n a : ℕ) :
    (allRootResidues n a).card =
      if a.Coprime (2 * n) then Nat.card (ModularRoots n a) else 0 := by
  classical
  split_ifs with h
  · have ha : 0 < a := by
      by_contra hh
      have ha0 : a = 0 := by omega
      have hbad : 2 * n = 1 := by simpa [ha0] using h
      omega
    exact allRootResidues_card_eq ha h
  · have he : allRootResidues n a = ∅ := by
      ext b
      simp only [mem_allRootResidues, Finset.notMem_empty, iff_false]
      rintro ⟨_, hcop, _⟩
      exact h hcop
    rw [he, Finset.card_empty]

noncomputable def allRootCoefficient (n : ℕ) : ArithmeticFunction ℕ where
  toFun a := (allRootResidues n a).card
  map_zero' := by simp [allRootResidues]

@[simp] theorem allRootCoefficient_apply (n a : ℕ) :
    allRootCoefficient n a = (allRootResidues n a).card := rfl

theorem allRootCoefficient_multiplicative (n : ℕ) :
    (allRootCoefficient n).IsMultiplicative := by
  classical
  constructor
  · change (allRootResidues n 1).card = 1
    simp [allRootResidues]
  · intro a b hab
    simp only [allRootCoefficient_apply, allRootResidues_card_formula,
      Nat.coprime_mul_iff_left]
    by_cases ha : a.Coprime (2 * n)
    · by_cases hb : b.Coprime (2 * n)
      · rw [if_pos ⟨ha, hb⟩, if_pos ha, if_pos hb]
        exact modularRoots_card_mul n hab
      · rw [if_neg (by tauto : ¬(a.Coprime (2 * n) ∧ b.Coprime (2 * n))),
          if_pos ha, if_neg hb, mul_zero]
    · rw [if_neg (by tauto : ¬(a.Coprime (2 * n) ∧ b.Coprime (2 * n))),
        if_neg ha, zero_mul]

theorem allRootCoefficient_prime_pow (n : ℕ) {p : ℕ} [Fact p.Prime]
    (hcop : p.Coprime (2 * n)) (k : ℕ) :
    (allRootCoefficient n (p ^ (k + 1)) : ℤ) = legendreSym p (-(n : ℤ)) + 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    have hh := hcop.of_dvd_right (dvd_mul_right 2 n)
    norm_num at hh
  rw [allRootCoefficient_apply,
    allRootResidues_card_eq (pow_pos hp.pos _) (hcop.pow_left _),
    modularRoots_card_prime_pow n hcop k]
  exact modularRoots_card_prime n hp2

theorem allRootCoefficient_bad_prime_pow (n : ℕ) {p : ℕ}
    (hcop : ¬p.Coprime (2 * n)) (k : ℕ) :
    allRootCoefficient n (p ^ (k + 1)) = 0 := by
  rw [allRootCoefficient_apply, allRootResidues_card_formula, if_neg]
  exact fun h => hcop (h.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero k)))

end Erdos941

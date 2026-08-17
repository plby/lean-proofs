/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPrimeExtension

/-!
# Good permutations at prime-power moduli

This file packages the iteration of Jackson--Mauldin Lemma 4.8 which is
needed when the nontrivial part of a denominator is a prime power.  At the
successor step the already constructed good permutation on `Fin (p ^ a)` is
embedded as the partial map on the source class `0 mod p`; Lemma 4.8 then
extends it to a good permutation on all of `Fin (p ^ (a + 1))`.
-/

namespace Erdos215.Selector.PrimePowerGood

open Erdos215.Selector
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Regard the value of a permutation of `Fin d` as an element of
`Fin (p * d)`.  Only its values on indices `oldIndex p hp i` matter in the
partial-goodness argument, but defining it on every index makes it directly
usable as the partial map in Lemma 4.8. -/
private def embeddedOldPerm (p : ℕ) (hp : 0 < p) {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) : Fin (p * d) → Fin (p * d) :=
  fun x => Fin.castLE (Nat.le_mul_of_pos_left d hp) (sigma (quotientIndex p x))

private lemma embeddedOldPerm_oldIndex_modEq (p : ℕ) (hp : 0 < p) {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (i : Fin d) :
    (embeddedOldPerm p hp sigma (oldIndex p hp i)).1 ≡ (sigma i).1 [MOD d] := by
  simp only [embeddedOldPerm, quotientIndex_oldIndex, Fin.coe_castLE]
  exact Nat.ModEq.refl _

/-- Every prime-power modulus admits a permutation satisfying the exact
Jackson--Mauldin goodness condition (4.3). -/
theorem exists_goodPerm_primePower (p a : ℕ) (hp : p.Prime) :
    ∃ sigma : Equiv.Perm (Fin (p ^ a)), GoodPerm (p ^ a) sigma := by
  induction a with
  | zero =>
      refine ⟨Equiv.refl (Fin 1), ?_⟩
      intro i j hij
      exfalso
      apply hij
      apply Fin.ext
      have hi : i.1 < 1 := by simpa only [pow_zero] using i.2
      have hj : j.1 < 1 := by simpa only [pow_zero] using j.2
      omega
  | succ a ih =>
      rw [pow_succ, Nat.mul_comm (p ^ a) p]
      rcases ih with ⟨sigma, hsigma⟩
      let d := p ^ a
      let N := p * d
      let pi : Fin N → Fin N := embeddedOldPerm p hp.pos sigma
      have hsigmaMap : GoodMap d (fun i => sigma i) := by
        simpa only [GoodMap, GoodPerm] using hsigma
      have hpartial : PartialGoodOnClass N p 0 pi := by
        refine partialGoodOnOldClass_of_reduces_good p hp.pos
          (fun i => sigma i) hsigmaMap pi ?_
        intro i
        exact embeddedOldPerm_oldIndex_modEq p hp.pos sigma i
      let target : Fin p := ⟨0, hp.pos⟩
      have hcop : Nat.Coprime p 1 := Nat.coprime_one_right p
      have hpd : N = p * d := rfl
      have hn : 0 < a + 1 := Nat.succ_pos a
      have hN : N = 1 * p ^ (a + 1) := by
        simp only [N, d, one_mul, pow_succ]
        ac_rfl
      obtain ⟨tau, htau, _⟩ :=
        exists_goodPerm_to_target hp hn hcop hpd hN target pi hpartial
      change ∃ tau : Equiv.Perm (Fin N), GoodPerm N tau
      exact ⟨tau, htau⟩

end

end Erdos215.Selector.PrimePowerGood

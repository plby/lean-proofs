/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.KeyStructure
import ErdosProblems.Erdos565.KeyUnion
import Mathlib.Tactic

/-!
# Scaled finite-union lemmas for the ACDFM key lemma

The key lemma is most naturally proved by denominator-cleared estimates of
the form `|E| * 2^q ≤ |Ω|`.  This file supplies the three finite counting
operations used when assembling those estimates: unioning two exceptional
events, unioning an indexed family after reserving an exponent for the number
of indices, and unioning over the dependent structural tuples.
-/

namespace Erdos565
namespace KeyFiberCounting

/-- Unioning two events costs one binary exponent. -/
theorem card_union_mul_pow_le
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (A B : Finset Omega) (q : ℕ)
    (hA : A.card * 2 ^ (q + 1) ≤ Fintype.card Omega)
    (hB : B.card * 2 ^ (q + 1) ≤ Fintype.card Omega) :
    (A ∪ B).card * 2 ^ q ≤ Fintype.card Omega := by
  let M := Fintype.card Omega
  let d := 2 ^ (q + 1)
  have hd : 0 < d := by positivity
  have hAdiv : A.card ≤ M / d := (Nat.le_div_iff_mul_le hd).2 hA
  have hBdiv : B.card ≤ M / d := (Nat.le_div_iff_mul_le hd).2 hB
  have hunion : (A ∪ B).card ≤ 2 * (M / d) := by
    calc
      (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ M / d + M / d := Nat.add_le_add hAdiv hBdiv
      _ = 2 * (M / d) := by omega
  calc
    (A ∪ B).card * 2 ^ q ≤ (2 * (M / d)) * 2 ^ q :=
      Nat.mul_le_mul_right _ hunion
    _ = d * (M / d) := by
      dsimp [d]
      rw [pow_add]
      ring
    _ ≤ M := Nat.mul_div_le M d

/-- If an indexed family has at most `2^c` members and each member saves
`c+q` binary exponents, its union saves `q` exponents. -/
theorem card_biUnion_mul_pow_le
    {Omega I : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype I]
    (E : I → Finset Omega) (c q : ℕ)
    (hI : Fintype.card I ≤ 2 ^ c)
    (hE : ∀ i, (E i).card * 2 ^ (c + q) ≤ Fintype.card Omega) :
    (Finset.univ.biUnion E).card * 2 ^ q ≤ Fintype.card Omega := by
  classical
  let M := Fintype.card Omega
  let d := 2 ^ (c + q)
  have hd : 0 < d := by positivity
  have hEdiv : ∀ i, (E i).card ≤ M / d := fun i ↦
    (Nat.le_div_iff_mul_le hd).2 (hE i)
  have hunion : (Finset.univ.biUnion E).card ≤ 2 ^ c * (M / d) := by
    calc
      (Finset.univ.biUnion E).card ≤ ∑ i ∈ (Finset.univ : Finset I), (E i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset I), M / d :=
        Finset.sum_le_sum fun i _ ↦ hEdiv i
      _ = Fintype.card I * (M / d) := by simp
      _ ≤ 2 ^ c * (M / d) := Nat.mul_le_mul_right _ hI
  calc
    (Finset.univ.biUnion E).card * 2 ^ q ≤
        (2 ^ c * (M / d)) * 2 ^ q := Nat.mul_le_mul_right _ hunion
    _ = d * (M / d) := by
      dsimp [d]
      rw [pow_add]
      ring
    _ ≤ M := Nat.mul_div_le M d

/-- Dependent structural union bound stated directly with a scaled estimate
for every fixed tuple.  It is the denominator-cleared form consumed by the
ACDFM fixed-tuple proof, and avoids choosing an artificial uniform natural
bound `K` at the call site. -/
theorem dependent_key_union_bound_scaled
    {V Omega : Type*} [Fintype V] [DecidableEq V] [Fintype Omega]
    (r N D : ℕ) (Small : Finset V → Prop)
    (bad : KeyStructure.RestrictedStructure V r N Small → Omega → Prop)
    (hV : Fintype.card V = N)
    (hr : 1 ≤ r) (hND : N ≤ r * D)
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hSmall : ∀ U : Finset V, Small U →
      r * U.card.choose 2 ≤ 4 * r * D)
    (hfixed : ∀ sigma,
      (KeyUnion.badSet bad sigma).card * 2 ^ (8 * r * D) ≤
        Fintype.card Omega) :
    (KeyUnion.badUnion bad).card * 2 ^ D ≤ Fintype.card Omega := by
  let M := Fintype.card Omega
  let d := 2 ^ (8 * r * D)
  have hd : 0 < d := by positivity
  have hstructures :
      Fintype.card (KeyStructure.RestrictedStructure V r N Small) ≤
        2 ^ (3 * N + 4 * r * D) :=
    KeyStructure.card_restrictedStructure_le_two_pow V r N D Small hV hR hSmall
  have hbad : ∀ sigma, (KeyUnion.badSet bad sigma).card ≤ M / d := fun sigma ↦
    (Nat.le_div_iff_mul_le hd).2 (hfixed sigma)
  have hunion : (KeyUnion.badUnion bad).card ≤
      2 ^ (3 * N + 4 * r * D) * (M / d) :=
    (KeyUnion.card_badUnion_le bad (M / d) hbad).trans
      (Nat.mul_le_mul_right (M / d) hstructures)
  calc
    (KeyUnion.badUnion bad).card * 2 ^ D ≤
        (2 ^ (3 * N + 4 * r * D) * (M / d)) * 2 ^ D :=
      Nat.mul_le_mul_right (2 ^ D) hunion
    _ = (M / d) * 2 ^ (3 * N + 4 * r * D + D) := by
      rw [pow_add]
      ring
    _ ≤ (M / d) * d := by
      exact Nat.mul_le_mul_left (M / d)
        (Nat.pow_le_pow_right (by decide : 0 < 2)
          (KeyUnion.structural_exponent_add_target_le hr hND))
    _ ≤ M := Nat.div_mul_le_self M d

end KeyFiberCounting
end Erdos565

import ErdosProblems.Erdos941.NegativeQuadraticCharacter

/-! # Quadratic roots modulo coprime moduli and modulo primes -/

namespace Erdos941

def ModularRoots (n a : ℕ) := {x : ZMod a // x ^ 2 = -(n : ZMod a)}

def modularRootsReduce (n : ℕ) {a b : ℕ} (hab : a ∣ b) :
    ModularRoots n b → ModularRoots n a := fun x =>
  ⟨ZMod.castHom hab (ZMod a) x.val, by
    have h := congrArg (ZMod.castHom hab (ZMod a)) x.property
    simpa only [map_pow, map_neg, map_natCast] using h⟩

noncomputable def modularRootsCRT (n : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    ModularRoots n (a * b) ≃ ModularRoots n a × ModularRoots n b := by
  let e := ZMod.chineseRemainder hab
  refine
    { toFun := fun x => (⟨(e x.val).1, ?_⟩, ⟨(e x.val).2, ?_⟩)
      invFun := fun x => ⟨e.symm (x.1.val, x.2.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := congrArg (fun x => (e x).1) x.property
    simpa only [map_pow, map_neg, map_natCast, Prod.pow_fst, Prod.fst_neg, Prod.fst_natCast] using h
  · have h := congrArg (fun x => (e x).2) x.property
    simpa only [map_pow, map_neg, map_natCast, Prod.pow_snd, Prod.snd_neg, Prod.snd_natCast] using h
  · apply e.injective
    rw [map_pow, map_neg, map_natCast, e.apply_symm_apply]
    apply Prod.ext
    · exact x.1.property
    · exact x.2.property
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  · intro x
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (x.1.val, x.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd (e.apply_symm_apply (x.1.val, x.2.val))

theorem modularRoots_card_mul (n : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    Nat.card (ModularRoots n (a * b)) = Nat.card (ModularRoots n a) * Nat.card (ModularRoots n b) := by
  rw [Nat.card_congr (modularRootsCRT n hab), Nat.card_prod]

theorem modularRoots_card_prime (n : ℕ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (Nat.card (ModularRoots n p) : ℤ) = legendreSym p (-(n : ℤ)) + 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ringChar.eq (ZMod p) p]
  have h := quadraticChar_card_sqrts hchar (-(n : ZMod p))
  have hcard : ({x : ZMod p | x ^ 2 = -(n : ZMod p)}.toFinset).card =
      Nat.card (ModularRoots n p) := by
    rw [Set.toFinset_card]
    exact Nat.card_eq_fintype_card.symm
  rw [hcard] at h
  simpa only [legendreSym, Int.cast_neg, Int.cast_natCast] using h

end Erdos941

import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Surjectivity of simultaneous reduction at a finite prime set
-/

open Nat Finset

namespace Erdos394

/-- Simultaneous integer reduction into a finite product of `ZMod p`. -/
def zmodPiLinear (P : Finset ℕ) :
    ℤ →ₗ[ℤ] (∀ p : {p // p ∈ P}, ZMod p.val) where
  toFun := fun z p ↦ (z : ZMod p.val)
  map_add' x y := by ext p; simp
  map_smul' n x := by ext p; simp [smul_eq_mul]

@[simp] theorem zmodPiLinear_apply (P : Finset ℕ) (z : ℤ)
    (p : {p // p ∈ P}) : zmodPiLinear P z p = (z : ZMod p.val) := rfl

/-- CRT: simultaneous reduction at distinct primes is surjective. -/
theorem zmodPiLinear_surjective (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) : Function.Surjective (zmodPiLinear P) := by
  classical
  intro y
  let I := {p // p ∈ P}
  let a : I → ℕ := fun p ↦ (y p).val
  let s : I → ℕ := fun p ↦ p.1
  have hs : ∀ p ∈ (Finset.univ : Finset I), s p ≠ 0 := by
    intro p hp
    exact (hprime p.1 p.2).ne_zero
  have hpair : Set.Pairwise (↑(Finset.univ : Finset I))
      (Function.onFun Nat.Coprime s) := by
    intro p hp q hq hpq
    apply (Nat.coprime_primes (hprime p.1 p.2) (hprime q.1 q.2)).mpr
    intro heq
    apply hpq
    exact Subtype.ext heq
  let k := Nat.chineseRemainderOfFinset a s Finset.univ hs hpair
  refine ⟨(k : ℤ), ?_⟩
  funext p
  letI : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  change ((k : ℤ) : ZMod p.val) = y p
  rw [show ((k : ℤ) : ZMod p.val) = ((k : ℕ) : ZMod p.val) by norm_num,
    ← ZMod.natCast_zmod_val (y p)]
  exact (ZMod.natCast_eq_natCast_iff k (y p).val p.1).mpr (k.prop p (Finset.mem_univ p))

end Erdos394

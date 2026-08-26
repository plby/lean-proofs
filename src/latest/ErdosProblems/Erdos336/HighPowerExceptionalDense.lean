import Mathlib
import ErdosProblems.Erdos336.HighPowerKneserReduction
import ErdosProblems.Erdos336.DenseProgressionCore
import ErdosProblems.Erdos336.HighPowerSmallSupport

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# High powers eliminate Lev's bounded-coset exceptional alternative
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Uniformly bounded fibres of a map to `ZMod m` bound the source cardinality
by `m` times the fibre bound. -/
theorem card_le_modulus_mul_of_fiber_bound
    {m V : ℕ} (hm : 0 < m) (π : G →+ ZMod m)
    (hfiber : ∀ z : ZMod m, (homFiberFinset π z).card ≤ V) :
    Fintype.card G ≤ m * V := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let U : Finset G := Finset.univ.biUnion (homFiberFinset π)
  have hU : U = Finset.univ := by
    ext x
    simp [U, homFiberFinset]
  calc
    Fintype.card G = U.card := by rw [hU, Finset.card_univ]
    _ ≤ (Finset.univ : Finset (ZMod m)).card * V := by
      exact Finset.card_biUnion_le_card_mul Finset.univ (homFiberFinset π) V
        (fun z _ => hfiber z)
    _ = m * V := by simp

/-- A primitive `t`-th power with `t≥3` cannot realize Lev's three-coset
exception without being globally dense.  Indeed its image support of size at
most three forces the whole quotient to have size at most three; Lev's
exceptional inequality and strict `9/4` doubling then give `|G|<2|tC|`. -/
theorem highPower_three_coset_exception_is_dense
    {m V t : ℕ} (hm : 0 < m) (ht : 3 ≤ t)
    (π : G →+ ZMod m) (hπ : Function.Surjective π)
    {C : Set G} (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hfiber : ∀ z : ZMod m, (homFiberFinset π z).card ≤ V)
    (himage : (π '' ExactPower C t).ncard ≤ 3)
    (hexception : (ExactPower C t).ncard + 3 * V ≤
      (ExactPower C (2 * t)).ncard)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard) :
    Fintype.card G < 2 * (ExactPower C t).ncard := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hzero' : 0 ∈ π '' C := ⟨0, hzero, π.map_zero⟩
  have hprimitive' := exactPower_univ_image_of_surjective π hπ hprimitive
  have hsmall : (ExactPower (π '' C) t).ncard ≤ 3 := by
    rw [← image_exactPower]
    exact himage
  have hm3 : m ≤ 3 := by
    simpa using card_le_of_highPower_ncard_le hzero' hprimitive' ht hsmall
  have hcard : Fintype.card G ≤ m * V :=
    card_le_modulus_mul_of_fiber_bound hm π hfiber
  have hMV : m * V ≤ 3 * V := Nat.mul_le_mul_right V hm3
  omega

end Erdos336

import Mathlib
import ErdosProblems.Erdos336.KneserTheorem
import ErdosProblems.Erdos336.HighPowerSmallQuotient
import ErdosProblems.Erdos336.DyadicSmallDoubling

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Kneser reduction for a primitive high power

This file extracts the canonical aperiodic quotient of a small-doubling set.
It also records that exact powers commute with additive homomorphic images, so
primitive high-power growth survives in every finite quotient.
-/

namespace Erdos336

open scoped Pointwise

variable {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]

/-- Exact list powers commute with additive homomorphic images. -/
theorem image_exactPower (f : G →+ Q) (C : Set G) (t : ℕ) :
    f '' ExactPower C t = ExactPower (f '' C) t := by
  rw [exactPower_eq_nsmul, exactPower_eq_nsmul]
  induction t with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      exact Set.image_singleton.trans (congrArg singleton f.map_zero)
  | succ t ih =>
      rw [succ_nsmul, succ_nsmul, Set.image_add, ih]

/-- Primitivity passes through a surjective additive homomorphism. -/
theorem exactPower_univ_image_of_surjective
    [Fintype G] [Fintype Q]
    (f : G →+ Q) (hf : Function.Surjective f)
    {C : Set G} (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ) :
    ∃ q : ℕ, ExactPower (f '' C) q = Set.univ := by
  obtain ⟨q, hq⟩ := hprimitive
  refine ⟨q, ?_⟩
  rw [← image_exactPower, hq, Set.image_univ]
  exact hf.range_eq

/-- In every finite quotient, a primitive zero-containing power is either
already full or has at least `t+1` points. -/
theorem image_highPower_full_or_large
    [Fintype G] [Fintype Q]
    (f : G →+ Q) (hf : Function.Surjective f)
    {C : Set G} (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (t : ℕ) :
    ExactPower (f '' C) t = Set.univ ∨
      t + 1 ≤ (ExactPower (f '' C) t).ncard := by
  have hzero' : 0 ∈ f '' C := ⟨0, hzero, f.map_zero⟩
  have hprimitive' := exactPower_univ_image_of_surjective f hf hprimitive
  by_cases hfull : ExactPower (f '' C) t = Set.univ
  · exact Or.inl hfull
  · exact Or.inr
      (add_one_le_ncard_exactPower_of_not_full hzero' hprimitive' t hfull)

section Finite

variable [Fintype G] [DecidableEq G]

/-- Kneser's inequality makes the stabilizer-saturation of a strict `9/4`
small-doubling set more than `8/9` dense, up to the one stabilizer fibre. -/
theorem stabilizer_saturation_density_of_nine_four
    (S : Finset G) (hdoub : 4 * (S + S).card < 9 * S.card) :
    8 * (S + (S + S).addStab).card <
      9 * S.card + 4 * (S + S).addStab.card := by
  have hk := Finset.add_kneser S S
  omega

/-- If the stabilizer-saturation in the Kneser reduction is the whole group,
then the small-doubling set is already globally dense. -/
theorem card_lt_three_mul_of_stabilizer_saturation_eq_univ
    (S : Finset G) (hdoub : 4 * (S + S).card < 9 * S.card)
    (hfull : S + (S + S).addStab = Finset.univ) :
    Fintype.card G < 3 * S.card := by
  have hk := Finset.add_kneser S S
  have hstab : (S + S).addStab.card ≤ Fintype.card G :=
    Finset.card_le_univ _
  rw [hfull, Finset.card_univ] at hk
  omega

/-- Quotienting by the stabilizer of `S+S` makes the doubled image aperiodic. -/
theorem addStab_image_add_self_quotient_stabilizer
    (S : Finset G) (hS : S.Nonempty) :
    let H := AddAction.stabilizer G (↑(S + S) : Set G)
    let D : Finset (G ⧸ H) := S.image (↑)
    (D + D).addStab = 0 := by
  let H := AddAction.stabilizer G (↑(S + S) : Set G)
  let q : G →+ G ⧸ H := QuotientAddGroup.mk' H
  let D : Finset (G ⧸ H) := S.image q
  change (D + D).addStab = 0
  have hsum : (S + S).Nonempty := hS.add hS
  have h := Finset.addStab_image_coe_quotient hsum
  have him : Finset.image q (S + S) = D + D := by
    simpa [D] using (Finset.image_add q (s := S) (t := S))
  rw [← him]
  simpa [q, H] using h

/-- Canonical Kneser dichotomy at the strict `9/4` threshold: either `S` is
already globally dense, or its stabilizer-saturation is proper, is quantitatively
dense, and the doubled image in the stabilizer quotient is aperiodic. -/
theorem nine_four_dense_or_aperiodic_quotient
    (S : Finset G) (hS : S.Nonempty)
    (hdoub : 4 * (S + S).card < 9 * S.card) :
    Fintype.card G < 3 * S.card ∨
      (S + (S + S).addStab ≠ Finset.univ ∧
        8 * (S + (S + S).addStab).card <
          9 * S.card + 4 * (S + S).addStab.card ∧
        (let H := AddAction.stabilizer G (↑(S + S) : Set G)
         let D : Finset (G ⧸ H) := S.image (↑)
         (D + D).addStab = 0)) := by
  by_cases hfull : S + (S + S).addStab = Finset.univ
  · exact Or.inl
      (card_lt_three_mul_of_stabilizer_saturation_eq_univ S hdoub hfull)
  · exact Or.inr ⟨hfull,
      stabilizer_saturation_density_of_nine_four S hdoub,
      addStab_image_add_self_quotient_stabilizer S hS⟩

end Finite

end Erdos336

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BezoutAdditiveCharacter
import ErdosProblems.Erdos387.CongruenceCounting
import ErdosProblems.Erdos387.ProgressionFourier

/-!
# Fourier expansion of a simultaneous CRT class

This is the exact finite interface used when the fixed covering progression
and a divisor-certificate progression are counted together.  It identifies
the existing natural-number CRT class with a `ZMod` residue fibre, expands
its cardinality by additive orthogonality, and then applies the canonical
Bézout factorization to the residue phase.
-/

namespace Erdos387

open scoped BigOperators

namespace SimultaneousFourier

/-- The elementary simultaneous class is exactly the corresponding `ZMod`
residue fibre on the natural interval. -/
theorem simultaneousClassIoc_eq_residueClass
    {L U M d a b : ℕ} [NeZero M] [NeZero d]
    (hcop : Nat.Coprime M d)
    (hM : 0 < M) (hd : 0 < d) :
    simultaneousClassIoc L U M d a b hcop =
      ProgressionFourier.residueClass (M * d) (Finset.Ioc L U)
        (simultaneousResidue hcop a b : ZMod (M * d)) := by
  classical
  have hr := simultaneousResidue_lt hcop hM hd a b
  ext n
  simp only [simultaneousClassIoc, modularPreimageIoc,
    ProgressionFourier.residueClass, Finset.mem_filter,
    Finset.mem_singleton]
  rw [ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt hr]

/-- Exact additive-character expansion of a combined progression count. -/
theorem card_simultaneousClassIoc_eq_phase_sum
    {L U M d a b : ℕ} [NeZero M] [NeZero d]
    (hcop : Nat.Coprime M d)
    (hM : 0 < M) (hd : 0 < d) :
    (((simultaneousClassIoc L U M d a b hcop).card : ℕ) : ℂ) =
      ((M * d : ℕ) : ℂ)⁻¹ *
        ∑ h : ZMod (M * d),
          ZMod.stdAddChar
              (-h * (simultaneousResidue hcop a b : ZMod (M * d))) *
            ProgressionFourier.coefficient (M * d) (Finset.Ioc L U) h := by
  rw [simultaneousClassIoc_eq_residueClass hcop hM hd]
  exact ProgressionFourier.card_residueClass_eq_phase_sum
    (M * d) (Finset.Ioc L U)
      (simultaneousResidue hcop a b : ZMod (M * d))

/-- The ring-theoretic CRT sends the canonical natural simultaneous residue
to its two prescribed coordinates. -/
theorem chineseRemainder_simultaneousResidue
    {M d : ℕ} (hcop : Nat.Coprime M d) (a b : ℕ) :
    ZMod.chineseRemainder hcop
        (simultaneousResidue hcop a b : ZMod (M * d)) =
      ((a : ZMod M), (b : ZMod d)) := by
  have ha : (simultaneousResidue hcop a b : ZMod M) = (a : ZMod M) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (simultaneousResidue_mod_left hcop a b)
  have hb : (simultaneousResidue hcop a b : ZMod d) = (b : ZMod d) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (simultaneousResidue_mod_right hcop a b)
  apply Prod.ext
  · simpa [ZMod.chineseRemainder, ZMod.castHom_apply] using ha
  · simpa [ZMod.chineseRemainder, ZMod.castHom_apply] using hb

/-- The combined residue phase splits into a divisor-modulus phase and a
fixed-progression phase.  Both inverses are the canonical Bézout
coefficients, so the identity contains no choice of representatives. -/
theorem stdAddChar_neg_mul_simultaneousResidue
    {M d : ℕ} [NeZero M] [NeZero d]
    (hcop : Nat.Coprime M d) (a b : ℕ) (h : ZMod (M * d)) :
    ZMod.stdAddChar
        (-h * (simultaneousResidue hcop a b : ZMod (M * d))) =
      ZMod.stdAddChar
          (-(ZMod.chineseRemainder hcop h).2 * (b : ZMod d) *
            (Nat.gcdA M d : ZMod d)) *
        ZMod.stdAddChar
          (-(ZMod.chineseRemainder hcop h).1 * (a : ZMod M) *
            (Nat.gcdB M d : ZMod M)) := by
  rw [BezoutAdditiveCharacter.stdAddChar_product_crt M d hcop]
  simp only [map_mul, map_neg,
    chineseRemainder_simultaneousResidue hcop a b]
  congr 2

/-- Reciprocity form used in the source: after subtracting the distinguished
residue `b`, all dependence on the varying modulus `d` appears through the
canonical inverse `gcdB M d` of `d` modulo `M`. -/
theorem stdAddChar_mul_simultaneousResidue_reciprocity
    {M d : ℕ} [NeZero M] [NeZero d]
    (hcop : Nat.Coprime M d) (a b : ℕ) (h : ZMod (M * d)) :
    ZMod.stdAddChar
        (h * (simultaneousResidue hcop a b : ZMod (M * d))) =
      ZMod.stdAddChar
          ((ZMod.chineseRemainder hcop h).1 *
            ((a : ZMod M) - (b : ZMod M)) *
            (Nat.gcdB M d : ZMod M)) *
        ZMod.stdAddChar (h * (b : ZMod (M * d))) := by
  let hM := (ZMod.chineseRemainder hcop h).1
  let hd := (ZMod.chineseRemainder hcop h).2
  let A : ZMod d := Nat.gcdA M d
  let B : ZMod M := Nat.gcdB M d
  have hleft :
      ZMod.stdAddChar
          (h * (simultaneousResidue hcop a b : ZMod (M * d))) =
        ZMod.stdAddChar (hd * (b : ZMod d) * A) *
          ZMod.stdAddChar (hM * (a : ZMod M) * B) := by
    rw [BezoutAdditiveCharacter.stdAddChar_product_crt M d hcop]
    simp only [map_mul,
      chineseRemainder_simultaneousResidue hcop a b]
    rfl
  have hbase :
      ZMod.stdAddChar (h * (b : ZMod (M * d))) =
        ZMod.stdAddChar (hd * (b : ZMod d) * A) *
          ZMod.stdAddChar (hM * (b : ZMod M) * B) := by
    rw [BezoutAdditiveCharacter.stdAddChar_product_crt M d hcop]
    simp [hM, hd, A, B, ZMod.chineseRemainder, ZMod.castHom_apply]
  have hcombine :
      ZMod.stdAddChar
          (hM * ((a : ZMod M) - (b : ZMod M)) * B) *
          ZMod.stdAddChar (hM * (b : ZMod M) * B) =
        ZMod.stdAddChar (hM * (a : ZMod M) * B) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hleft, hbase]
  change
    ZMod.stdAddChar (hd * (b : ZMod d) * A) *
        ZMod.stdAddChar (hM * (a : ZMod M) * B) =
      ZMod.stdAddChar
          (hM * ((a : ZMod M) - (b : ZMod M)) * B) *
        (ZMod.stdAddChar (hd * (b : ZMod d) * A) *
          ZMod.stdAddChar (hM * (b : ZMod M) * B))
  rw [mul_left_comm,
    show ZMod.stdAddChar
          (hM * ((a : ZMod M) - (b : ZMod M)) * B) *
          ZMod.stdAddChar (hM * (b : ZMod M) * B) =
        ZMod.stdAddChar (hM * (a : ZMod M) * B) from hcombine]

/-- Source-facing form of the exact combined progression formula, with the
two CRT phases already separated. -/
theorem card_simultaneousClassIoc_eq_split_phase_sum
    {L U M d a b : ℕ} [NeZero M] [NeZero d]
    (hcop : Nat.Coprime M d)
    (hM : 0 < M) (hd : 0 < d) :
    (((simultaneousClassIoc L U M d a b hcop).card : ℕ) : ℂ) =
      ((M * d : ℕ) : ℂ)⁻¹ *
        ∑ h : ZMod (M * d),
          (ZMod.stdAddChar
              (-(ZMod.chineseRemainder hcop h).2 * (b : ZMod d) *
                (Nat.gcdA M d : ZMod d)) *
            ZMod.stdAddChar
              (-(ZMod.chineseRemainder hcop h).1 * (a : ZMod M) *
                (Nat.gcdB M d : ZMod M))) *
            ProgressionFourier.coefficient (M * d) (Finset.Ioc L U) h := by
  rw [card_simultaneousClassIoc_eq_phase_sum hcop hM hd]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [stdAddChar_neg_mul_simultaneousResidue hcop a b h]

end SimultaneousFourier

end Erdos387

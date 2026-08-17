/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPureExtension
import ErdosProblems.Erdos215.SelectorPrimeClassGood
import ErdosProblems.Erdos215.SelectorOldLine
import ErdosProblems.Erdos215.SelectorPrimePowerGood

/-!
# Goodness of the pure nontrivial-prime extension

This file verifies condition (4.3) for every line map in
`PurePrimeExtension.extendedFamily`.  Old line labels use (4.9) and the
partial-good extension lemma.  For a new line label, the distinguished
values are treated in the two cases determined by whether the full new
`p`-power divides the input difference: the new primary coordinate handles
the first case, and the complementary coordinate reduces the second case to
one old-line extension.
-/

namespace Erdos215.Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PrimeExtension.OldLine
open Erdos215.Selector.PrimeClassGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Formula (4.12) is good whenever its label lies in the old residue
class. -/
lemma oldLineExtension_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a))
    (hj : jtilde.1 % p = 0) :
    GoodMap (newDenom p u a)
      (oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s lam jtilde) := by
  let D := oldDenom p u a
  let N := newDenom p u a
  let q : Fin N → ℕ := oldShiftGuide p u
  let pi : Fin N → Fin N :=
    inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      (copiedLift p u a s) lam jtilde
  have hpartial : PartialGoodOnClass N p 0 pi := by
    simpa only [N, D, pi, copiedLift, newDenom] using
      inducedFamily_primeCopy_partialGood_oldLine hp hp2
        (oldDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
        hodd s hs lam jtilde hj
  apply partialGoodExtension_good hp (Nat.succ_pos a) hcop
    (show N = p * D by rfl)
    (show N = u * p ^ (a + 1) by
      dsimp only [N]
      rw [newDenom_eq]
      exact Nat.mul_comm _ _)
    q pi
  · intro i j hij
    exact shiftGuide_constant_mod (0 : ZMod p) i j hij
  · intro i
    change (partialGoodShift N u (shiftGuide p u (0 : ZMod p)) i).1 % p = 0
    simpa using
      partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
        (show N = u * p ^ (a + 1) by
          dsimp only [N]
          rw [newDenom_eq]
          exact Nat.mul_comm _ _)
        ⟨0, hp.pos⟩ i
  · exact hpartial

private def primaryCorrection
    (p u a : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) : ℕ :=
  ZMod.val (-((newPrimeComponent p u a hp hcop).reduce lam *
    (newPrimeComponent p u a hp hcop).localQuotient
      ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde)))

/-- The first CRT coordinate of (4.14) has exactly the fixed-translate
shape required by the prime-power goodness lemma. -/
lemma distinguishedValue_primary_formula
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (jtilde i : Fin (newDenom p u a)) :
    (distinguishedValue p u a hp hcop rho s lam jtilde i).1 ≡
      (rho (PrimeClassGood.classDigit p a hp.pos i)).1 +
        primaryCorrection p u a hp hcop lam jtilde
      [MOD p ^ (a + 1)] := by
  let cP := newPrimeComponent p u a hp hcop
  apply (ZMod.natCast_eq_natCast_iff _ _ (p ^ (a + 1))).mp
  have hsplit := congrArg Prod.fst
    (distinguishedValue_split p u a hp hcop rho s lam jtilde i)
  simp only [PrimaryComponent.split_fst_eq_reduce] at hsplit
  rw [PrimaryComponent.reduce_natCast] at hsplit
  change (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
      ZMod cP.q) = _ at hsplit
  have hsplit' :
      (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
          ZMod (p ^ (a + 1))) =
        primaryDistinguishedValue p u a hp hcop rho lam jtilde i := by
    exact hsplit
  let z : ZMod (p ^ (a + 1)) :=
    -((newPrimeComponent p u a hp hcop).reduce lam *
      (newPrimeComponent p u a hp hcop).localQuotient
        ((jtilde.1 : ℤ) - primaryLabelRepresentative p a jtilde))
  have hcorr : primaryCorrection p u a hp hcop lam jtilde = ZMod.val z := by
    rfl
  have hprimary :
      primaryDistinguishedValue p u a hp hcop rho lam jtilde i =
        (((rho (PrimeClassGood.classDigit p a hp.pos i)).1 : ℕ) :
          ZMod (p ^ (a + 1))) + z := by
    simp only [primaryDistinguishedValue, primaryDigit,
      PrimeClassGood.classDigit, z]
    rw [sub_eq_add_neg]
    rfl
  change (((distinguishedValue p u a hp hcop rho s lam jtilde i).1 : ℕ) :
      ZMod (p ^ (a + 1))) = _
  rw [hsplit', hprimary, hcorr]
  let _ : NeZero (p ^ (a + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  push_cast
  rw [ZMod.natCast_zmod_val]

private lemma int_dvd_sub_iff_natModEq (m x y : ℕ) :
    (m : ℤ) ∣ (x : ℤ) - (y : ℤ) ↔ x ≡ y [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  constructor <;> intro h <;> simpa only [neg_sub] using dvd_neg.mpr h

/-- The CRT values prescribed in (4.13)--(4.14) are partially good on the
distinguished source class. -/
lemma distinguishedValue_partialGood
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    PartialGoodOnClass (newDenom p u a) p
      (distinguishedClass p u a hp lam jtilde : ℕ)
      (distinguishedValue p u a hp hcop rho s lam jtilde) := by
  let N := newDenom p u a
  let cP := newPrimeComponent p u a hp hcop
  let f : Fin N → Fin N :=
    distinguishedValue p u a hp hcop rho s lam jtilde
  intro i j hi hj hij
  by_cases hpow : p ^ (a + 1) ∣ indexDiff i j
  · let M := survivingModulus N (indexDiff i j)
    have hMu : M ∣ u := by
      exact survivingModulus_indexDiff_dvd_complement hp
        (show N = p ^ (a + 1) * u by exact newDenom_eq p u a) i j hpow
    have huN : u ∣ N := by
      rw [show N = p ^ (a + 1) * u by exact newDenom_eq p u a]
      exact dvd_mul_left u _
    have hMN : M ∣ N := hMu.trans huN
    let down : ZMod u →+* ZMod M := ZMod.castHom hMu (ZMod M)
    let direct : ZMod N →+* ZMod M := ZMod.castHom hMN (ZMod M)
    have hcomp : down.comp cP.reduceComplement = direct := RingHom.ext_zmod _ _
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam jtilde i
    have hjt : auxiliaryLabel p u a hp hcop lam jtilde j = jt := by
      exact (auxiliaryLabel_eq_of_primaryPower_dvd_indexDiff hp hcop lam
        jtilde i j hpow).symm
    have hjtOld : jt.1 % p = 0 := by
      exact auxiliaryLabel_isOld hp hp2 hcop lam jtilde i hi
    let oldF : Fin N → Fin N :=
      oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s mu jt
    have holdGood : GoodMap N oldF := by
      exact oldLineExtension_good hp hp2 hcop hodd s hs mu jt hjtOld
    intro hbad
    have houtMod : (f i).1 ≡ (f j).1 [MOD M] :=
      (int_dvd_sub_iff_natModEq M (f i).1 (f j).1).mp hbad
    have houtDirect :
        direct (((f i).1 : ℕ) : ZMod N) =
          direct (((f j).1 : ℕ) : ZMod N) := by
      have hcast : (((f i).1 : ℕ) : ZMod M) = (((f j).1 : ℕ) : ZMod M) :=
        (ZMod.natCast_eq_natCast_iff _ _ M).2 houtMod
      simpa [direct] using hcast
    have houtComplement :
        down (cP.reduceComplement (((f i).1 : ℕ) : ZMod N)) =
          down (cP.reduceComplement (((f j).1 : ℕ) : ZMod N)) := by
      calc
        down (cP.reduceComplement (((f i).1 : ℕ) : ZMod N)) =
            direct (((f i).1 : ℕ) : ZMod N) :=
          DFunLike.congr_fun hcomp _
        _ = direct (((f j).1 : ℕ) : ZMod N) := houtDirect
        _ = down (cP.reduceComplement (((f j).1 : ℕ) : ZMod N)) :=
          (DFunLike.congr_fun hcomp _).symm
    have hiSplit := congrArg Prod.snd
      (distinguishedValue_split p u a hp hcop rho s lam jtilde i)
    have hjSplit := congrArg Prod.snd
      (distinguishedValue_split p u a hp hcop rho s lam jtilde j)
    simp only [PrimaryComponent.split_snd_eq_reduceComplement] at hiSplit hjSplit
    let corr : ZMod cP.D := complementLocalQuotient p u a
      ((jtilde.1 : ℤ) - (jt.1 : ℤ))
    have hiComplement :
        cP.reduceComplement (((f i).1 : ℕ) : ZMod N) =
          cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N) -
            cP.reduceComplement lam * corr := by
      rw [hiSplit]
      dsimp only [corr]
      rfl
    have hjComplement :
        cP.reduceComplement (((f j).1 : ℕ) : ZMod N) =
          cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N) -
            cP.reduceComplement lam * corr := by
      rw [hjSplit]
      simp only [complementDistinguishedValue, hjt]
      dsimp only [corr]
      rfl
    rw [hiComplement, hjComplement] at houtComplement
    change down ((show ZMod u from
        cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
          (show ZMod u from cP.reduceComplement lam) * (show ZMod u from corr)) =
      down ((show ZMod u from
        cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
          (show ZMod u from cP.reduceComplement lam) * (show ZMod u from corr))
      at houtComplement
    have houtComplementMap :
        down (show ZMod u from
            cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) =
          down (show ZMod u from
            cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) := by
      calc
        down (show ZMod u from
            cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) =
            down ((show ZMod u from
              cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) -
                (show ZMod u from cP.reduceComplement lam) *
                  (show ZMod u from corr)) :=
          (down.map_sub _ _).symm
        _ = down ((show ZMod u from
              cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
                (show ZMod u from cP.reduceComplement lam) *
                  (show ZMod u from corr)) := houtComplement
        _ = down (show ZMod u from
            cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) -
            down ((show ZMod u from cP.reduceComplement lam) *
              (show ZMod u from corr)) := down.map_sub _ _
    have holdComplement :
        down (cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) =
          down (cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) := by
      exact sub_left_inj.mp houtComplementMap
    have holdCast : (((oldF i).1 : ℕ) : ZMod M) =
        (((oldF j).1 : ℕ) : ZMod M) := by
      calc
        (((oldF i).1 : ℕ) : ZMod M) =
            direct (((oldF i).1 : ℕ) : ZMod N) := by simp [direct]
        _ = down (cP.reduceComplement (((oldF i).1 : ℕ) : ZMod N)) :=
          (DFunLike.congr_fun hcomp _).symm
        _ = down (cP.reduceComplement (((oldF j).1 : ℕ) : ZMod N)) :=
          holdComplement
        _ = direct (((oldF j).1 : ℕ) : ZMod N) :=
          DFunLike.congr_fun hcomp _
        _ = (((oldF j).1 : ℕ) : ZMod M) := by simp [direct]
    have holdMod : (oldF i).1 ≡ (oldF j).1 [MOD M] :=
      (ZMod.natCast_eq_natCast_iff _ _ M).1 holdCast
    exact holdGood i j hij
      ((int_dvd_sub_iff_natModEq M (oldF i).1 (oldF j).1).2 holdMod)
  · exact not_dvd_output_sub_of_primePower_formula hp hcop
      (show N = p ^ (a + 1) * u by exact newDenom_eq p u a)
      rho hrho f
      (fun x _ ↦ distinguishedValue_primary_formula hp hcop rho s lam jtilde x)
      i j hi hj hpow

/-- Every new-label line map obtained from (4.15) is good. -/
lemma newLineExtension_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated)
    (lam : Root (newDenom p u a)) (jtilde : Fin (newDenom p u a)) :
    GoodMap (newDenom p u a)
      (newLineExtension p u a hp hcop rho s lam jtilde) := by
  let N := newDenom p u a
  let target := distinguishedClass p u a hp lam jtilde
  let q : Fin N → ℕ := lineShiftGuide p u a hp lam jtilde
  let pi : Fin N → Fin N := distinguishedValue p u a hp hcop rho s lam jtilde
  apply partialGoodExtension_good hp (Nat.succ_pos a) hcop
    (show N = p * oldDenom p u a by rfl)
    (show N = u * p ^ (a + 1) by
      dsimp only [N]
      rw [newDenom_eq]
      exact Nat.mul_comm _ _)
    q pi
  · intro i j hij
    exact shiftGuide_constant_mod (target : ZMod p) i j hij
  · intro i
    change (partialGoodShift N u (shiftGuide p u (target : ZMod p)) i).1 % p =
      target.1
    exact partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
      (show N = u * p ^ (a + 1) by
        dsimp only [N]
        rw [newDenom_eq]
        exact Nat.mul_comm _ _)
      target i
  · exact distinguishedValue_partialGood hp hp2 hcop hodd rho hrho s hs lam jtilde

/-- Condition (4.3) for the complete pure nontrivial-prime line family. -/
theorem extendedFamily_good
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hodd : Nat.Coprime 2 (oldDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (hrho : GoodPerm (p ^ a) rho)
    (s : LiftData (oldDenom p u a)) (hs : s.Separated) :
    FamilyGood (extendedFamily p u a hp hcop rho s) := by
  intro lam jtilde
  by_cases hj : jtilde.1 % p = 0
  · rw [extendedFamily_old hp hcop rho s lam jtilde hj]
    exact oldLineExtension_good hp hp2 hcop hodd s hs lam jtilde hj
  · rw [extendedFamily_new hp hcop rho s lam jtilde hj]
    exact newLineExtension_good hp hp2 hcop hodd rho hrho s hs lam jtilde

end

end Erdos215.Selector.PurePrimeExtension

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPrimeExtension
import ErdosProblems.Erdos215.SelectorGood

/-!
# The old residue class in the nontrivial prime-extension step

This file isolates formula (4.9) of Jackson--Mauldin.  If the denominator is
enlarged from `D` to `p * D`, both the argument and the line label lie in the
old residue class `0 mod p`, and the lift data are copied from denominator
`D`, then the enlarged line map reduces modulo `D` to the old line map.
Consequently the enlarged map is partially good on that residue class.
-/

namespace Erdos215.Selector.PrimeExtension.OldLine

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PartialGood
open Erdos215.Selector.PrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Reduction of a root at denominator `p * D` to denominator `D`. -/
def reducedRoot (p D : ℕ) (lam : Root (p * D)) : Root D :=
  ⟨ZMod.castHom (dvd_mul_left D p) (ZMod D) lam.1, by
    simpa using congrArg (ZMod.castHom (dvd_mul_left D p) (ZMod D)) lam.property⟩

@[simp] lemma reducedRoot_coe (p D : ℕ) (lam : Root (p * D)) :
    (reducedRoot p D lam : ZMod D) =
      ZMod.castHom (dvd_mul_left D p) (ZMod D) lam.1 := rfl

/-- The quotient of a line label in the old residue class. -/
def reducedLabel (p : ℕ) {D : ℕ} (J : Fin (p * D)) : Fin D :=
  quotientIndex p J

lemma val_eq_p_mul_reducedLabel {p D : ℕ} (hp : 0 < p)
    (J : Fin (p * D)) (hJ : J.1 % p = 0) :
    J.1 = p * (reducedLabel p J).1 := by
  have h := val_eq_mul_quotient_add_remainder p hp J
  simpa only [reducedLabel, remainderIndex, hJ, add_zero] using h

lemma rootVal_reducedRoot {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    rootVal hD (reducedRoot p D lam) = ZMod.val lam.1 % D := by
  let _ : NeZero (p * D) := ⟨Nat.mul_ne_zero hp.ne' hD⟩
  let _ : NeZero D := ⟨hD⟩
  have hcast :
      ((rootVal hD (reducedRoot p D lam) : ℕ) : ZMod D) =
        ((ZMod.val lam.1 : ℕ) : ZMod D) := by
    rw [rootVal_cast, reducedRoot_coe]
    rw [← ZMod.natCast_zmod_val lam.1]
    simp
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast, ZMod.val_natCast] at hv
  have hlt : rootVal hD (reducedRoot p D lam) < D := by
    change (reducedRoot p D lam : ZMod D).val < D
    exact ZMod.val_lt (reducedRoot p D lam : ZMod D)
  calc
    rootVal hD (reducedRoot p D lam) =
        rootVal hD (reducedRoot p D lam) % D := (Nat.mod_eq_of_lt hlt).symm
    _ = ZMod.val lam.1 % D := hv

lemma val_eq_rootVal_add_D_mul_div {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    ZMod.val lam.1 = rootVal hD (reducedRoot p D lam) +
      D * (ZMod.val lam.1 / D) := by
  rw [rootVal_reducedRoot hp hD]
  exact (Nat.mod_add_div (ZMod.val lam.1) D).symm

/-- The exact quotient identity behind the phase correction in (4.9). -/
lemma rootQuotient_reduction {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) :
    p * rootQuotient lam =
      rootQuotient (reducedRoot p D lam) +
        2 * rootVal hD (reducedRoot p D lam) * (ZMod.val lam.1 / D) +
        D * (ZMod.val lam.1 / D) ^ 2 := by
  have hN : p * D ≠ 0 := Nat.mul_ne_zero hp.ne' hD
  have hn := mul_rootQuotient hN lam
  have ho := mul_rootQuotient hD (reducedRoot p D lam)
  change D * rootQuotient (reducedRoot p D lam) =
    1 + rootVal hD (reducedRoot p D lam) ^ 2 at ho
  have hval := val_eq_rootVal_add_D_mul_div hp hD lam
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hD)
  calc
    D * (p * rootQuotient lam) = (p * D) * rootQuotient lam := by ring
    _ = 1 + ZMod.val lam.1 ^ 2 := hn
    _ = 1 + (rootVal hD (reducedRoot p D lam) +
        D * (ZMod.val lam.1 / D)) ^ 2 := by
      conv_lhs => rw [hval]
    _ = D * (rootQuotient (reducedRoot p D lam) +
        2 * rootVal hD (reducedRoot p D lam) * (ZMod.val lam.1 / D) +
        D * (ZMod.val lam.1 / D) ^ 2) := by
      calc
        1 + (rootVal hD (reducedRoot p D lam) +
            D * (ZMod.val lam.1 / D)) ^ 2 =
            (1 + rootVal hD (reducedRoot p D lam) ^ 2) +
              D * (2 * rootVal hD (reducedRoot p D lam) *
                (ZMod.val lam.1 / D) + D * (ZMod.val lam.1 / D) ^ 2) := by ring
        _ = D * rootQuotient (reducedRoot p D lam) +
              D * (2 * rootVal hD (reducedRoot p D lam) *
                (ZMod.val lam.1 / D) + D * (ZMod.val lam.1 / D) ^ 2) := by
              rw [← ho]
        _ = _ := by ring

lemma two_coprime_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime 2 p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)

/-- After reduction to the old denominator, the enlarged phase differs from
the old phase by the root carry.  This is the phase part of formula (4.9). -/
lemma rootPhase_reduction {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (lam : Root (p * D)) :
    (p : ZMod D) *
        ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam) =
      rootPhase (reducedRoot p D lam) +
        (rootVal hD (reducedRoot p D lam) : ZMod D) *
          (ZMod.val lam.1 / D : ℕ) := by
  have h2p : Nat.Coprime 2 p := two_coprime_prime hp hp2
  have h2N : Nat.Coprime 2 (p * D) := h2p.mul_right h2D
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hn := congrArg r (two_mul_rootPhase h2N lam)
  have hn' :
      (2 : ZMod D) * r (rootPhase lam) = (rootQuotient lam : ZMod D) := by
    simpa only [map_mul, map_ofNat, map_natCast] using hn
  have ho := two_mul_rootPhase h2D (reducedRoot p D lam)
  have hq := rootQuotient_reduction hp.pos hD lam
  have hq' :
      (p : ZMod D) * (rootQuotient lam : ZMod D) =
        (rootQuotient (reducedRoot p D lam) : ZMod D) +
          (2 : ZMod D) * rootVal hD (reducedRoot p D lam) *
            (ZMod.val lam.1 / D : ℕ) := by
    have hqCast := congrArg (fun n : ℕ => (n : ZMod D)) hq
    push_cast at hqCast
    simpa using hqCast
  have htwo : IsUnit (2 : ZMod D) := by
    change IsUnit (((2 : ℕ) : ZMod D))
    rw [ZMod.isUnit_iff_coprime]
    exact h2D
  apply htwo.mul_left_cancel
  change (2 : ZMod D) * ((p : ZMod D) * r (rootPhase lam)) = _
  calc
    (2 : ZMod D) * ((p : ZMod D) * r (rootPhase lam)) =
        (p : ZMod D) * ((2 : ZMod D) * r (rootPhase lam)) := by ring
    _ = (p : ZMod D) * (rootQuotient lam : ZMod D) := by rw [hn']
    _ = (rootQuotient (reducedRoot p D lam) : ZMod D) +
          (2 : ZMod D) * rootVal hD (reducedRoot p D lam) *
            (ZMod.val lam.1 / D : ℕ) := hq'
    _ = (2 : ZMod D) *
        (rootPhase (reducedRoot p D lam) +
          (rootVal hD (reducedRoot p D lam) : ZMod D) *
            (ZMod.val lam.1 / D : ℕ)) := by rw [← ho]; ring

/-- On an old line, the canonical line residue is itself an old index. -/
lemma lineResidue_oldIndex {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    lineResidue (Nat.mul_ne_zero hp.ne' hD) lam J (oldIndex p hp i) =
      oldIndex p hp
        (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) := by
  apply Fin.ext
  simp only [lineResidue, oldIndex]
  rw [val_eq_p_mul_reducedLabel hp J hJ]
  have hfactor :
      p * (reducedLabel p J).1 + rootVal (Nat.mul_ne_zero hp.ne' hD) lam *
          (p * i.1) =
        p * ((reducedLabel p J).1 +
          rootVal (Nat.mul_ne_zero hp.ne' hD) lam * i.1) := by ring
  rw [hfactor, Nat.mul_mod_mul_left]
  congr 1
  rw [show rootVal (Nat.mul_ne_zero hp.ne' hD) lam = ZMod.val lam.1 by rfl,
    rootVal_reducedRoot hp hD]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The enlarged carry is the old carry plus the root quotient digit times
the old argument. -/
lemma lineCarry_oldIndex {p D : ℕ} (hp : 0 < p) (hD : D ≠ 0)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    lineCarry (Nat.mul_ne_zero hp.ne' hD) lam J (oldIndex p hp i) =
      lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i +
        (ZMod.val lam.1 / D) * i.1 := by
  simp only [lineCarry, oldIndex]
  rw [val_eq_p_mul_reducedLabel hp J hJ]
  have hfactor :
      p * (reducedLabel p J).1 + rootVal (Nat.mul_ne_zero hp.ne' hD) lam *
          (p * i.1) =
        p * ((reducedLabel p J).1 +
          rootVal (Nat.mul_ne_zero hp.ne' hD) lam * i.1) := by ring
  rw [hfactor, Nat.mul_div_mul_left _ _ hp]
  rw [show rootVal (Nat.mul_ne_zero hp.ne' hD) lam = ZMod.val lam.1 by rfl]
  conv_lhs => rw [val_eq_rootVal_add_D_mul_div hp hD lam]
  rw [show (reducedLabel p J).1 +
      (rootVal hD (reducedRoot p D lam) + D * (ZMod.val lam.1 / D)) * i.1 =
        ((reducedLabel p J).1 +
          rootVal hD (reducedRoot p D lam) * i.1) +
            D * ((ZMod.val lam.1 / D) * i.1) by ring]
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hD)]

/-- Formula (4.9): the copied enlarged line value reduces literally to the
old line value on the old argument and old line-label classes. -/
lemma lineValue_oldIndex {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
        (lineValue (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
          (oldIndex p hp.pos i)) =
      lineValue hD s (reducedRoot p D lam) (reducedLabel p J) i := by
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hj := lineResidue_oldIndex hp.pos hD lam J hJ i
  have hm := lineCarry_oldIndex hp.pos hD lam J hJ i
  have hphase := rootPhase_reduction hp hp2 hD h2D lam
  simp only [lineValue, map_add, map_sub, map_mul, map_intCast, map_natCast]
  rw [hj, hm]
  simp only [primeCopyLift, quotientIndex_oldIndex]
  change
    (s.k i (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) : ZMod D) +
        (reducedRoot p D lam : ZMod D) *
          (s.l i (lineResidue hD (reducedRoot p D lam) (reducedLabel p J) i) : ZMod D) -
        (reducedRoot p D lam : ZMod D) *
          (((lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ℕ) +
            (ZMod.val lam.1 / D) * i.1 : ℕ) : ZMod D) +
        ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam) *
          ((p * i.1 : ℕ) : ZMod D) = _
  rw [show ((p * i.1 : ℕ) : ZMod D) = (p : ZMod D) * (i.1 : ZMod D) by
    push_cast; rfl]
  rw [show (((lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ℕ) +
      (ZMod.val lam.1 / D) * i.1 : ℕ) : ZMod D) =
      (lineCarry hD (reducedRoot p D lam) (reducedLabel p J) i : ZMod D) +
        (ZMod.val lam.1 / D : ℕ) * (i.1 : ZMod D) by push_cast; rfl]
  rw [← mul_assoc, mul_comm
    (ZMod.castHom (dvd_mul_left D p) (ZMod D) (rootPhase lam)) (p : ZMod D),
    hphase]
  rw [rootVal_cast hD (reducedRoot p D lam)]
  ring

/-- Nat-valued form of (4.9), precisely matching the reduction hypothesis
of `partialGoodOnOldClass_of_reduces_good`. -/
lemma inducedFamily_oldIndex_modEq {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (lam : Root (p * D)) (J : Fin (p * D)) (hJ : J.1 % p = 0)
    (i : Fin D) :
    ((inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i) : Fin (p * D)) : ℕ) ≡
      ((inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J) i : Fin D) : ℕ)
        [MOD D] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ D).mp
  let r : ZMod (p * D) →+* ZMod D :=
    ZMod.castHom (dvd_mul_left D p) (ZMod D)
  have hn := congrArg r
    (inducedFamily_formula (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s)
      lam J (oldIndex p hp.pos i))
  have ho := inducedFamily_formula hD s (reducedRoot p D lam) (reducedLabel p J) i
  calc
    (((inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i) : Fin (p * D)) : ℕ) : ZMod D) =
      r (lineValue (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J
        (oldIndex p hp.pos i)) := by
          simpa only [map_natCast] using hn
    _ = lineValue hD s (reducedRoot p D lam) (reducedLabel p J) i :=
      lineValue_oldIndex hp hp2 hD h2D s lam J hJ i
    _ = (((inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J) i :
        Fin D) : ℕ) : ZMod D) := ho.symm

/-- The copied enlarged line map is partially good on the old residue class.
This is the old-line case required before applying Lemma 4.8. -/
theorem inducedFamily_primeCopy_partialGood_oldLine
    {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : D ≠ 0) (h2D : Nat.Coprime 2 D) (s : LiftData D)
    (hs : s.Separated) (lam : Root (p * D)) (J : Fin (p * D))
    (hJ : J.1 % p = 0) :
    PartialGoodOnClass (p * D) p 0
      (inducedFamily (Nat.mul_ne_zero hp.ne_zero hD) (primeCopyLift p s) lam J) := by
  let F : Fin D → Fin D :=
    inducedFamily hD s (reducedRoot p D lam) (reducedLabel p J)
  have hF : GoodMap D F :=
    inducedFamily_good hD h2D s hs (reducedRoot p D lam) (reducedLabel p J)
  apply partialGoodOnOldClass_of_reduces_good p hp.pos F hF
  intro i
  exact inducedFamily_oldIndex_modEq hp hp2 hD h2D s lam J hJ i

end

end Erdos215.Selector.PrimeExtension.OldLine

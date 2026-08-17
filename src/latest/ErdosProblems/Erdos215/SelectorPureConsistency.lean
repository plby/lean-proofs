/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPureExtension

/-!
# Consistency of the pure nontrivial-prime extension

This file verifies the componentwise identity (4.6) for the line family
constructed in `SelectorPureExtension`.  The proof keeps the four source
cases visible: old--old, mixed, new--new at the new primary component, and
new--new at a complementary component (with its same-sign and opposite-sign
subcases).
-/

namespace Erdos215.Selector.PurePrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.PrimeExtension
open Erdos215.Selector.PartialGood

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

private lemma partialGoodShift_cast
    {N u : ℕ} (hN : N ≠ 0) (q : Fin N → ℕ) (i : Fin N) :
    ((((partialGoodShift N u q i : Fin N) : ℕ) : ZMod N)) =
      ((i : ℕ) : ZMod N) + (u : ZMod N) * (q i : ℕ) := by
  let _ : NeZero N := ⟨hN⟩
  simp [partialGoodShift]

private lemma partialGoodExtension_cast
    {N u d : ℕ} (hN : N ≠ 0) (q : Fin N → ℕ)
    (pi : Fin N → Fin N) (i : Fin N) :
    ((((partialGoodExtension N u d q pi i : Fin N) : ℕ) : ZMod N)) =
      (((pi (partialGoodShift N u q i) : Fin N) : ℕ) : ZMod N) +
        (d : ZMod N) * (q i : ℕ) := by
  let _ : NeZero N := ⟨hN⟩
  simp [partialGoodExtension]

private lemma oldLineExtension_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    ((((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
      s lam j i : Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (((inducedFamily
          (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
          (copiedLift p u a s) lam j
          (partialGoodShift (newDenom p u a) u (oldShiftGuide p u) i) :
            Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) +
        (oldDenom p u a : ZMod (newDenom p u a)) *
          (oldShiftGuide p u i : ℕ) := by
  exact partialGoodExtension_cast
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (oldShiftGuide p u)
    (inducedFamily (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      (copiedLift p u a s) lam j) i

private def complementToComponent
    {p u a : ℕ} (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u) :
    ZMod u →+* ZMod c.q :=
  ZMod.castHom hc (ZMod c.q)

private lemma reduce_eq_complementToComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (x : ZMod (newDenom p u a)) :
    c.reduce x = complementToComponent c hc
      ((newPrimeComponent p u a hp hcop).reduceComplement x) := by
  let cP := newPrimeComponent p u a hp hcop
  let down := complementToComponent c hc
  have hhom : down.comp cP.reduceComplement = c.reduce := RingHom.ext_zmod _ _
  exact (DFunLike.congr_fun hhom x).symm

private lemma other_component_D_eq
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hdiv : c.q ∣ u) :
    c.D = p ^ (a + 1) * (u / c.q) := by
  apply Nat.eq_of_mul_eq_mul_left c.q_pos
  calc
    c.q * c.D = newDenom p u a := c.factor_q.symm
    _ = p ^ (a + 1) * u := newDenom_eq p u a
    _ = c.q * (p ^ (a + 1) * (u / c.q)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm c.q (p ^ (a + 1)), Nat.mul_assoc,
        Nat.mul_div_cancel' hdiv]

private lemma cast_complementLocalQuotient_eq_localQuotient
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hdiv : c.q ∣ u)
    (z : ℤ) (hz : (u : ℤ) ∣ z) :
    complementToComponent c hdiv (complementLocalQuotient p u a z) =
      c.localQuotient z := by
  let f : ZMod u →+* ZMod c.q := complementToComponent c hdiv
  apply c.isUnit_D.mul_right_cancel
  rw [c.localQuotient_mul_D]
  have hcomp := congrArg f
    (complementLocalQuotient_mul_power (a := a)
      (complement_ne_zero hp hcop) hcop z)
  simp only [map_mul, map_natCast, map_intCast] at hcomp
  rw [other_component_D_eq hp hcop c hdiv]
  push_cast
  have hpow : f ((p : ℕ) : ZMod u) ^ (a + 1) =
      ((p : ℕ) : ZMod c.q) ^ (a + 1) := by
    rw [map_natCast]
  simp only [map_pow] at hcomp
  rw [← hpow, ← mul_assoc, hcomp]
  rcases hz with ⟨k, rfl⟩
  have hu : (u : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (complement_ne_zero hp hcop)
  have hcq : (c.q : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr c.q_ne_zero
  have hu_factor : (u : ℤ) = (c.q : ℤ) * (u / c.q : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  rw [Int.mul_ediv_cancel_left k hu]
  rw [hu_factor]
  rw [show (c.q : ℤ) * (u / c.q : ℕ) * k =
      (c.q : ℤ) * ((u / c.q : ℕ) * k) by ring,
    Int.mul_ediv_cancel_left ((u / c.q : ℕ) * k) hcq]
  push_cast
  rw [← Int.natCast_div]
  simp only [Int.cast_natCast]
  ring

private lemma complementToComponent_complementDistinguishedValue
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam j i
    complementToComponent c hc
        (complementDistinguishedValue p u a hp hcop s lam j i) =
      c.reduce ((((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jt i) : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
      c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jt.1 : ℤ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  let oldValue : ZMod (newDenom p u a) :=
    (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop) s
      (flippedRoot p u a hp hcop lam)
      (auxiliaryLabel p u a hp hcop lam j i) i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))
  change complementToComponent c hc
      ((show ZMod u from cP.reduceComplement oldValue) -
        (show ZMod u from cP.reduceComplement lam) *
          complementLocalQuotient p u a
            ((j.1 : ℤ) - (auxiliaryLabel p u a hp hcop lam j i).1)) =
    c.reduce oldValue - c.reduce lam *
      c.localQuotient
        ((j.1 : ℤ) - (auxiliaryLabel p u a hp hcop lam j i).1)
  rw [map_sub, map_mul]
  rw [← reduce_eq_complementToComponent hp hcop c hc oldValue]
  rw [← reduce_eq_complementToComponent hp hcop c hc lam]
  rw [cast_complementLocalQuotient_eq_localQuotient hp hcop c hc]
  exact complement_dvd_label_sub_auxiliary p u a hp hcop lam j i

private lemma newPrime_reductions_eq_or_neg
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a)) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce lam₁ = cP.reduce lam₂ ∨ cP.reduce lam₁ = -cP.reduce lam₂ := by
  let cP := newPrimeComponent p u a hp hcop
  have hpTwo : Nat.Coprime p 2 :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  have hodd : Nat.Coprime 2 cP.q := by
    exact hpTwo.symm.pow_right (a + 1)
  exact cP.root_eq_or_eq_neg hodd (cP.reduceRoot lam₁) (cP.reduceRoot lam₂)

private lemma primeRoot_eq_of_newPrime_reduce_eq
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (h : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂) :
    (primeRoot p u a lam₁ : ZMod p) = primeRoot p u a lam₂ := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
    ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  exact congrArg down (by simpa only [cP] using h)

private lemma primeRoot_eq_neg_of_newPrime_reduce_eq_neg
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (h : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂) :
    (primeRoot p u a lam₁ : ZMod p) = -(primeRoot p u a lam₂) := by
  let cP := newPrimeComponent p u a hp hcop
  let down : ZMod cP.q →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p)
  have hcomp : down.comp cP.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
  rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
  calc
    down (cP.reduce lam₁) = down (-cP.reduce lam₂) :=
      congrArg down (by simpa only [cP] using h)
    _ = -down (cP.reduce lam₂) := map_neg down _

private lemma lineShift_reaches_distinguished
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let x := partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam j) i
    x.1 % p = (distinguishedClass p u a hp lam j : ℕ) := by
  apply partialGoodShift_shiftGuide_mod hp (Nat.succ_pos a) hcop.symm
  rw [newDenom_eq, Nat.mul_comm]

private lemma newLineExtension_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    ((((newLineExtension p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      (((distinguishedValue p u a hp hcop rho s lam j
        (partialGoodShift (newDenom p u a) u
          (lineShiftGuide p u a hp lam j) i) : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) +
        (oldDenom p u a : ZMod (newDenom p u a)) *
          (lineShiftGuide p u a hp lam j i : ℕ) := by
  exact partialGoodExtension_cast
    (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (lineShiftGuide p u a hp lam j)
    (distinguishedValue p u a hp hcop rho s lam j) i

private lemma oldShiftGuide_after_lineShift
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    oldShiftGuide p u
        (partialGoodShift (newDenom p u a) u
          (lineShiftGuide p u a hp lam j) i) =
      shiftDigit p u 0
        (distinguishedResidue (primeRoot p u a lam) (primeLabel p j)) := by
  unfold oldShiftGuide shiftGuide
  congr 1
  unfold sourceClass
  rw [← ZMod.natCast_mod]
  rw [lineShift_reaches_distinguished hp hcop lam j i]
  exact distinguishedClass_cast p u a hp lam j

/-- The old label obtained from an arbitrary opposite-primary auxiliary
root, rather than the canonical `flippedRoot`. -/
private def auxiliaryLabelFor
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) : Fin (newDenom p u a) :=
  residueFin (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
    (((j.1 : ℕ) : ZMod (newDenom p u a)) +
      ((i.1 : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu))

@[simp] private lemma auxiliaryLabelFor_cast
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) :
    (((auxiliaryLabelFor hp hcop lam mu j i : ℕ) :
      ZMod (newDenom p u a))) =
      ((j.1 : ℕ) : ZMod (newDenom p u a)) +
        ((i.1 : ℕ) : ZMod (newDenom p u a)) *
          ((lam : ZMod (newDenom p u a)) - mu) := by
  exact residueFin_cast _ _

private lemma auxiliaryLabelFor_relation
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a)) :
    ((i.1 : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu) =
      -(((j.1 : ℕ) : ZMod (newDenom p u a)) -
        ((auxiliaryLabelFor hp hcop lam mu j i : ℕ) :
          ZMod (newDenom p u a))) := by
  rw [auxiliaryLabelFor_cast]
  ring

private lemma auxiliaryLabelFor_isOld
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam mu : Root (newDenom p u a))
    (j i : Fin (newDenom p u a))
    (hi : i.1 % p = (distinguishedClass p u a hp lam j : ℕ))
    (hmu : (primeRoot p u a mu : ZMod p) = -(primeRoot p u a lam : ZMod p)) :
    (auxiliaryLabelFor hp hcop lam mu j i : ℕ) % p = 0 := by
  have hiCast : ((i.1 : ℕ) : ZMod p) =
      distinguishedResidue (primeRoot p u a lam) (primeLabel p j) := by
    calc
      ((i.1 : ℕ) : ZMod p) = ((i.1 % p : ℕ) : ZMod p) :=
        (ZMod.natCast_mod i.1 p).symm
      _ = ((distinguishedClass p u a hp lam j : ℕ) : ZMod p) := by rw [hi]
      _ = _ := distinguishedClass_cast p u a hp lam j
  have hrel := distinguishedResidue_relation
    (primeRoot p u a lam) (primeLabel p j)
    (primeRoot_sub_neg_isUnit hp hp2 lam)
  have hcast := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p))
    (auxiliaryLabelFor_cast hp hcop lam mu j i)
  simp only [map_add, map_mul, map_sub, map_natCast] at hcast
  change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) mu.1 =
    -ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam.1 at hmu
  have hz : (((auxiliaryLabelFor hp hcop lam mu j i : ℕ) : ℕ) : ZMod p) = 0 := by
    rw [hcast, hiCast, hmu]
    change primeLabel p j +
      distinguishedResidue (primeRoot p u a lam) (primeLabel p j) *
        ((primeRoot p u a lam : ZMod p) - -(primeRoot p u a lam : ZMod p)) = 0
    rw [hrel]
    exact add_neg_cancel _
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff
    (auxiliaryLabelFor hp hcop lam mu j i : ℕ) p).mp hz)

private theorem oldLineExtension_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (hoddN : Nat.Coprime 2 (newDenom p u a))
    (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p = 0) (hj₂ : j₂.1 % p = 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s lam₁ j₁ i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s lam₂ j₂ i :
          Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
        -(c.reduce lam₁) * c.localQuotient
          (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let N := newDenom p u a
  let hN : N ≠ 0 := newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)
  let cP := newPrimeComponent p u a hp hcop
  let x : Fin N := partialGoodShift N u (oldShiftGuide p u) i
  have hoddP : Nat.Coprime 2 cP.q := hoddN.of_dvd_right cP.q_dvd
  have hxline : ((x : ℕ) : ZMod N) *
        ((lam₁ : ZMod N) - lam₂) =
      -(((j₁ : ℕ) : ZMod N) - ((j₂ : ℕ) : ZMod N)) := by
    rcases cP.root_eq_or_eq_neg hoddP (cP.reduceRoot lam₁)
        (cP.reduceRoot lam₂) with hsame | hopp
    · change cP.reduce lam₁ = cP.reduce lam₂ at hsame
      have huDiff : (u : ZMod N) *
          ((lam₁ : ZMod N) - lam₂) = 0 := by
        apply cP.split.injective
        apply Prod.ext
        · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
          simp only [map_mul, map_sub, map_natCast, hsame, sub_self, mul_zero,
            map_zero]
        · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
          simp only [map_mul, map_sub, map_natCast, map_zero]
          have hu0 : (u : ZMod cP.D) = 0 := by
            change (u : ZMod u) = 0
            exact ZMod.natCast_self u
          rw [hu0, zero_mul]
      rw [partialGoodShift_cast hN]
      calc
        (((i : ℕ) : ZMod N) + (u : ZMod N) *
              (oldShiftGuide p u i : ℕ)) *
            ((lam₁ : ZMod N) - lam₂) =
            ((i : ℕ) : ZMod N) * ((lam₁ : ZMod N) - lam₂) +
              (oldShiftGuide p u i : ZMod N) *
                ((u : ZMod N) * ((lam₁ : ZMod N) - lam₂)) := by ring
        _ = ((i : ℕ) : ZMod N) * ((lam₁ : ZMod N) - lam₂) := by
          rw [huDiff, mul_zero, add_zero]
        _ = -(((j₁ : ℕ) : ZMod N) - ((j₂ : ℕ) : ZMod N)) := hline
    · change cP.reduce lam₁ = -cP.reduce lam₂ at hopp
      have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
      have hj₁p : ((j₁.1 : ℕ) : ZMod p) = 0 := by
        rw [← ZMod.natCast_mod j₁.1 p, hj₁]
        simp
      have hj₂p : ((j₂.1 : ℕ) : ZMod p) = 0 := by
        rw [← ZMod.natCast_mod j₂.1 p, hj₂]
        simp
      have hlineP := congrArg
        (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
      simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
      change ((i.1 : ℕ) : ZMod p) *
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) =
        -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
      have hlineP' : ((i.1 : ℕ) : ZMod p) *
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) = 0 := by
        simpa only [hj₁p, hj₂p, sub_self, neg_zero] using hlineP
      have hdiffUnit : IsUnit
          ((primeRoot p u a lam₁ : ZMod p) -
            (primeRoot p u a lam₂ : ZMod p)) := by
        rw [hoppP]
        have hu := (primeRoot_sub_neg_isUnit hp hp2 lam₂).neg
        convert hu using 1 <;> ring
      have hiP : ((i.1 : ℕ) : ZMod p) = 0 := by
        apply hdiffUnit.mul_right_cancel
        simpa using hlineP'
      have hiMod : i.1 % p = 0 := by
        have hv := congrArg ZMod.val hiP
        simpa using hv
      have hq : oldShiftGuide p u i = 0 := oldShiftGuide_zero hp.pos i hiMod
      have hxi : x = i := by
        apply Fin.ext
        dsimp only [x, partialGoodShift]
        change (i.1 + u * oldShiftGuide p u i) % N = i.1
        rw [hq, mul_zero, add_zero, Nat.mod_eq_of_lt i.2]
      simpa only [hxi] using hline
  have hbase := inducedFamily_consistent hN hoddN (copiedLift p u a s)
    c lam₁ lam₂ j₁ j₂ x hr hxline
  rw [oldLineExtension_cast hp hcop, oldLineExtension_cast hp hcop]
  simp only [map_add, map_mul]
  dsimp only [N, hN, x] at hbase
  linear_combination hbase

private lemma reduce_distinguishedValue_other_component
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hc : c.q ∣ u)
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let mu := flippedRoot p u a hp hcop lam
    let jt := auxiliaryLabel p u a hp hcop lam j i
    c.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jt i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
        c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jt.1 : ℤ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  let z : ZMod (newDenom p u a) :=
    (((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))
  have hs := distinguishedValue_split p u a hp hcop rho s lam j i
  have hsnd := congrArg Prod.snd hs
  rw [cP.split_snd_eq_reduceComplement] at hsnd
  change c.reduce z = _
  rw [reduce_eq_complementToComponent hp hcop c hc z, hsnd]
  exact complementToComponent_complementDistinguishedValue hp hcop s c hc lam j i

private lemma reduce_distinguishedValue_newPrimeComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam : Root (newDenom p u a)) (j i : Fin (newDenom p u a)) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      primaryDistinguishedValue p u a hp hcop rho lam j i := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  have hs := distinguishedValue_split p u a hp hcop rho s lam j i
  have hfst := congrArg Prod.fst hs
  change cP.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
    Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) = _
  rw [← cP.split_fst_eq_reduce]
  exact hfst

/-- Formula (4.13) is independent of the allowed old auxiliary line. -/
private lemma reduce_distinguishedValue_eq_auxiliary
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam mu : Root (newDenom p u a))
    (j jOld i : Fin (newDenom p u a))
    (hjOld : jOld.1 % p = 0)
    (hi : i.1 % p = (distinguishedClass p u a hp lam j : ℕ))
    (hmuP : (newPrimeComponent p u a hp hcop).reduce mu =
      -(newPrimeComponent p u a hp hcop).reduce lam)
    (hmuC : c.reduce mu = c.reduce lam)
    (haux : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam : ZMod (newDenom p u a)) - mu) =
      -(((j : ℕ) : ZMod (newDenom p u a)) -
        ((jOld : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce ((((distinguishedValue p u a hp hcop rho s lam j i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a))) =
      c.reduce (((oldLineExtension p u a hp.ne_zero
        (complement_ne_zero hp hcop) s mu jOld i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) -
        c.reduce lam * c.localQuotient ((j.1 : ℤ) - (jOld.1 : ℤ)) := by
  let jt := auxiliaryLabel p u a hp hcop lam j i
  let flip := flippedRoot p u a hp hcop lam
  have hcq : c.q ∣ u := component_q_dvd_complement hp hcop c hcp
  have hjt : jt.1 % p = 0 :=
    auxiliaryLabel_isOld hp hp2 hcop lam j i hi
  have hflipC : c.reduce flip = c.reduce lam :=
    reduce_flippedRoot_eq_of_other_component hp hcop c hcp lam
  have hroot : c.reduce flip = c.reduce mu := hflipC.trans hmuC.symm
  have hcanonical := auxiliaryLabel_relation p u a hp hcop lam j i
  have holdLine : ((i : ℕ) : ZMod (newDenom p u a)) *
      ((flip : ZMod (newDenom p u a)) - mu) =
      -(((jt : ℕ) : ZMod (newDenom p u a)) -
        ((jOld : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination haux - hcanonical
  have hold := oldLineExtension_consistent hp hp2 hcop hoddN s c
    flip mu jt jOld i hjt hjOld hroot holdLine
  have hq_jt_old : (c.q : ℤ) ∣ (jt.1 : ℤ) - (jOld.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c flip mu jt jOld i hroot holdLine).2
  have hq_j_jt : (c.q : ℤ) ∣ (j.1 : ℤ) - (jt.1 : ℤ) := by
    have hcu : (c.q : ℤ) ∣ (u : ℤ) := by exact_mod_cast hcq
    exact hcu.trans (complement_dvd_label_sub_auxiliary p u a hp hcop lam j i)
  have hq_j_old : (c.q : ℤ) ∣ (j.1 : ℤ) - (jOld.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam mu j jOld i hmuC.symm haux).2
  have htelescope := localizedQuotient_telescope c.q c.q_ne_zero
    ((c.D : ZMod c.q)⁻¹)
    (j.1 : ℤ) (jOld.1 : ℤ) (jt.1 : ℤ) (jOld.1 : ℤ)
    hq_jt_old hq_j_jt (by simpa using (dvd_zero (c.q : ℤ)))
  change c.localQuotient ((jt.1 : ℤ) - jOld.1) +
      c.localQuotient ((j.1 : ℤ) - jt.1) -
        c.localQuotient ((jOld.1 : ℤ) - jOld.1) =
      c.localQuotient ((j.1 : ℤ) - jOld.1) at htelescope
  have hzero : c.localQuotient 0 = 0 := by
    simp [PrimaryComponent.localQuotient, localizedQuotient]
  rw [sub_self, hzero, sub_zero] at htelescope
  rw [reduce_distinguishedValue_other_component hp hcop rho s c hcq]
  rw [hflipC] at hold
  dsimp only [flip, jt] at hold ⊢
  linear_combination hold - c.reduce lam * htelescope

private lemma new_old_opposite_and_distinguished
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p = 0)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce lam₁ = -cP.reduce lam₂ ∧
      i.1 % p = (distinguishedClass p u a hp lam₁ j₁ : ℕ) := by
  let cP := newPrimeComponent p u a hp hcop
  have hj₂p : ((j₂.1 : ℕ) : ZMod p) = 0 := by
    rw [← ZMod.natCast_mod j₂.1 p, hj₂]
    simp
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hlineP' : ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) - (primeRoot p u a lam₂ : ZMod p)) =
      -((j₁.1 : ℕ) : ZMod p) := by
    simpa only [hj₂p, sub_zero] using hlineP
  rcases newPrime_reductions_eq_or_neg hp hp2 hcop lam₁ lam₂ with hsame | hopp
  · have hsameP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hsame
    have hj₁p : ((j₁.1 : ℕ) : ZMod p) = 0 := by
      rw [hsameP, sub_self, mul_zero] at hlineP'
      simpa using hlineP'.symm
    have hv := congrArg ZMod.val hj₁p
    exact (hj₁ (by simpa using hv)).elim
  · refine ⟨hopp, ?_⟩
    have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
    have hlam₂ : (primeRoot p u a lam₂ : ZMod p) =
        -(primeRoot p u a lam₁ : ZMod p) := by
      linear_combination hoppP
    rw [hlam₂] at hlineP'
    have hiCast := distinguishedResidue_unique
      (primeRoot p u a lam₁) (primeLabel p j₁) ((i.1 : ℕ) : ZMod p)
      (primeRoot_sub_neg_isUnit hp hp2 lam₁) (by
        simpa only [primeLabel] using hlineP')
    have hclass := distinguishedClass_cast p u a hp lam₁ j₁
    have hiClass : ((i.1 : ℕ) : ZMod p) =
        ((distinguishedClass p u a hp lam₁ j₁ : ℕ) : ZMod p) :=
      hiCast.trans hclass.symm
    have hv := congrArg ZMod.val hiClass
    simpa only [ZMod.val_natCast,
      Nat.mod_eq_of_lt (distinguishedClass p u a hp lam₁ j₁).isLt] using hv

private lemma tested_component_ne_newPrime
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hopp : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂) :
    c.p ≠ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro hcp
  have hpq : p ∣ c.q := by
    rw [PrimaryComponent.q, hcp]
    exact dvd_pow_self p c.exp_pos.ne'
  let down : ZMod c.q →+* ZMod p := ZMod.castHom hpq (ZMod p)
  have hcomp : down.comp c.reduce =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) :=
    RingHom.ext_zmod _ _
  have hsameP : (primeRoot p u a lam₁ : ZMod p) = primeRoot p u a lam₂ := by
    change ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₁.1 =
      ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p) lam₂.1
    rw [← DFunLike.congr_fun hcomp, ← DFunLike.congr_fun hcomp]
    exact congrArg down hr
  have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
  have hzero : (primeRoot p u a lam₂ : ZMod p) -
      -(primeRoot p u a lam₂ : ZMod p) = 0 := by
    linear_combination hoppP - hsameP
  exact (primeRoot_sub_neg_isUnit hp hp2 lam₂).ne_zero hzero

private lemma component_eq_newPrimeComponent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p = p) :
    c = newPrimeComponent p u a hp hcop := by
  have hq := component_q_eq_newPrimePower hp hcop c hcp
  have ha : c.a = a + 1 := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [PrimaryComponent.q, hcp] using hq
  have hD : c.D = u := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (a + 1))
    calc
      p ^ (a + 1) * c.D = c.q * c.D := by rw [hq]
      _ = newDenom p u a := c.factor_q.symm
      _ = p ^ (a + 1) * u := newDenom_eq p u a
  cases c with
  | mk cp ca cD cprime cexp cfactor ccop =>
      dsimp only [PrimaryComponent.q] at hcp ha hD
      subst cp
      subst ca
      subst cD
      rfl

private theorem new_old_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p = 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
        s lam₂ j₂ i : Fin (newDenom p u a)) : ℕ) :
          ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  obtain ⟨hopp, hi⟩ :=
    new_old_opposite_and_distinguished hp hp2 hcop lam₁ lam₂ j₁ j₂ i
      hj₁ hj₂ hline
  have hcp : c.p ≠ p := tested_component_ne_newPrime hp hp2 hcop c lam₁ lam₂ hr hopp
  rw [newLineExtension_eq_on_distinguished hp hcop rho s lam₁ j₁ i hi]
  have hopp' : (newPrimeComponent p u a hp hcop).reduce lam₂ =
      -(newPrimeComponent p u a hp hcop).reduce lam₁ := by
    linear_combination hopp
  have hvalue := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₁ lam₂ j₁ j₂ i hj₂ hi hopp' hr.symm hline
  linear_combination hvalue

private theorem old_new_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p = 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((oldLineExtension p u a hp.ne_zero (complement_ne_zero hp hcop)
      s lam₁ j₁ i : Fin (newDenom p u a)) : ℕ) :
        ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  have hline' : ((i : ℕ) : ZMod (newDenom p u a)) *
      ((lam₂ : ZMod (newDenom p u a)) - lam₁) =
      -(((j₂ : ℕ) : ZMod (newDenom p u a)) -
        ((j₁ : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination -hline
  have hswap := new_old_consistent hp hp2 hcop hoddN rho s c
    lam₂ lam₁ j₂ j₁ i hj₂ hj₁ hr.symm hline'
  have hdiv : (c.q : ℤ) ∣ ((j₁ : ℕ) : ℤ) - (j₂ : ℕ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam₁ lam₂ j₁ j₂ i hr hline).2
  have hneg : c.localQuotient (((j₂ : ℕ) : ℤ) - (j₁ : ℕ)) =
      -c.localQuotient (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
    simp only [PrimaryComponent.localQuotient]
    convert localizedQuotient_neg c.q c.q_ne_zero ((c.D : ZMod c.q)⁻¹)
      (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) hdiv using 1 <;> ring
  rw [hneg, ← hr] at hswap
  linear_combination -hswap

private theorem new_new_primary_consistent
    {p u a : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p u)
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hr : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    let cP := newPrimeComponent p u a hp hcop
    cP.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      cP.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(cP.reduce lam₁) * cP.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  dsimp only
  let cP := newPrimeComponent p u a hp hcop
  have hrootP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hr
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hjPrime : primeLabel p j₁ = primeLabel p j₂ := by
    have hcast : ((j₁.1 : ℕ) : ZMod p) = ((j₂.1 : ℕ) : ZMod p) := by
      rw [hrootP, sub_self, mul_zero] at hlineP
      linear_combination hlineP
    exact hcast
  have hclass : distinguishedClass p u a hp lam₁ j₁ =
      distinguishedClass p u a hp lam₂ j₂ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hp.ne_zero
    rw [distinguishedClass_cast, distinguishedClass_cast, hrootP, hjPrime]
  have hguide : lineShiftGuide p u a hp lam₁ j₁ =
      lineShiftGuide p u a hp lam₂ j₂ := by
    funext z
    simp only [lineShiftGuide, hclass]
  let x : Fin (newDenom p u a) :=
    partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₁ j₁) i
  have hx₂ : partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₂ j₂) i = x := by
    rw [← hguide]
  have hjCast : ((j₁.1 : ℕ) : ZMod cP.q) = ((j₂.1 : ℕ) : ZMod cP.q) := by
    have hred := congrArg cP.reduce hline
    simp only [map_mul, map_sub, map_neg, map_natCast] at hred
    change ((i.1 : ℕ) : ZMod cP.q) *
      (cP.reduce lam₁ - cP.reduce lam₂) =
        -(((j₁.1 : ℕ) : ZMod cP.q) - ((j₂.1 : ℕ) : ZMod cP.q)) at hred
    rw [hr, sub_self, mul_zero] at hred
    linear_combination hred
  have hrep : primaryLabelRepresentative p a j₁ =
      primaryLabelRepresentative p a j₂ := by
    have hv := congrArg ZMod.val hjCast
    change ((j₁.1 : ZMod (p ^ (a + 1))).val) =
      ((j₂.1 : ZMod (p ^ (a + 1))).val) at hv
    simpa only [primaryLabelRepresentative, ZMod.val_natCast] using hv
  have hz₁ := primaryPower_dvd_label_sub p a j₁
  have hz₂ := primaryPower_dvd_label_sub p a j₂
  have hquot : cP.localQuotient
        ((j₁.1 : ℤ) - primaryLabelRepresentative p a j₁) -
      cP.localQuotient
        ((j₂.1 : ℤ) - primaryLabelRepresentative p a j₂) =
      cP.localQuotient ((j₁.1 : ℤ) - j₂.1) := by
    simp only [PrimaryComponent.localQuotient]
    rw [← localizedQuotient_sub cP.q cP.q_ne_zero
      ((cP.D : ZMod cP.q)⁻¹) _ _ (by simpa [cP] using hz₁)
        (by simpa [cP] using hz₂)]
    congr 1
    rw [hrep]
    ring
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i]
  rw [hx₂]
  simp only [map_add, map_mul]
  rw [reduce_distinguishedValue_newPrimeComponent hp hcop rho s,
    reduce_distinguishedValue_newPrimeComponent hp hcop rho s]
  simp only [PrimaryComponent.reduce_natCast]
  simp only [primaryDistinguishedValue]
  rw [hr, hrep]
  dsimp only [cP] at hquot ⊢
  rw [hrep] at hquot
  dsimp only [x]
  rw [congrFun hguide i]
  linear_combination
    -(newPrimeComponent p u a hp hcop).reduce lam₂ * hquot

private theorem new_new_complement_same_sign
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hsame : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      (newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let cP := newPrimeComponent p u a hp hcop
  have hcq : c.q ∣ u := component_q_dvd_complement hp hcop c hcp
  have hrootP := primeRoot_eq_of_newPrime_reduce_eq hp hcop lam₁ lam₂ hsame
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hjPrime : primeLabel p j₁ = primeLabel p j₂ := by
    rw [hrootP, sub_self, mul_zero] at hlineP
    change ((j₁.1 : ℕ) : ZMod p) = ((j₂.1 : ℕ) : ZMod p)
    linear_combination hlineP
  have hclass : distinguishedClass p u a hp lam₁ j₁ =
      distinguishedClass p u a hp lam₂ j₂ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hp.ne_zero
    rw [distinguishedClass_cast, distinguishedClass_cast, hrootP, hjPrime]
  have hguide : lineShiftGuide p u a hp lam₁ j₁ =
      lineShiftGuide p u a hp lam₂ j₂ := by
    funext z
    simp only [lineShiftGuide, hclass]
  let x : Fin (newDenom p u a) :=
    partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₁ j₁) i
  have hx₂ : partialGoodShift (newDenom p u a) u
      (lineShiftGuide p u a hp lam₂ j₂) i = x := by rw [← hguide]
  have hxclass₁ : x.1 % p = (distinguishedClass p u a hp lam₁ j₁ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₁ j₁ i
  have hxclass₂ : x.1 % p = (distinguishedClass p u a hp lam₂ j₂ : ℕ) := by
    rw [← hclass]
    exact hxclass₁
  let mu := flippedRoot p u a hp hcop lam₁
  let jt := auxiliaryLabel p u a hp hcop lam₁ j₁ x
  have hjt : jt.1 % p = 0 :=
    auxiliaryLabel_isOld hp hp2 hcop lam₁ j₁ x hxclass₁
  have hmuP : cP.reduce mu = -cP.reduce lam₂ := by
    dsimp only [mu, cP]
    rw [newPrimeComponent_reduce_flippedRoot, hsame]
  have hmuC : c.reduce mu = c.reduce lam₂ := by
    dsimp only [mu]
    rw [reduce_flippedRoot_eq_of_other_component hp hcop c hcp, hr]
  have huDiff : (u : ZMod (newDenom p u a)) *
      ((lam₁ : ZMod (newDenom p u a)) - lam₂) = 0 := by
    apply cP.split.injective
    apply Prod.ext
    · rw [cP.split_fst_eq_reduce, cP.split_fst_eq_reduce]
      simp only [map_mul, map_sub, map_natCast, map_zero]
      rw [hsame, sub_self, mul_zero]
    · rw [cP.split_snd_eq_reduceComplement, cP.split_snd_eq_reduceComplement]
      simp only [map_mul, map_sub, map_natCast, map_zero]
      have hu0 : (u : ZMod cP.D) = 0 := by
        change (u : ZMod u) = 0
        exact ZMod.natCast_self u
      rw [hu0, zero_mul]
  have hxline : ((x : ℕ) : ZMod (newDenom p u a)) *
      ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a))) := by
    rw [partialGoodShift_cast
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))]
    calc
      _ = ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam₁ : ZMod (newDenom p u a)) - lam₂) +
        (lineShiftGuide p u a hp lam₁ j₁ i : ZMod (newDenom p u a)) *
          ((u : ZMod (newDenom p u a)) *
            ((lam₁ : ZMod (newDenom p u a)) - lam₂)) := by ring
      _ = ((i : ℕ) : ZMod (newDenom p u a)) *
          ((lam₁ : ZMod (newDenom p u a)) - lam₂) := by rw [huDiff]; ring
      _ = _ := hline
  have haux₁ := auxiliaryLabel_relation p u a hp hcop lam₁ j₁ x
  have haux₂ : ((x : ℕ) : ZMod (newDenom p u a)) *
      ((lam₂ : ZMod (newDenom p u a)) - mu) =
      -(((j₂ : ℕ) : ZMod (newDenom p u a)) -
        ((jt : ℕ) : ZMod (newDenom p u a))) := by
    linear_combination haux₁ - hxline
  have hv₁ := reduce_distinguishedValue_other_component hp hcop rho s c hcq
    lam₁ j₁ x
  have hv₂ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₂ mu j₂ jt x hjt hxclass₂ hmuP hmuC haux₂
  have hz₁ : (c.q : ℤ) ∣ (j₁.1 : ℤ) - (jt.1 : ℤ) := by
    have hcu : (c.q : ℤ) ∣ (u : ℤ) := by exact_mod_cast hcq
    exact hcu.trans (complement_dvd_label_sub_auxiliary p u a hp hcop lam₁ j₁ x)
  have hz₂ : (c.q : ℤ) ∣ (j₂.1 : ℤ) - (jt.1 : ℤ) :=
    (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
      (newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop))
      c lam₂ mu j₂ jt x hmuC.symm haux₂).2
  have hquot : c.localQuotient ((j₁.1 : ℤ) - jt.1) -
      c.localQuotient ((j₂.1 : ℤ) - jt.1) =
      c.localQuotient ((j₁.1 : ℤ) - j₂.1) := by
    simp only [PrimaryComponent.localQuotient]
    rw [← localizedQuotient_sub c.q c.q_ne_zero ((c.D : ZMod c.q)⁻¹)
      _ _ hz₁ hz₂]
    congr 1
    ring
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i, hx₂]
  simp only [map_add, map_mul]
  rw [hv₁, hv₂, hr]
  simp only [PrimaryComponent.reduce_natCast]
  dsimp only [mu, jt] at hquot ⊢
  have hguideC :
      ((lineShiftGuide p u a hp lam₁ j₁ i : ℕ) : ZMod c.q) =
        ((lineShiftGuide p u a hp lam₂ j₂ i : ℕ) : ZMod c.q) :=
    congrArg (fun n : ℕ ↦ (n : ZMod c.q)) (congrFun hguide i)
  linear_combination -(c.reduce lam₂) * hquot +
    (oldDenom p u a : ZMod c.q) * hguideC

private theorem new_new_complement_opposite_sign
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u) (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a))) (s : LiftData (oldDenom p u a))
    (c : PrimaryComponent (newDenom p u a)) (hcp : c.p ≠ p)
    (lam₁ lam₂ : Root (newDenom p u a))
    (j₁ j₂ i : Fin (newDenom p u a))
    (hj₁ : j₁.1 % p ≠ 0) (hj₂ : j₂.1 % p ≠ 0)
    (hr : c.reduce lam₁ = c.reduce lam₂)
    (hopp : (newPrimeComponent p u a hp hcop).reduce lam₁ =
      -(newPrimeComponent p u a hp hcop).reduce lam₂)
    (hline : ((i : ℕ) : ZMod (newDenom p u a)) *
        ((lam₁ : ZMod (newDenom p u a)) - lam₂) =
      -(((j₁ : ℕ) : ZMod (newDenom p u a)) -
        ((j₂ : ℕ) : ZMod (newDenom p u a)))) :
    c.reduce (((newLineExtension p u a hp hcop rho s lam₁ j₁ i :
      Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) -
      c.reduce (((newLineExtension p u a hp hcop rho s lam₂ j₂ i :
        Fin (newDenom p u a)) : ℕ) : ZMod (newDenom p u a)) =
      -(c.reduce lam₁) * c.localQuotient
        (((j₁ : ℕ) : ℤ) - (j₂ : ℕ)) := by
  let N := newDenom p u a
  let hN : N ≠ 0 := newDenom_ne_zero hp.ne_zero (complement_ne_zero hp hcop)
  let cP := newPrimeComponent p u a hp hcop
  let q₁ := lineShiftGuide p u a hp lam₁ j₁ i
  let q₂ := lineShiftGuide p u a hp lam₂ j₂ i
  let x₁ : Fin N := partialGoodShift N u (lineShiftGuide p u a hp lam₁ j₁) i
  let x₂ : Fin N := partialGoodShift N u (lineShiftGuide p u a hp lam₂ j₂) i
  let r₂ := oldShiftGuide p u x₁
  let r₁ := oldShiftGuide p u x₂
  let k₃ := auxiliaryLabelFor hp hcop lam₁ lam₂ j₁ x₁
  let k₄ := auxiliaryLabelFor hp hcop lam₂ lam₁ j₂ x₂
  let y₁ : Fin N := partialGoodShift N u (oldShiftGuide p u) x₁
  let y₂ : Fin N := partialGoodShift N u (oldShiftGuide p u) x₂
  have hoppP := primeRoot_eq_neg_of_newPrime_reduce_eq_neg hp hcop lam₁ lam₂ hopp
  have hoppP' : (primeRoot p u a lam₂ : ZMod p) =
      -(primeRoot p u a lam₁ : ZMod p) := by linear_combination hoppP
  have hlineP := congrArg
    (ZMod.castHom (prime_dvd_newDenom p u a) (ZMod p)) hline
  simp only [map_mul, map_sub, map_neg, map_natCast] at hlineP
  change ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) -
        (primeRoot p u a lam₂ : ZMod p)) =
    -(((j₁.1 : ℕ) : ZMod p) - ((j₂.1 : ℕ) : ZMod p)) at hlineP
  have hlineP' : ((i.1 : ℕ) : ZMod p) *
      ((primeRoot p u a lam₁ : ZMod p) - (primeRoot p u a lam₂ : ZMod p)) =
      -(primeLabel p j₁ - primeLabel p j₂) := by
    simpa only [primeLabel] using hlineP
  have hcross := shiftDigit_cross_eq (u := u) hp
    (primeRoot p u a lam₁) (primeRoot p u a lam₂)
    (primeLabel p j₁) (primeLabel p j₂) ((i.1 : ℕ) : ZMod p)
    (primeRoot_sub_neg_isUnit hp hp2 lam₁) hoppP' hlineP'
  have hsum0 := shiftDigit_cross_sum (u := u) hp
    (primeRoot p u a lam₁) (primeRoot p u a lam₂)
    (primeLabel p j₁) (primeLabel p j₂) ((i.1 : ℕ) : ZMod p)
    (primeRoot_sub_neg_isUnit hp hp2 lam₁) hoppP' hlineP'
  have hs₇₁ : q₁ = r₁ := by
    dsimp only [q₁, r₁]
    rw [oldShiftGuide_after_lineShift hp hcop lam₂ j₂ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hcross.1
  have hs₇₂ : q₂ = r₂ := by
    dsimp only [q₂, r₂]
    rw [oldShiftGuide_after_lineShift hp hcop lam₁ j₁ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hcross.2
  have hsum : q₁ + r₂ = q₂ + r₁ := by
    dsimp only [q₁, q₂, r₁, r₂]
    rw [oldShiftGuide_after_lineShift hp hcop lam₁ j₁ i,
      oldShiftGuide_after_lineShift hp hcop lam₂ j₂ i]
    simpa only [lineShiftGuide, shiftGuide, sourceClass, distinguishedClass_cast] using hsum0
  have hx₁class : x₁.1 % p =
      (distinguishedClass p u a hp lam₁ j₁ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₁ j₁ i
  have hx₂class : x₂.1 % p =
      (distinguishedClass p u a hp lam₂ j₂ : ℕ) :=
    lineShift_reaches_distinguished hp hcop lam₂ j₂ i
  have hk₃old : k₃.1 % p = 0 :=
    auxiliaryLabelFor_isOld hp hp2 hcop lam₁ lam₂ j₁ x₁ hx₁class hoppP'
  have hk₄old : k₄.1 % p = 0 :=
    auxiliaryLabelFor_isOld hp hp2 hcop lam₂ lam₁ j₂ x₂ hx₂class hoppP
  have haux₁ := auxiliaryLabelFor_relation hp hcop lam₁ lam₂ j₁ x₁
  have haux₂ := auxiliaryLabelFor_relation hp hcop lam₂ lam₁ j₂ x₂
  have hy : y₂ = y₁ := by
    apply Erdos215.Selector.Separation.fin_eq_of_zmod_cast_eq hN
    rw [partialGoodShift_cast hN, partialGoodShift_cast hN,
      partialGoodShift_cast hN, partialGoodShift_cast hN]
    change ((i : ℕ) : ZMod N) + (u : ZMod N) * (q₂ : ℕ) +
        (u : ZMod N) * (r₁ : ℕ) =
      ((i : ℕ) : ZMod N) + (u : ZMod N) * (q₁ : ℕ) +
        (u : ZMod N) * (r₂ : ℕ)
    have hsumN := congrArg (fun n : ℕ ↦ (n : ZMod N)) hsum
    push_cast at hsumN
    linear_combination -(u : ZMod N) * hsumN
  have hyline : ((y₁ : ℕ) : ZMod N) *
      ((lam₂ : ZMod N) - lam₁) =
      -(((k₃ : ℕ) : ZMod N) - ((k₄ : ℕ) : ZMod N)) := by
    have haux₁' : (((i : ℕ) : ZMod N) + (u : ZMod N) * (q₁ : ℕ)) *
        ((lam₁ : ZMod N) - lam₂) =
        -(((j₁ : ℕ) : ZMod N) - ((k₃ : ℕ) : ZMod N)) := by
      rw [← partialGoodShift_cast hN]
      exact haux₁
    have haux₂' : (((i : ℕ) : ZMod N) + (u : ZMod N) * (q₂ : ℕ)) *
        ((lam₂ : ZMod N) - lam₁) =
        -(((j₂ : ℕ) : ZMod N) - ((k₄ : ℕ) : ZMod N)) := by
      rw [← partialGoodShift_cast hN]
      exact haux₂
    have hrel := auxiliaryOldLines_relation
      ((i : ℕ) : ZMod N) ((u : ZMod N) * (q₁ : ℕ))
      ((u : ZMod N) * (q₂ : ℕ))
      ((j₁ : ℕ) : ZMod N) ((j₂ : ℕ) : ZMod N)
      ((k₃ : ℕ) : ZMod N) ((k₄ : ℕ) : ZMod N)
      (lam₁ : ZMod N) (lam₂ : ZMod N) hline haux₁' haux₂'
    rw [partialGoodShift_cast hN, partialGoodShift_cast hN]
    dsimp only [q₁, q₂, r₂] at hs₇₂ ⊢
    push_cast at hs₇₂ ⊢
    rw [← hs₇₂]
    simpa only [add_assoc] using hrel
  have hbase := inducedFamily_consistent hN hoddN (copiedLift p u a s)
    c lam₂ lam₁ k₃ k₄ y₁ hr.symm hyline
  have hmu₁P : cP.reduce lam₂ = -cP.reduce lam₁ := by linear_combination hopp
  have hv₁ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₁ lam₂ j₁ k₃ x₁ hk₃old hx₁class hmu₁P hr.symm haux₁
  have hv₂ := reduce_distinguishedValue_eq_auxiliary hp hp2 hcop hoddN rho s
    c hcp lam₂ lam₁ j₂ k₄ x₂ hk₄old hx₂class hopp hr haux₂
  have hz₃₄ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₂ lam₁ k₃ k₄ y₁ hr.symm hyline).2
  have hz₁₃ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₁ lam₂ j₁ k₃ x₁ hr haux₁).2
  have hz₂₄ := (Erdos215.Selector.Final.PrimaryComponent.relation_divisibility
    hN c lam₂ lam₁ j₂ k₄ x₂ hr.symm haux₂).2
  have htelescope := localizedQuotient_telescope c.q c.q_ne_zero
    ((c.D : ZMod c.q)⁻¹) (j₁.1 : ℤ) (j₂.1 : ℤ)
      (k₃.1 : ℤ) (k₄.1 : ℤ) hz₃₄ hz₁₃ hz₂₄
  change c.localQuotient ((k₃.1 : ℤ) - k₄.1) +
      c.localQuotient ((j₁.1 : ℤ) - k₃.1) -
        c.localQuotient ((j₂.1 : ℤ) - k₄.1) =
      c.localQuotient ((j₁.1 : ℤ) - j₂.1) at htelescope
  have hsumC : ((q₁ : ℕ) : ZMod c.q) + (r₂ : ℕ) =
      ((q₂ : ℕ) : ZMod c.q) + (r₁ : ℕ) := by
    have hsumC' := congrArg (fun n : ℕ ↦ (n : ZMod c.q)) hsum
    push_cast at hsumC'
    exact hsumC'
  have hsumCRed :
      c.reduce ((q₁ : ℕ) : ZMod (newDenom p u a)) +
          c.reduce ((r₂ : ℕ) : ZMod (newDenom p u a)) =
        c.reduce ((q₂ : ℕ) : ZMod (newDenom p u a)) +
          c.reduce ((r₁ : ℕ) : ZMod (newDenom p u a)) := by
    have hsumCRed' := congrArg
      (fun n : ℕ ↦ c.reduce ((n : ℕ) : ZMod (newDenom p u a))) hsum
    simpa only [Nat.cast_add, map_add] using hsumCRed'
  rw [newLineExtension_cast hp hcop rho s lam₁ j₁ i,
    newLineExtension_cast hp hcop rho s lam₂ j₂ i]
  simp only [map_add, map_mul]
  rw [hv₁, hv₂]
  rw [oldLineExtension_cast hp hcop, oldLineExtension_cast hp hcop]
  simp only [map_add, map_mul]
  have hy' : partialGoodShift (newDenom p u a) u (oldShiftGuide p u) x₂ =
      partialGoodShift (newDenom p u a) u (oldShiftGuide p u) x₁ := by
    simpa only [N, y₁, y₂] using hy
  rw [hy', hr]
  dsimp only [q₁, q₂, r₁, r₂, k₃, k₄, y₁] at hbase htelescope hsumC hsumCRed ⊢
  linear_combination hbase - c.reduce lam₂ * htelescope +
    c.reduce (oldDenom p u a : ZMod (newDenom p u a)) * hsumCRed

/-- The family produced by the pure nontrivial-prime construction satisfies
 the exact componentwise consistency identity (4.6). -/
theorem extendedFamily_consistent
    {p u a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p u)
    (hoddN : Nat.Coprime 2 (newDenom p u a))
    (rho : Equiv.Perm (Fin (p ^ a)))
    (s : LiftData (oldDenom p u a)) :
    FamilyConsistent (extendedFamily p u a hp hcop rho s) := by
  intro c lam₁ lam₂ j₁ j₂ i hr hline
  by_cases hj₁ : j₁.1 % p = 0
  · by_cases hj₂ : j₂.1 % p = 0
    · rw [extendedFamily_old hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_old hp hcop rho s lam₂ j₂ hj₂]
      exact oldLineExtension_consistent hp hp2 hcop hoddN s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
    · rw [extendedFamily_old hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_new hp hcop rho s lam₂ j₂ hj₂]
      exact old_new_consistent hp hp2 hcop hoddN rho s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
  · by_cases hj₂ : j₂.1 % p = 0
    · rw [extendedFamily_new hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_old hp hcop rho s lam₂ j₂ hj₂]
      exact new_old_consistent hp hp2 hcop hoddN rho s c
        lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hline
    · rw [extendedFamily_new hp hcop rho s lam₁ j₁ hj₁,
        extendedFamily_new hp hcop rho s lam₂ j₂ hj₂]
      rcases component_classification hp hcop c with hprimary | hother
      · obtain ⟨hcp, _hq⟩ := hprimary
        have hcEq := component_eq_newPrimeComponent hp hcop c hcp
        subst c
        exact new_new_primary_consistent hp hcop rho s lam₁ lam₂
          j₁ j₂ i hr hline
      · obtain ⟨hcp, _hcq⟩ := hother
        rcases newPrime_reductions_eq_or_neg hp hp2 hcop lam₁ lam₂ with
          hsame | hopp
        · exact new_new_complement_same_sign hp hp2 hcop hoddN rho s c hcp
            lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hsame hline
        · exact new_new_complement_opposite_sign hp hp2 hcop hoddN rho s c hcp
            lam₁ lam₂ j₁ j₂ i hj₁ hj₂ hr hopp hline

end

end Erdos215.Selector.PurePrimeExtension

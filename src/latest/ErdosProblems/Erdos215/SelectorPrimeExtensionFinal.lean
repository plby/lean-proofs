/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorPureGoodness
import ErdosProblems.Erdos215.SelectorPureConsistency
import ErdosProblems.Erdos215.SelectorPrimeSplit
import ErdosProblems.Erdos215.SelectorComplete
import ErdosProblems.Erdos215.SelectorCompleteFactorization
import ErdosProblems.Erdos215.SelectorCoset
import ErdosProblems.Erdos215.SelectorLimit

/-!
# The literal prime-extension theorem

This file closes the finite part of the Jackson--Mauldin construction.  For
an odd prime congruent to one modulo four, it splits a pure denominator as
`u * p^a`, applies the explicit good and consistent line family, and
reconstructs a separated literal extension.  The nontrivial/trivial
factorization and the coset gluing theorem then reduce a general denominator
to that pure case.  The prime `2` and primes congruent to three modulo four
use the elementary copied extensions already proved in `Selector.lean`.
-/

namespace Erdos215.Selector.PrimeExtension

open Erdos215.Selector
open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Separation
open Erdos215.Selector.PurePrimeExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Transport a literal prime extension across an equality of its old
denominators. -/
private theorem transportPrimeExtensionResult
    {p d e : ℕ} (hp : 0 < p) (h : d = e) (s : LiftData e)
    (H : ∃ t : LiftData (p * d),
      PrimeExtends p hp (s.transport h.symm) t ∧ t.Separated) :
    ∃ t : LiftData (p * e), PrimeExtends p hp s t ∧ t.Separated := by
  subst e
  simpa only [LiftData.transport_rfl] using H

/-- Literal extension across a `1 mod 4` prime when every prime divisor of
the old denominator is also `1 mod 4`. -/
theorem pureLiteralPrimeExtension
    {p d : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hp2 : p ≠ 2) (hd : d ≠ 0)
    (hodd : Nat.Coprime 2 d)
    (hpure : ∀ q : ℕ, q.Prime → q ∣ d → q % 4 = 1)
    (s : LiftData d) (hs : s.Separated) :
    ∃ t : LiftData (p * d), PrimeExtends p hp.pos s t ∧ t.Separated := by
  obtain ⟨u, a, hsplit, hu, hcop⟩ :=
    PrimeSplit.exists_eq_complement_mul_pow hp hd
  subst d
  have h2p : Nat.Coprime 2 p := by
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (fun h ↦
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
  have hoddN : Nat.Coprime 2 (newDenom p u a) := by
    simpa only [newDenom, oldDenom] using Nat.Coprime.mul_right h2p hodd
  have hN : newDenom p u a ≠ 0 :=
    newDenom_ne_zero hp.ne_zero hu
  have hpureN : ∀ q : ℕ, q.Prime → q ∣ newDenom p u a → q % 4 = 1 := by
    intro q hq hqN
    have hqMul : q ∣ p * oldDenom p u a := by
      simpa only [newDenom] using hqN
    rcases hq.dvd_mul.mp hqMul with hqp | hqOld
    · have hqpEq : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      simpa only [hqpEq] using hp1
    · exact hpure q hq hqOld
  obtain ⟨rho, hrho⟩ := PrimePowerGood.exists_goodPerm_primePower p a hp
  let C : CompleteComponents (newDenom p u a) :=
    Complete.canonicalCompleteComponents (newDenom p u a) hN
  have hroot : ConflictRootLineProperty (newDenom p u a) :=
    Complete.canonical_conflictRootLineProperty hN hpureN
  obtain ⟨lam₀⟩ := Complete.canonical_root_nonempty hN hpureN
  have hgood : FamilyGood (extendedFamily p u a hp hcop rho s) :=
    extendedFamily_good hp hp2 hcop hodd rho hrho s hs
  have hcons : FamilyConsistent (extendedFamily p u a hp hcop rho s) :=
    extendedFamily_consistent hp hp2 hcop hoddN rho s
  exact purePrimeExtension_of_family hp hcop hoddN C hroot rho s
    hgood hcons lam₀

/-- The pure extension theorem in the form needed by the `P`/`Q` coset
reduction: the old denominator is the nontrivial part of an arbitrary
nonzero denominator. -/
theorem pureLiteralPrimeExtension_nontrivialPart
    (p : ℕ) (hp : p.Prime) (hp1 : p % 4 = 1)
    (d : ℕ) (hd : d ≠ 0)
    (s : LiftData (nontrivialPart d)) (hs : s.Separated) :
    ∃ t : LiftData (p * nontrivialPart d),
      PrimeExtends p hp.pos s t ∧ t.Separated := by
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    norm_num at hp1
  exact pureLiteralPrimeExtension hp hp1 hp2
    (nontrivialPart_ne_zero d hd)
    (coprime_two_nontrivialPart d hd)
    (fun q hq hqP ↦ ((prime_dvd_nontrivialPart_iff d q hd hq).mp hqP).2)
    s hs

/-- Every separated finite selector has a literal separated extension across
every prime.  This is the exact finite hypothesis consumed by the direct
limit construction. -/
theorem literalPrimeExtension : Erdos215.Selector.LiteralPrimeExtensionHypothesis := by
  intro p hp d hd s hs
  rcases hp.eq_two_or_odd with hpEq | hpOdd
  · subst p
    exact ⟨doubleLift s, doubleLift_primeExtends s,
      doubleLift_separated hd s hs⟩
  · have hpMod : p % 4 = 1 ∨ p % 4 = 3 :=
      (Nat.odd_mod_four_iff).mp hpOdd
    rcases hpMod with hp1 | hp3
    · let P := nontrivialPart d
      let Q := trivialPart d
      have hP : 0 < P := Nat.pos_of_ne_zero (nontrivialPart_ne_zero d hd)
      have hQ : 0 < Q := Nat.pos_of_ne_zero (trivialPart_ne_zero d hd)
      have hPQ : P * Q = d := by
        simpa only [P, Q] using nontrivialPart_mul_trivialPart d hd
      have hp2 : p ≠ 2 := by
        intro hpEq
        subst p
        norm_num at hp1
      have hcopQ : Nat.Coprime p Q := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpQ
        have hpQ' : p ∣ trivialPart d := by
          simpa only [Q] using hpQ
        rcases ((prime_dvd_trivialPart_iff d p hd hp).mp hpQ').2 with htwo | hthree
        · exact hp2 htwo
        · omega
      have hRigid : SquareNormRigid Q := by
        simpa only [Q] using squareNormRigid_trivialPart d hd
      let sPQ : LiftData (P * Q) := s.transport hPQ.symm
      have hsPQ : sPQ.Separated :=
        LiftData.separated_transport hPQ.symm s hs
      have hresult := primeExtension_of_pure_cosets p hp.pos P Q hP hQ hcopQ
        hRigid sPQ hsPQ (fun u hu ↦ by
          simpa only [P] using
            pureLiteralPrimeExtension_nontrivialPart p hp hp1 d hd u hu)
      apply transportPrimeExtensionResult hp.pos hPQ s
      simpa only [sPQ] using hresult
    · letI : Fact p.Prime := ⟨hp⟩
      exact primeCopy_step_of_prime_mod_four_eq_three p hp3 hd s hs

end

end Erdos215.Selector.PrimeExtension

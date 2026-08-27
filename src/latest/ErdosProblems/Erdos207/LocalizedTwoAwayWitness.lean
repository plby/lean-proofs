/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SeparatedLocalizedRootedThreat
import ErdosProblems.Erdos207.TwoAwayThreatWeight

/-! # Two-away witnesses localized to a prescribed third-vertex set -/

namespace Erdos207

open Finset

noncomputable section

abbrev LocalizedTwoAwayWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (a b : V) (U : Finset V) :=
  {w : TwoAwayThreatWitness V F T //
    a ∈ w.1.2.1 ∧ b ∈ w.1.2.1 ∧ ∃ u ∈ w.1.2.1, u ∈ U ∧ u ≠ a ∧ u ≠ b}

noncomputable instance instFintypeLocalizedTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) (a b : V) (U : Finset V) :
    Fintype (LocalizedTwoAwayWitness V F T a b U) := Fintype.ofFinite _

def localizedTwoAwayRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (w : LocalizedTwoAwayWitness V F T a b U) : TripleSystemOn V :=
  twoAwayThreatRemainder w.1

def localizedTwoAwayToRooted
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (w : LocalizedTwoAwayWitness V F T a b U) : LocalizedRootedThreatWitness V F a b U :=
  ⟨⟨w.1.1, w.1.2.1, w.1.2.2.1, w.2.1, w.2.2.1⟩, w.2.2.2⟩

theorem localizedTwoAwayToRooted_injective
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V} :
    Function.Injective (localizedTwoAwayToRooted :
      LocalizedTwoAwayWitness V F T a b U → LocalizedRootedThreatWitness V F a b U) := by
  intro w z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v ↦ v.1.1) h

theorem localizedTwoAwayToRooted_remainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (w : LocalizedTwoAwayWitness V F T a b U) :
    localizedRootedThreatRemainder (localizedTwoAwayToRooted w) = insert T (localizedTwoAwayRemainder w) := by
  change w.1.1.1.erase w.1.1.2 = insert T ((w.1.1.1.erase w.1.1.2).erase T)
  exact (insert_erase (mem_erase.mpr ⟨w.1.2.2.2.2.symm, w.1.2.2.2.1⟩)).symm

abbrev LocalizedTwoAwayRemainderFiber
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :=
  {w : LocalizedTwoAwayWitness V F T a b U // localizedTwoAwayRemainder w = R}

noncomputable instance instFintypeLocalizedTwoAwayRemainderFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :
    Fintype (LocalizedTwoAwayRemainderFiber V F T a b U R) := Fintype.ofFinite _

def localizedTwoAwayFiberToRooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {T : TripleOn V} {a b : V} {U : Finset V} {R : TripleSystemOn V}
    (w : LocalizedTwoAwayRemainderFiber V (absorberErdosForbiddenConfigurationsOn q B) T a b U R) :
    LocalizedRootedThreatRemainderFiber V q B a b U (insert T R) :=
  ⟨localizedTwoAwayToRooted w.1, by rw [localizedTwoAwayToRooted_remainder, w.2]⟩

theorem localizedTwoAwayFiberToRooted_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {T : TripleOn V} {a b : V} {U : Finset V} {R : TripleSystemOn V} :
    Function.Injective (localizedTwoAwayFiberToRooted :
      LocalizedTwoAwayRemainderFiber V (absorberErdosForbiddenConfigurationsOn q B) T a b U R →
        LocalizedRootedThreatRemainderFiber V q B a b U (insert T R)) := by
  intro w z h
  apply Subtype.ext
  exact localizedTwoAwayToRooted_injective (congrArg Subtype.val h)

theorem card_localizedTwoAwayRemainderFiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {T : TripleOn V} {a b : V} (hab : a ≠ b) (R : TripleSystemOn V)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B) :
    Fintype.card (LocalizedTwoAwayRemainderFiber V
      (absorberErdosForbiddenConfigurationsOn q B) T a b U R) ≤ 45 * (R.card + 1) + 28 := by
  calc
    _ ≤ Fintype.card (LocalizedRootedThreatRemainderFiber V q B a b U (insert T R)) :=
      Fintype.card_le_of_injective localizedTwoAwayFiberToRooted localizedTwoAwayFiberToRooted_injective
    _ ≤ 45 * (insert T R).card + 28 := card_localizedRootedThreatRemainderFiber_le hab _ hsep hrootLocal
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 45 (card_insert_le T R)) 28

end

end Erdos207

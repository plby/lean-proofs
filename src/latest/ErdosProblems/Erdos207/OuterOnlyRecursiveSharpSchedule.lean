/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpRecursiveSchedules
import ErdosProblems.Erdos207.OuterOnlySharpInitialActive

/-!
# Recursive sharp schedules for the outer-only phase
-/

namespace Erdos207

open Finset

noncomputable section

def outerSharpLowerFormula
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (_X : Finset V) (i d _u : ℕ) : ℕ :=
  (Nat.choose (Fintype.card V) 2 - 3 * i -
      (graphEdges H).card) * d / 3

def outerSharpUpperFormula
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (_X : Finset V) (i _d u : ℕ) : ℕ :=
  ((Nat.choose (Fintype.card V) 2 - 3 * i -
      (graphEdges H).card) * u) / 3

abbrev outerSharpEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ) :=
  sharpPairEnvelope upper₀ lower₀ buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)

abbrev outerSharpLowerSchedule
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ) :=
  sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)

abbrev outerSharpUpperSchedule
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ) :=
  sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)

abbrev outerSharpLowerAvailability
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ) :=
  sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)

abbrev outerSharpUpperAvailability
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ) :=
  sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)

lemma outerSharpLowerAvailability_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ) :
    outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i =
      (Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges H).card) *
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i / 3 := rfl

lemma outerSharpUpperAvailability_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc i : ℕ) :
    outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i =
      ((Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges H).card) *
        outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) / 3 := rfl

/-- The recursive outer-only schedules satisfy the complete sharp active
predicate at time zero.  The only availability input is the lower cutoff:
the two scheduled availability comparisons are definitional, and the
initial pair floor/cap follow from floor/ceiling monotonicity. -/
theorem timedSharpScheduledAggregatePairBandActive_outerSharp_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc m Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {Habs G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (hq : 4 ≤ q)
    (hA2 : HasAbsorberLocalization q Mloc Habs X B)
    (htri : ConsistsOfTriangles G A)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hfloor : HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hKpair : pairTwoAwayThreatExtensionCoefficient q B ≤ Kpair)
    (hKglobal :
      twoAwayThreatExtensionCoefficient q Mloc Habs X B ≤ Kglobal)
    (hKinc : initialAggregatePairTwoAwayCoefficient q B *
      Fintype.card V ≤ Kinc)
    (hOuterDelta : (univ \ U).card ≤ Delta)
    (hdelta : delta ≤ m + 1)
    (hI : Fintype.card (TripleOn V) *
      twoAwayThreatExtensionCoefficient q Mloc Habs X B ≤ I)
    (buffer : ℝ) (hbuffer : 0 ≤ buffer)
    (hDcutPos : 0 < Dcut)
    (hDcut : Dcut ≤
      outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
        ((univ \ U).card : ℝ) ((m + 1 : ℕ) : ℝ) buffer Kinc 0) :
    timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      Kpair Kglobal Kinc Delta delta I Dcut
      (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
        ((univ \ U).card : ℝ) ((m + 1 : ℕ) : ℝ) buffer Kinc)
      (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
        ((univ \ U).card : ℝ) ((m + 1 : ℕ) : ℝ) buffer Kinc)
      (outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
        ((univ \ U).card : ℝ) ((m + 1 : ℕ) : ℝ) buffer Kinc)
      (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
        ((univ \ U).card : ℝ) ((m + 1 : ℕ) : ℝ) buffer Kinc) 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)) := by
  let Hout := (internalOuterGraph G U)ᶜ
  let upper₀ := (univ \ U).card
  let lower₀ := m + 1
  have hd : outerSharpLowerSchedule Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc 0 ≤ m + 1 := by
    apply nonnegativeNatFloor_le_nat_of_le
    simp only [sharpPairEnvelope_zero, lower₀]
    linarith
  have hu : (univ \ U).card ≤ outerSharpUpperSchedule Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc 0 := by
    have hreal : (upper₀ : ℝ) ≤
        (outerSharpUpperSchedule Hout U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc 0 : ℕ) := by
      calc
        (upper₀ : ℝ) ≤ (upper₀ : ℝ) + buffer := by linarith
        _ ≤ (nonnegativeNatCeil ((upper₀ : ℝ) + buffer) : ℕ) :=
          le_nonnegativeNatCeil
        _ = (outerSharpUpperSchedule Hout U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc 0 : ℕ) := by
          rfl
    exact_mod_cast hreal
  have hDcutRaw : Dcut ≤
      (Nat.choose (Fintype.card V) 2 -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * (m + 1) / 3 := by
    apply hDcut.trans
    rw [outerSharpLowerAvailability_eq]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hd)
  apply timedSharpScheduledAggregatePairBandActive_outerOnly_initial_sharp
    (H := Habs) (G := G) (X := X) (U := U) (B := B) (A := A)
    hq hA2 htri houtside hfloor hKpair hKglobal hKinc hOuterDelta hdelta hI
    (outerSharpLowerAvailability Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
    (outerSharpLowerSchedule Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
    (outerSharpUpperAvailability Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
    (outerSharpUpperSchedule Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
    hDcutPos
  · exact hDcutRaw
  · exact le_rfl
  · exact hd
  · exact hu
  · exact le_rfl

/-- A compact scalar certificate for positivity of all recursive schedules.
Only a uniform lower bound on the surviving eligible pair count and one
linear buffer inequality remain to be checked in applications. -/
theorem outerSharpRecursive_schedule_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (buffer : ℝ) (Kinc fuel : ℕ)
    (Umax dmin Rmin Dcut : ℕ)
    (hupper : nonnegativeNatCeil ((upper₀ : ℝ) + buffer) ≤ Umax)
    (hpairCount : ∀ i, i ≤ fuel → Rmin ≤
      Nat.choose (Fintype.card V) 2 - 3 * i -
        (graphEdges H).card)
    (hDcut : Dcut ≤ Rmin * dmin / 3)
    (hgap : Umax < Dcut)
    (hbuffer : ∀ i, i ≤ fuel →
      (dmin : ℝ) + buffer + (i : ℝ) *
        sharpScheduledPairLowerRate Dcut Umax Kinc ≤ (lower₀ : ℝ)) :
    ∀ i, i ≤ fuel →
      dmin ≤ outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i ∧
      outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i ≤ Umax ∧
      Dcut ≤ outerSharpLowerAvailability H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i ∧
      0 ≤ (outerSharpEnvelope H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i).2 - buffer := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have hu : outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i ≤ Umax :=
        (sharpRecursiveUpperSchedule_le_initial
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
          (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i).trans hupper
      have hrate : ∀ j, j < i →
          sharpScheduledPairLowerRate
            (outerSharpLowerAvailability H X (upper₀ : ℝ) (lower₀ : ℝ)
              buffer Kinc j)
            (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ)
              buffer Kinc j) Kinc ≤
            sharpScheduledPairLowerRate Dcut Umax Kinc := by
        intro j hj
        have hjfuel : j ≤ fuel := (Nat.le_of_lt hj).trans hi
        have hjbounds := ih j hj hjfuel
        exact sharpScheduledPairLowerRate_mono hjbounds.2.2.1 hjbounds.2.1 hgap
      have hd : dmin ≤ outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
        exact le_sharpRecursiveLowerSchedule_of_sub_mul
          (upper₀ : ℝ) (lower₀ : ℝ) buffer
          (sharpScheduledPairLowerRate Dcut Umax Kinc) Kinc dmin i
          (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)
          hrate (hbuffer i hi)
      have hD : Dcut ≤ outerSharpLowerAvailability H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
        rw [outerSharpLowerAvailability_eq]
        exact hDcut.trans (Nat.div_le_div_right <|
          Nat.mul_le_mul (hpairCount i hi) hd)
      have henv := sharpPairEnvelope_lower_ge_sub_mul
        (upper₀ : ℝ) (lower₀ : ℝ) buffer
        (sharpScheduledPairLowerRate Dcut Umax Kinc) Kinc
        (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i hrate
      have hnonneg : 0 ≤
          (outerSharpEnvelope H X (upper₀ : ℝ) (lower₀ : ℝ)
            buffer Kinc i).2 - buffer := by
        have hb := hbuffer i hi
        linarith
      exact ⟨hd, hu, hD, hnonneg⟩

/-- The recursive construction discharges all four target-envelope clauses
of sharp first passage. -/
theorem outerSharpRecursive_target_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ : GreedyStateOn V}
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ : ℕ) (buffer : ℝ) (Kinc fuel Delta delta : ℕ)
    (hcap₀ : HasAvailablePairCutoff upper₀ S₀)
    (hfloor₀ : HasAvailablePairFloor lower₀ S₀)
    (hnonneg : ∀ i, i ≤ fuel →
      0 ≤ (outerSharpEnvelope H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i).2 - buffer)
    (huDelta : ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤ Delta)
    (hdelta : ∀ i, i ≤ fuel →
      delta ≤ outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) :
    (∀ P : PairOn V, ∀ i, i ≤ fuel →
      sharpScheduledPairUpperTarget S₀
          (outerSharpUpperAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          P i + buffer ≤ ((Delta + 1 : ℕ) : ℝ)) ∧
    (∀ P : PairOn V, ∀ i, i ≤ fuel → PairAlive P.1 S₀ →
      (delta : ℝ) ≤
        sharpScheduledPairLowerTarget S₀
          (outerSharpLowerAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          Kinc P i - buffer) ∧
    (∀ P : PairOn V, ∀ i, i ≤ fuel →
      sharpScheduledPairUpperTarget S₀
          (outerSharpUpperAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          P i + buffer ≤
        ((outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i + 1 : ℕ) : ℝ)) ∧
    (∀ P : PairOn V, ∀ i, i ≤ fuel → PairAlive P.1 S₀ →
      (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℝ) ≤
        sharpScheduledPairLowerTarget S₀
          (outerSharpLowerAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          Kinc P i - buffer) := by
  have hupperInitial : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ ≤ (upper₀ : ℝ) := by
    intro P
    rw [fixedPairAvailableCountReal_eq_current (S₀ := S₀) (S := S₀)
      (P := P.1) Subset.rfl]
    exact_mod_cast hcap₀ P.1 P.2
  have hlowerInitial : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (lower₀ : ℝ) ≤ fixedPairAvailableCountReal S₀ P.1 S₀ := by
    intro P halive
    rw [fixedPairAvailableCountReal_eq_current (S₀ := S₀) (S := S₀)
      (P := P.1) Subset.rfl]
    exact_mod_cast hfloor₀ P.1 P.2 halive
  have hupper : ∀ P : PairOn V, ∀ i, i ≤ fuel →
      sharpScheduledPairUpperTarget S₀
          (outerSharpUpperAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          P i + buffer ≤
        (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℝ) := by
    intro P i _hi
    exact sharpScheduledPairUpperTarget_add_buffer_le_recursiveUpper
      S₀ P (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
        (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i
        (hupperInitial P)
  have hlower : ∀ P : PairOn V, ∀ i, i ≤ fuel → PairAlive P.1 S₀ →
      (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℝ) ≤
        sharpScheduledPairLowerTarget S₀
          (outerSharpLowerAvailability H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          (outerSharpUpperSchedule H X (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
          Kinc P i - buffer := by
    intro P i hi halive
    exact recursiveLower_le_sharpScheduledPairLowerTarget_sub_buffer
      S₀ P (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
        (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i
        (hlowerInitial P halive) (hnonneg i hi)
  refine ⟨?_, ?_, ?_, hlower⟩
  · intro P i hi
    exact (hupper P i hi).trans (by
      have hnat := (huDelta i hi).trans (Nat.le_succ Delta)
      exact_mod_cast hnat)
  · intro P i hi halive
    have hdreal : (delta : ℝ) ≤
        (outerSharpLowerSchedule H X (upper₀ : ℝ) (lower₀ : ℝ)
          buffer Kinc i : ℝ) := by
      exact_mod_cast hdelta i hi
    exact hdreal.trans (hlower P i hi halive)
  · intro P i hi
    exact (hupper P i hi).trans (by norm_num)

end

end Erdos207

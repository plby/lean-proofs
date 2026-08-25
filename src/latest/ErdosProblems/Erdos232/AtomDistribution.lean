/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase
import Batteries.Data.Fin.OfBits

open MeasureTheory Set

namespace Erdos232

abbrev Assignment := Fin 23 → Bool

/-- Encode a Boolean assignment as the corresponding certificate atom. -/
def assignmentAtom (v : Assignment) : AtomIndex := Fin.ofBits v

theorem measurable_assignmentAtom : Measurable assignmentAtom :=
  measurable_of_countable _

/-- The event that every bit selected by `m` is true. -/
def maskEvent {Ω : Type*} (X : Ω → Assignment) (m : Nat) : Set Ω :=
  {ω | ∀ i : Fin 23, m.testBit i → X ω i = true}

theorem natMaskSubset_ofBits_iff (m : Nat) (hm : m < 2 ^ 23) (v : Assignment) :
    natMaskSubset m (Nat.ofBits v) = true ↔ ∀ i : Fin 23, m.testBit i → v i = true := by
  simp only [natMaskSubset, beq_iff_eq]
  constructor
  · intro hand i hi
    have ht := congrArg (fun z : Nat ↦ z.testBit i.val) hand
    simpa [Nat.testBit_and, hi, Nat.testBit_ofBits_lt] using ht
  · intro hv
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 23
    · rw [Nat.testBit_ofBits_lt v i hi]
      by_cases hb : m.testBit i
      · simpa [hb] using hv ⟨i, hi⟩ hb
      · simp [hb]
    · have hi23 : 23 ≤ i := Nat.le_of_not_gt hi
      have hpow : 2 ^ 23 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi23
      have hm' : m < 2 ^ i := lt_of_lt_of_le hm hpow
      rw [Nat.testBit_ofBits_ge v i hi23, Nat.testBit_lt_two_pow hm']
      rfl

theorem measurable_maskEvent {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Assignment} (hX : Measurable X) (m : Nat) :
    MeasurableSet (maskEvent X m) := by
  have hcoord (i : Fin 23) : Measurable fun ω ↦ X ω i :=
    (measurable_pi_apply i).comp hX
  rw [show maskEvent X m = ⋂ i : Fin 23,
      {ω | m.testBit i → X ω i = true} by
    ext ω
    simp [maskEvent]]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : m.testBit i
  · rw [show {ω | m.testBit i → X ω i = true} =
        (fun ω ↦ X ω i) ⁻¹' {true} by
      ext ω
      simp [hi]]
    exact (hcoord i) (measurableSet_singleton true)
  · simp [hi]

/-- The probability mass of a Boolean atom, as the real measure of its fiber. -/
noncomputable def atomMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Assignment) (s : AtomIndex) : ℝ :=
  μ.real ((assignmentAtom ∘ X) ⁻¹' {s})

theorem atomMass_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Assignment) (s : AtomIndex) :
    0 ≤ atomMass μ X s := measureReal_nonneg

theorem atomMass_total {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Assignment)
    (hX : Measurable X) :
    ∑ s, atomMass μ X s = 1 := by
  have hA : Measurable (assignmentAtom ∘ X) := measurable_assignmentAtom.comp hX
  rw [show (∑ s, atomMass μ X s) =
      μ.real ((assignmentAtom ∘ X) ⁻¹' (Set.univ : Set AtomIndex)) by
    simpa [atomMass] using
      sum_measureReal_preimage_singleton (μ := μ) (Finset.univ : Finset AtomIndex)
        (fun s _ ↦ hA (measurableSet_singleton s))
        (fun _ _ ↦ measure_ne_top μ _)]
  simp

/-- A mask marginal of the atom distribution is exactly the measure of the corresponding
multi-point occupancy event. -/
theorem maskMass_atomMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Assignment) (hX : Measurable X)
    (m : Nat) (hm : m < 2 ^ 23) :
    maskMass (atomMass μ X) m = μ.real (maskEvent X m) := by
  let A : Ω → AtomIndex := assignmentAtom ∘ X
  let good : Finset AtomIndex := Finset.univ.filter fun s ↦ natMaskSubset m s.val
  have hA : Measurable A := measurable_assignmentAtom.comp hX
  have hsum : (∑ s ∈ good, μ.real (A ⁻¹' {s})) =
      μ.real (A ⁻¹' (good : Set AtomIndex)) := by
    exact sum_measureReal_preimage_singleton (μ := μ) good
      (fun s _ ↦ hA (measurableSet_singleton s))
      (fun _ _ ↦ measure_ne_top μ _)
  rw [maskMass]
  have hleft : (∑ s, if natMaskSubset m s.val then atomMass μ X s else 0) =
      ∑ s ∈ good, μ.real (A ⁻¹' {s}) := by
    simp only [good, Finset.sum_filter, atomMass, A, Bool.decide_coe]
  rw [hleft, hsum]
  apply congrArg μ.real
  ext ω
  change ((assignmentAtom ∘ X) ω ∈ good) ↔
    ∀ i : Fin 23, m.testBit i → X ω i = true
  simpa [good, A, assignmentAtom] using natMaskSubset_ofBits_iff m hm (X ω)

end Erdos232

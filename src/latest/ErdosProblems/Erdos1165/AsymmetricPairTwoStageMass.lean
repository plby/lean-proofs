/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AsymmetricPairPartitionUpper

/-!
# Two-stage mass summation for the asymmetric far-pair decomposition

The source proof of HLOZ (A.16) first fixes the complete retained history of
the first point and then sums the possible post-separation radial words of
the second point.  This file records exactly that summation.  It deliberately
does not assume the final pair estimate: every refined atom has an exact
retained-atom mass times a radial-word weight, and only the sum of those
weights is bounded.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricPairTwoStageMass

open MarkedBridgeFactorization

noncomputable section

/-! ## Fixing one retained complementary word -/

/-- Restrict a complementary-skeleton atom to one literal retained word.
The bridge families and their insertion order are unchanged. -/
def fixComplement
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) :
    ComplementarySkeletonAtom m Unit Bridge where
  complementWord := fun _ ↦ atom.complementWord complement
  bridgeWord := atom.bridgeWord
  assemble := fun code ↦ atom.assemble (complement, code.2)
  prefixFree_assemble := by
    intro a b hab
    exact atom.prefixFree_assemble (fun h ↦ hab (by
      cases a with
      | mk _ ab =>
        cases b with
        | mk _ bb =>
          simp only [Prod.mk.injEq, true_and] at h ⊢
          exact h))
  prefixFree_bridge := atom.prefixFree_bridge
  length_assemble := by
    intro code
    simpa only using atom.length_assemble (complement, code.2)

@[simp] theorem fixComplement_complementWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) (u : Unit) :
    (fixComplement atom complement).complementWord u =
      atom.complementWord complement := rfl

@[simp] theorem fixComplement_bridgeWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) (j : Fin m) (bridge : Bridge j) :
    (fixComplement atom complement).bridgeWord j bridge =
      atom.bridgeWord j bridge := rfl

@[simp] theorem fixComplement_kernel
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) (j : Fin m) :
    (fixComplement atom complement).kernel j = atom.kernel j := rfl

@[simp] theorem fixComplement_weight
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) :
    (fixComplement atom complement).weight =
      stoppedWordMass (atom.complementWord complement) := by
  unfold ComplementarySkeletonAtom.weight fixComplement
  simp

/-- Exact conditional row factorization: after fixing one retained word,
the insertion-event mass is the product of its bridge kernels times the
mass of the retained prefix cylinder. -/
theorem fairSteps_fixComplement_event_eq_prod_mul_retainedCylinder
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) :
    fairSteps (fixComplement atom complement).event =
      (∏ j, atom.kernel j) *
        fairSteps (stoppedWordCylinder (atom.complementWord complement)) := by
  rw [fairSteps_event_eq_weight_mul_prod_kernel,
    fixComplement_weight, fairSteps_stoppedWordCylinder]
  simp only [fixComplement_kernel]
  exact mul_comm _ _

/-- The retained atom attached to one complementary code. -/
def fixedComplementRetainedAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) : Set StepPath :=
  stoppedWordCylinder (atom.complementWord complement)

/-- The insertion row attached to one complementary code. -/
def fixedComplementTailAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) : Set StepPath :=
  stoppedWordEvent
    (fun code : Unit × ((j : Fin m) → Bridge j) ↦
      atom.assemble (complement, code.2))

/-- The union of all fixed-complement rows is exactly the original
insertion event. -/
theorem iUnion_fixedComplementTailAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge) :
    (⋃ complement, fixedComplementTailAtom atom complement) = atom.event := by
  unfold fixedComplementTailAtom ComplementarySkeletonAtom.event
  unfold stoppedWordEvent
  ext omega
  simp only [mem_iUnion]
  constructor
  · rintro ⟨complement, code, hcode⟩
    exact ⟨(complement, code.2), hcode⟩
  · rintro ⟨code, hcode⟩
    exact ⟨code.1, (Unit.unit, code.2), hcode⟩

theorem measurableSet_fixedComplementRetainedAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) :
    MeasurableSet (fixedComplementRetainedAtom atom complement) :=
  measurableSet_stoppedWordCylinder _

theorem pairwise_disjoint_fixedComplementRetainedAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (hfree : PrefixFree atom.complementWord) :
    Pairwise fun c d : Complement ↦
      Disjoint (fixedComplementRetainedAtom atom c)
        (fixedComplementRetainedAtom atom d) :=
  hfree

/-- Fixed-complement rows provide exactly the atom-mass identity required
by `fairSteps_real_le_radialTail_mul_retained_of_atom_weights`. -/
theorem fairSteps_fixedComplementTailAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complement : Complement) :
    fairSteps (fixedComplementTailAtom atom complement) =
      (∏ j, atom.kernel j) *
        fairSteps (fixedComplementRetainedAtom atom complement) :=
  fairSteps_fixComplement_event_eq_prod_mul_retainedCylinder atom complement

/-- Restricting the admissible radial words by an extra retained-history
compatibility predicate can only decrease their total ENNReal weight.  This
is the sound way to handle the split level: compatibility is imposed on the
bridge subtype rather than asserted for every replacement word. -/
theorem tsum_subtype_le_tsum
    {Code : Type*} (admissible : Code → Prop)
    (weight : Code → ℝ≥0∞) :
    (∑' code : {code // admissible code}, weight code.1) ≤
      ∑' code, weight code := by
  exact ENNReal.tsum_comp_le_tsum_of_injective
    Subtype.coe_injective weight

/-- Convert a finite literal ENNReal radial-word sum bounded after `toReal`
back to the `ofReal` inequality consumed by the two-stage constructor. -/
theorem ennreal_le_of_toReal_le
    {mass : ℝ≥0∞} {bound : ℝ}
    (hmass : mass ≠ ⊤) (hbound0 : 0 ≤ bound)
    (hbound : mass.toReal ≤ bound) :
    mass ≤ ENNReal.ofReal bound := by
  apply (ENNReal.toReal_le_toReal hmass ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hbound0] using hbound

/-- Sum an explicit family of conditional post-separation words over a
disjoint retained stopped-skeleton partition.  This is the measure-theoretic
form of the asymmetric A.16 mixture. -/
theorem fairSteps_real_le_radialTail_mul_retained_of_atom_weights
    {RetainedCode : Type*} [Countable RetainedCode]
    (TailCode : RetainedCode → Type*)
    [∀ r, Countable (TailCode r)]
    (successful retained : Set StepPath)
    (retainedAtom : RetainedCode → Set StepPath)
    (tailAtom : ∀ r, TailCode r → Set StepPath)
    (tailWeight : ∀ r, TailCode r → ℝ≥0∞)
    (radialTail : ℝ)
    (hradial0 : 0 ≤ radialTail)
    (hsuccessful : successful ⊆ ⋃ r, ⋃ t, tailAtom r t)
    (hretained : retained = ⋃ r, retainedAtom r)
    (hretainedMeasurable : ∀ r, MeasurableSet (retainedAtom r))
    (hretainedDisjoint : Pairwise fun r s ↦
      Disjoint (retainedAtom r) (retainedAtom s))
    (hatomMass : ∀ r t,
      fairSteps (tailAtom r t) =
        tailWeight r t * fairSteps (retainedAtom r))
    (htailWeight : ∀ r, ∑' t, tailWeight r t ≤
      ENNReal.ofReal radialTail) :
    fairSteps.real successful ≤
      radialTail * fairSteps.real retained := by
  have hENN : fairSteps successful ≤
      ENNReal.ofReal radialTail * fairSteps retained := by
    calc
      fairSteps successful ≤ fairSteps (⋃ r, ⋃ t, tailAtom r t) :=
        measure_mono hsuccessful
      _ ≤ ∑' r, fairSteps (⋃ t, tailAtom r t) := measure_iUnion_le _
      _ ≤ ∑' r, ∑' t, fairSteps (tailAtom r t) :=
        ENNReal.tsum_le_tsum fun r ↦ measure_iUnion_le _
      _ = ∑' r, ∑' t,
          tailWeight r t * fairSteps (retainedAtom r) := by
        apply tsum_congr
        intro r
        apply tsum_congr
        intro t
        exact hatomMass r t
      _ = ∑' r, (∑' t, tailWeight r t) *
          fairSteps (retainedAtom r) := by
        apply tsum_congr
        intro r
        exact ENNReal.tsum_mul_right
      _ ≤ ∑' r, ENNReal.ofReal radialTail *
          fairSteps (retainedAtom r) :=
        ENNReal.tsum_le_tsum fun r ↦
          mul_le_mul (htailWeight r) le_rfl bot_le bot_le
      _ = ENNReal.ofReal radialTail *
          ∑' r, fairSteps (retainedAtom r) :=
        ENNReal.tsum_mul_left
      _ = ENNReal.ofReal radialTail * fairSteps retained := by
        rw [hretained, measure_iUnion hretainedDisjoint hretainedMeasurable]
  have hright : ENNReal.ofReal radialTail * fairSteps retained ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hright hENN
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hradial0,
    measureReal_def] using hreal

/-- A complementary-skeleton atom itself supplies the complete retained-row
partition once its retained word family is prefix-free.  This is the direct
adapter used by the asymmetric split-level splice: bridge compatibility is
already encoded in `atom`, and only its product-kernel row bound remains. -/
theorem fairSteps_real_event_le_radialTail_mul_retainedWordEvent
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [Countable Complement] [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (hcomplementFree : PrefixFree atom.complementWord)
    (radialTail : ℝ) (hradial0 : 0 ≤ radialTail)
    (hrow : ∏ j, atom.kernel j ≤ ENNReal.ofReal radialTail) :
    fairSteps.real atom.event ≤ radialTail *
      fairSteps.real (stoppedWordEvent atom.complementWord) := by
  apply fairSteps_real_le_radialTail_mul_retained_of_atom_weights
    (fun _ : Complement ↦ Unit) atom.event
    (stoppedWordEvent atom.complementWord)
    (fixedComplementRetainedAtom atom)
    (fun c _ ↦ fixedComplementTailAtom atom c)
    (fun _ _ ↦ ∏ j, atom.kernel j)
    radialTail hradial0
  · intro omega homega
    have hsingle : omega ∈
        ⋃ complement, fixedComplementTailAtom atom complement := by
      rw [iUnion_fixedComplementTailAtom atom]
      exact homega
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hsingle
    exact Set.mem_iUnion.mpr ⟨c,
      Set.mem_iUnion.mpr ⟨Unit.unit, hc⟩⟩
  · rfl
  · exact measurableSet_fixedComplementRetainedAtom atom
  · exact pairwise_disjoint_fixedComplementRetainedAtom atom hcomplementFree
  · intro c _
    exact fairSteps_fixedComplementTailAtom atom c
  · intro c
    simpa using hrow

end

end Erdos1165.AsymmetricPairTwoStageMass

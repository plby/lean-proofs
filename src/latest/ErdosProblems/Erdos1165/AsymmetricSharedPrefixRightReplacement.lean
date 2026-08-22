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

import ErdosProblems.Erdos1165.SharedPrefixPairFactorization

/-!
# Retaining the left branch of a shared-prefix pair atom

The terminal pair extractor naturally presents the deleted intervals as a
shared-prefix atom with a left and a right bridge family.  The asymmetric
argument must not sum over fresh left bridges: the complete left tuple is
part of the retained `Γ_x` history.  This file fixes that tuple literally
and leaves only the right tuple variable.

This is a finite-word operation.  In particular it does not replace both
branches and then appeal to a probability comparison.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricSharedPrefixRightReplacement

open MarkedBridgeFactorization SharedPrefixPairFactorization

noncomputable section

/-- Fix every left bridge of a shared-prefix pair atom to its actual source
word.  The singleton `Unit` coordinates are deliberately retained in the
type: this records their word lengths in the exact stopped-word mass while
making it impossible to choose a different left bridge. -/
def fixLeft
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) :
    SharedPrefixPairAtom mLeft mRight Common (fun _ ↦ Unit) RightBridge where
  commonWord := atom.commonWord
  leftBridgeWord := fun i _ ↦ atom.leftBridgeWord i (source i)
  rightBridgeWord := atom.rightBridgeWord
  assemble := fun code ↦ atom.assemble (code.1, (source, code.2.2))
  prefixFree_assemble := by
    intro a b hab
    apply atom.prefixFree_assemble
    intro h
    apply hab
    cases a with
    | mk ac abranches =>
      cases b with
      | mk bc bbranches =>
        simp only [Prod.mk.injEq] at h ⊢
        refine ⟨h.1, ?_⟩
        apply Prod.ext
        · funext i
          exact Subsingleton.elim _ _
        · exact h.2.2
  prefixFree_leftBridge := by
    intro i a b hab
    exact (hab (Subsingleton.elim _ _)).elim
  prefixFree_rightBridge := atom.prefixFree_rightBridge
  length_assemble := by
    intro code
    rw [atom.length_assemble]

@[simp] theorem fixLeft_commonWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) (c : Common) :
    (fixLeft atom source).commonWord c = atom.commonWord c := rfl

@[simp] theorem fixLeft_leftBridgeWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i)
    (i : Fin mLeft) (u : Unit) :
    (fixLeft atom source).leftBridgeWord i u =
      atom.leftBridgeWord i (source i) := rfl

@[simp] theorem fixLeft_rightBridgeWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i)
    (j : Fin mRight) (b : RightBridge j) :
    (fixLeft atom source).rightBridgeWord j b =
      atom.rightBridgeWord j b := rfl

@[simp] theorem fixLeft_assemble
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i)
    (code : Common ×
      (((i : Fin mLeft) → Unit) ×
        ((j : Fin mRight) → RightBridge j))) :
    (fixLeft atom source).assemble code =
      atom.assemble (code.1, (source, code.2.2)) := rfl

@[simp] theorem fixLeft_commonWeight
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) :
    (fixLeft atom source).commonWeight = atom.commonWeight := rfl

@[simp] theorem fixLeft_leftKernel
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) (i : Fin mLeft) :
    (fixLeft atom source).leftKernel i =
      stoppedWordMass (atom.leftBridgeWord i (source i)) := by
  unfold SharedPrefixPairAtom.leftKernel fixLeft
  simp

@[simp] theorem fixLeft_rightKernel
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) (j : Fin mRight) :
    (fixLeft atom source).rightKernel j = atom.rightKernel j := rfl

/-! ## Restricting only the right bridge family -/

/-- Replace the right bridge code at every coordinate by a subtype-like
family which injects into the original right bridge family.  The assembled
word and the left bridge family are inherited literally through erasure.

This is the finite-word operation used to expose right visit marks after
the left branch has already been fixed. -/
def markRight
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j)) :
    SharedPrefixPairAtom mLeft mRight Common LeftBridge MarkedRightBridge where
  commonWord := atom.commonWord
  leftBridgeWord := atom.leftBridgeWord
  rightBridgeWord := fun j b ↦ atom.rightBridgeWord j (erase j b)
  assemble := fun code ↦
    atom.assemble (code.1, (code.2.1, fun j ↦ erase j (code.2.2 j)))
  prefixFree_assemble := by
    intro a b hab
    apply atom.prefixFree_assemble
    intro h
    apply hab
    have hc := congrArg (fun z ↦ z.1) h
    have hbranches := congrArg (fun z ↦ z.2) h
    have hleft := congrArg (fun z ↦ z.1) hbranches
    have hright := congrArg (fun z ↦ z.2) hbranches
    apply Prod.ext
    · exact hc
    · apply Prod.ext
      · exact hleft
      · funext j
        exact herase j (congrFun hright j)
  prefixFree_leftBridge := atom.prefixFree_leftBridge
  prefixFree_rightBridge := by
    intro j a b hab
    exact atom.prefixFree_rightBridge j (fun h ↦ hab (herase j h))
  length_assemble := by
    intro code
    rw [atom.length_assemble]

@[simp] theorem markRight_commonWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j)) (c : Common) :
    (markRight atom erase herase).commonWord c = atom.commonWord c := rfl

@[simp] theorem markRight_leftBridgeWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j))
    (i : Fin mLeft) (b : LeftBridge i) :
    (markRight atom erase herase).leftBridgeWord i b =
      atom.leftBridgeWord i b := rfl

@[simp] theorem markRight_rightBridgeWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j))
    (j : Fin mRight) (b : MarkedRightBridge j) :
    (markRight atom erase herase).rightBridgeWord j b =
      atom.rightBridgeWord j (erase j b) := rfl

@[simp] theorem markRight_commonWeight
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j)) :
    (markRight atom erase herase).commonWeight = atom.commonWeight := rfl

@[simp] theorem markRight_leftKernel
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge MarkedRightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (erase : (j : Fin mRight) → MarkedRightBridge j → RightBridge j)
    (herase : ∀ j, Function.Injective (erase j)) (i : Fin mLeft) :
    (markRight atom erase herase).leftKernel i = atom.leftKernel i := rfl

/-! ## Absorbing the fixed left tuple into terminal complement data -/

/-- Regard the common code together with the complete left bridge tuple as
the complement of a one-sided complementary-skeleton atom.  The assembled
word is unchanged; the synthetic complement word records exactly the total
common-plus-left length, which is all that the stopped-word mass
factorization uses. -/
def absorbLeft
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    ComplementarySkeletonAtom mRight
      (Common × ((i : Fin mLeft) → LeftBridge i)) RightBridge where
  complementWord := fun code ↦
    ⟨(atom.commonWord code.1).1 +
        ∑ i, (atom.leftBridgeWord i (code.2 i)).1,
      fun _ ↦ default⟩
  bridgeWord := atom.rightBridgeWord
  assemble := fun code ↦
    atom.assemble (code.1.1, (code.1.2, code.2))
  prefixFree_assemble := by
    intro a b hab
    apply atom.prefixFree_assemble
    intro h
    apply hab
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z ↦ z.1) h
      · exact congrArg (fun z ↦ z.2.1) h
    · exact congrArg (fun z ↦ z.2.2) h
  prefixFree_bridge := atom.prefixFree_rightBridge
  length_assemble := by
    intro code
    simpa only using atom.length_assemble
      (code.1.1, (code.1.2, code.2))

@[simp] theorem absorbLeft_bridgeWord
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (j : Fin mRight) (b : RightBridge j) :
    (absorbLeft atom).bridgeWord j b = atom.rightBridgeWord j b := rfl

@[simp] theorem absorbLeft_kernel
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (j : Fin mRight) :
    (absorbLeft atom).kernel j = atom.rightKernel j := rfl

@[simp] theorem absorbLeft_event
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    (absorbLeft atom).event = atom.event := by
  unfold ComplementarySkeletonAtom.event SharedPrefixPairAtom.event
    stoppedWordEvent
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨code, hcode⟩
    exact ⟨(code.1.1, (code.1.2, code.2)), hcode⟩
  · rintro ⟨code, hcode⟩
    exact ⟨((code.1, code.2.1), code.2.2), hcode⟩

/-- The literal source cylinder is one member of the asymmetric right-only
replacement event. -/
theorem stoppedWordCylinder_source_subset_fixLeft_event
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (sourceLeft : (i : Fin mLeft) → LeftBridge i)
    (sourceRight : (j : Fin mRight) → RightBridge j)
    (common : Common) :
    stoppedWordCylinder
        (atom.assemble (common, (sourceLeft, sourceRight))) ⊆
      (fixLeft atom sourceLeft).event := by
  intro omega homega
  unfold SharedPrefixPairAtom.event stoppedWordEvent
  apply Set.mem_iUnion.mpr
  exact ⟨(common, (fun _ ↦ Unit.unit, sourceRight)), homega⟩

/-- Exact mass of the asymmetric terminal family.  The product of actual
left-word masses is retained literally; only the right kernels are summed. -/
theorem fairSteps_fixLeft_event_eq
    {mLeft mRight : ℕ} {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    [Countable Common] [∀ j, Countable (RightBridge j)]
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (source : (i : Fin mLeft) → LeftBridge i) :
    fairSteps (fixLeft atom source).event =
      atom.commonWeight *
        ((∏ i, stoppedWordMass (atom.leftBridgeWord i (source i))) *
          ∏ j, atom.rightKernel j) := by
  simpa only [fixLeft_commonWeight, fixLeft_leftKernel,
    fixLeft_rightKernel] using
      fairSteps_event_eq_commonWeight_mul_pairKernels (fixLeft atom source)

end

end Erdos1165.AsymmetricSharedPrefixRightReplacement

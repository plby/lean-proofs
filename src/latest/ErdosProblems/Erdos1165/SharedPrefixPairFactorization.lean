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

import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# Common-prefix factorization for two stopped bridge families

In the two-point appendix argument, the retained stopped skeleton common to
the two marked families must be charged only once.  The omitted bridge
coordinates then split into a left family and a right family.  This file gives
a literal finite-word insertion interface for exactly that situation.

A code has type `Common × (LeftTuple × RightTuple)`: the common retained
code appears once, while the two dependent finite tuples carry the separate
bridge words.  Prefix-free additivity and two applications of Tonelli give
the exact mass as

`commonWeight * (product leftKernel * product rightKernel)`.

As in `MarkedBridgeFactorization`, every premise is pathwise: an assembly map,
prefix-freeness of its exact stopped-prefix cylinders, and the exact word
length identity.  No probability identity, conditional independence, pair
estimate, or analytic bound is assumed.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.SharedPrefixPairFactorization

open Hitting
open MarkedBridgeFactorization
open TerminalSequentialVisitLaw

noncomputable section

/-! ## Literal common-prefix/two-branch insertion data -/

/-- Prefix-free insertion data for a common retained stopped-word code and
two separate finite families of omitted bridge words.

The type of `assemble` records the crucial combinatorial fact: the common
retained code occurs once, alongside independent choices of all left and all
right bridge codes. -/
structure SharedPrefixPairAtom (mLeft mRight : ℕ)
    (Common : Type*)
    (LeftBridge : Fin mLeft → Type*)
    (RightBridge : Fin mRight → Type*) where
  commonWord : Common → StoppedWord
  leftBridgeWord : (i : Fin mLeft) → LeftBridge i → StoppedWord
  rightBridgeWord : (j : Fin mRight) → RightBridge j → StoppedWord
  assemble : Common ×
    (((i : Fin mLeft) → LeftBridge i) ×
      ((j : Fin mRight) → RightBridge j)) → StoppedWord
  prefixFree_assemble : PrefixFree assemble
  prefixFree_leftBridge : ∀ i, PrefixFree (leftBridgeWord i)
  prefixFree_rightBridge : ∀ j, PrefixFree (rightBridgeWord j)
  length_assemble : ∀ code,
    (assemble code).1 =
      ((commonWord code.1).1 +
        ∑ i, (leftBridgeWord i (code.2.1 i)).1) +
          ∑ j, (rightBridgeWord j (code.2.2 j)).1

/-- The literal stopped-path event represented by a common-prefix pair atom. -/
def SharedPrefixPairAtom.event {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    Set StepPath :=
  stoppedWordEvent atom.assemble

/-- The stopped-word mass of the common retained skeleton. -/
def SharedPrefixPairAtom.commonWeight {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    ℝ≥0∞ :=
  ∑' c, stoppedWordMass (atom.commonWord c)

/-- The mass of one left stopped-bridge code family. -/
def SharedPrefixPairAtom.leftKernel {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (i : Fin mLeft) : ℝ≥0∞ :=
  ∑' b, stoppedWordMass (atom.leftBridgeWord i b)

/-- The mass of one right stopped-bridge code family. -/
def SharedPrefixPairAtom.rightKernel {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (j : Fin mRight) : ℝ≥0∞ :=
  ∑' b, stoppedWordMass (atom.rightBridgeWord j b)

/-! ## Canonical splitting of a flat finite bridge tuple -/

/-- A dependent tuple indexed by `Fin (mLeft + mRight)` is canonically the
pair of its initial and final coordinate tuples.  This is the reindexing used
to view an existing `ComplementarySkeletonAtom` as a common-prefix pair atom. -/
def splitBridgeCodeEquiv {mLeft mRight : ℕ}
    (Bridge : Fin (mLeft + mRight) → Type*) :
    ((q : Fin (mLeft + mRight)) → Bridge q) ≃
      (((i : Fin mLeft) → Bridge (Fin.castAdd mRight i)) ×
        ((j : Fin mRight) → Bridge (Fin.natAdd mLeft j))) where
  toFun code :=
    ⟨fun i ↦ code (Fin.castAdd mRight i),
      fun j ↦ code (Fin.natAdd mLeft j)⟩
  invFun branches := Fin.addCases branches.1 branches.2
  left_inv code := by
    funext q
    exact Fin.addCases_castAdd_natAdd code q
  right_inv branches := by
    apply Prod.ext
    · funext i
      simp
    · funext j
      simp

/-! ## Finite dependent products of stopped-word masses -/

private theorem tsum_pi_stoppedWordMass
    {m : ℕ} {Bridge : Fin m → Type*} [∀ j, Countable (Bridge j)]
    (word : (j : Fin m) → Bridge j → StoppedWord) :
    (∑' b : (j : Fin m) → Bridge j,
        ∏ j, stoppedWordMass (word j (b j))) =
      ∏ j, ∑' bj, stoppedWordMass (word j bj) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (∑' b : (j : Fin (m + 1)) → Bridge j,
            ∏ j, stoppedWordMass (word j (b j))) =
            ∑' p : Bridge 0 × ((j : Fin m) → Bridge j.succ),
              ∏ j, stoppedWordMass
                (word j ((Fin.consEquiv Bridge) p j)) := by
                  exact (Equiv.tsum_eq (Fin.consEquiv Bridge)
                    (fun b ↦ ∏ j, stoppedWordMass (word j (b j)))).symm
        _ = ∑' p : Bridge 0 × ((j : Fin m) → Bridge j.succ),
              stoppedWordMass (word 0 p.1) *
                ∏ j, stoppedWordMass (word j.succ (p.2 j)) := by
                  apply tsum_congr
                  intro p
                  rw [Fin.prod_univ_succ]
                  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = ∑' b0 : Bridge 0, ∑' tail : (j : Fin m) → Bridge j.succ,
              stoppedWordMass (word 0 b0) *
                ∏ j, stoppedWordMass (word j.succ (tail j)) :=
                  (@ENNReal.tsum_prod (Bridge 0)
                    ((j : Fin m) → Bridge j.succ)
                    (fun b0 tail ↦ stoppedWordMass (word 0 b0) *
                      ∏ j, stoppedWordMass (word j.succ (tail j))))
        _ = ∑' b0 : Bridge 0,
              stoppedWordMass (word 0 b0) *
                ∑' tail : (j : Fin m) → Bridge j.succ,
                  ∏ j, stoppedWordMass (word j.succ (tail j)) := by
                    congr 1
                    funext b0
                    exact ENNReal.tsum_mul_left
        _ = ∑' b0 : Bridge 0,
              stoppedWordMass (word 0 b0) *
                ∏ j : Fin m, ∑' bj, stoppedWordMass (word j.succ bj) := by
                    rw [ih (Bridge := fun j : Fin m ↦ Bridge j.succ)
                      (fun j bj ↦ word j.succ bj)]
        _ = (∑' b0 : Bridge 0, stoppedWordMass (word 0 b0)) *
              ∏ j : Fin m, ∑' bj, stoppedWordMass (word j.succ bj) :=
                ENNReal.tsum_mul_right
        _ = ∏ j : Fin (m + 1), ∑' bj, stoppedWordMass (word j bj) := by
              rw [Fin.prod_univ_succ]

private theorem stoppedWordMass_length_pair_add
    {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (code : Common ×
      (((i : Fin mLeft) → LeftBridge i) ×
        ((j : Fin mRight) → RightBridge j))) :
    stoppedWordMass (atom.assemble code) =
      stoppedWordMass (atom.commonWord code.1) *
        ((∏ i, stoppedWordMass (atom.leftBridgeWord i (code.2.1 i))) *
          ∏ j, stoppedWordMass (atom.rightBridgeWord j (code.2.2 j))) := by
  unfold stoppedWordMass
  rw [atom.length_assemble code, pow_add, pow_add,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [mul_assoc]

private theorem tsum_pair_bridge_mass
    {mLeft mRight : ℕ}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    [∀ i, Countable (LeftBridge i)]
    [∀ j, Countable (RightBridge j)]
    (leftWord : (i : Fin mLeft) → LeftBridge i → StoppedWord)
    (rightWord : (j : Fin mRight) → RightBridge j → StoppedWord) :
    (∑' branches :
        ((i : Fin mLeft) → LeftBridge i) ×
          ((j : Fin mRight) → RightBridge j),
      (∏ i, stoppedWordMass (leftWord i (branches.1 i))) *
        ∏ j, stoppedWordMass (rightWord j (branches.2 j))) =
      (∏ i, ∑' bi, stoppedWordMass (leftWord i bi)) *
        ∏ j, ∑' bj, stoppedWordMass (rightWord j bj) := by
  calc
    (∑' branches :
        ((i : Fin mLeft) → LeftBridge i) ×
          ((j : Fin mRight) → RightBridge j),
      (∏ i, stoppedWordMass (leftWord i (branches.1 i))) *
        ∏ j, stoppedWordMass (rightWord j (branches.2 j))) =
      ∑' left : (i : Fin mLeft) → LeftBridge i,
        ∑' right : (j : Fin mRight) → RightBridge j,
          (∏ i, stoppedWordMass (leftWord i (left i))) *
            ∏ j, stoppedWordMass (rightWord j (right j)) :=
      (@ENNReal.tsum_prod
        ((i : Fin mLeft) → LeftBridge i)
        ((j : Fin mRight) → RightBridge j)
        (fun left right ↦
          (∏ i, stoppedWordMass (leftWord i (left i))) *
            ∏ j, stoppedWordMass (rightWord j (right j))))
    _ = ∑' left : (i : Fin mLeft) → LeftBridge i,
          (∏ i, stoppedWordMass (leftWord i (left i))) *
            ∑' right : (j : Fin mRight) → RightBridge j,
              ∏ j, stoppedWordMass (rightWord j (right j)) := by
          congr 1
          funext left
          exact ENNReal.tsum_mul_left
    _ = (∑' left : (i : Fin mLeft) → LeftBridge i,
          ∏ i, stoppedWordMass (leftWord i (left i))) *
            ∑' right : (j : Fin mRight) → RightBridge j,
              ∏ j, stoppedWordMass (rightWord j (right j)) :=
          ENNReal.tsum_mul_right
    _ = (∏ i, ∑' bi, stoppedWordMass (leftWord i bi)) *
          ∏ j, ∑' bj, stoppedWordMass (rightWord j bj) := by
          rw [tsum_pi_stoppedWordMass leftWord,
            tsum_pi_stoppedWordMass rightWord]

/-! ## Exact pair factorization -/

/-- Exact common-prefix/two-branch stopped-word factorization.  The common
retained weight appears exactly once. -/
theorem fairSteps_event_eq_commonWeight_mul_pairKernels
    {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    [Countable Common]
    [∀ i, Countable (LeftBridge i)]
    [∀ j, Countable (RightBridge j)]
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    fairSteps atom.event = atom.commonWeight *
      ((∏ i, atom.leftKernel i) * ∏ j, atom.rightKernel j) := by
  rw [SharedPrefixPairAtom.event,
    fairSteps_stoppedWordEvent atom.prefixFree_assemble]
  simp_rw [stoppedWordMass_length_pair_add atom]
  calc
    (∑' code : Common ×
        (((i : Fin mLeft) → LeftBridge i) ×
          ((j : Fin mRight) → RightBridge j)),
      stoppedWordMass (atom.commonWord code.1) *
        ((∏ i, stoppedWordMass (atom.leftBridgeWord i (code.2.1 i))) *
          ∏ j, stoppedWordMass (atom.rightBridgeWord j (code.2.2 j)))) =
      ∑' c : Common,
        ∑' branches :
          ((i : Fin mLeft) → LeftBridge i) ×
            ((j : Fin mRight) → RightBridge j),
        stoppedWordMass (atom.commonWord c) *
          ((∏ i, stoppedWordMass (atom.leftBridgeWord i (branches.1 i))) *
            ∏ j, stoppedWordMass
              (atom.rightBridgeWord j (branches.2 j))) :=
      (@ENNReal.tsum_prod Common
        (((i : Fin mLeft) → LeftBridge i) ×
          ((j : Fin mRight) → RightBridge j))
        (fun c branches ↦ stoppedWordMass (atom.commonWord c) *
          ((∏ i, stoppedWordMass (atom.leftBridgeWord i (branches.1 i))) *
            ∏ j, stoppedWordMass
              (atom.rightBridgeWord j (branches.2 j)))))
    _ = ∑' c : Common, stoppedWordMass (atom.commonWord c) *
          ∑' branches :
            ((i : Fin mLeft) → LeftBridge i) ×
              ((j : Fin mRight) → RightBridge j),
            ((∏ i, stoppedWordMass (atom.leftBridgeWord i (branches.1 i))) *
              ∏ j, stoppedWordMass
                (atom.rightBridgeWord j (branches.2 j))) := by
          congr 1
          funext c
          exact ENNReal.tsum_mul_left
    _ = (∑' c : Common, stoppedWordMass (atom.commonWord c)) *
          ∑' branches :
            ((i : Fin mLeft) → LeftBridge i) ×
              ((j : Fin mRight) → RightBridge j),
            ((∏ i, stoppedWordMass (atom.leftBridgeWord i (branches.1 i))) *
              ∏ j, stoppedWordMass
                (atom.rightBridgeWord j (branches.2 j))) :=
          ENNReal.tsum_mul_right
    _ = atom.commonWeight *
          ((∏ i, atom.leftKernel i) * ∏ j, atom.rightKernel j) := by
          rw [tsum_pair_bridge_mass atom.leftBridgeWord atom.rightBridgeWord]
          rfl

/-- Left-associated form of the exact factorization, convenient when a
one-point bound is applied to each branch product separately. -/
theorem fairSteps_event_eq_commonWeight_mul_leftKernels_mul_rightKernels
    {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    [Countable Common]
    [∀ i, Countable (LeftBridge i)]
    [∀ j, Countable (RightBridge j)]
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge) :
    fairSteps atom.event =
      (atom.commonWeight * ∏ i, atom.leftKernel i) *
        ∏ j, atom.rightKernel j := by
  rw [fairSteps_event_eq_commonWeight_mul_pairKernels atom, mul_assoc]

/-! ## Reindexing an existing flat complementary atom -/

/-- Canonically view an existing complementary atom with `mLeft + mRight`
bridge coordinates as a common-prefix pair atom.  No data are copied: the
common word is unchanged and the assembly map is merely precomposed with
`splitBridgeCodeEquiv.symm`. -/
def SharedPrefixPairAtom.ofComplementarySkeletonAtom
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge) :
    SharedPrefixPairAtom mLeft mRight Common
      (fun i ↦ Bridge (Fin.castAdd mRight i))
      (fun j ↦ Bridge (Fin.natAdd mLeft j)) where
  commonWord := base.complementWord
  leftBridgeWord := fun i ↦ base.bridgeWord (Fin.castAdd mRight i)
  rightBridgeWord := fun j ↦ base.bridgeWord (Fin.natAdd mLeft j)
  assemble := fun code ↦
    base.assemble ⟨code.1, (splitBridgeCodeEquiv Bridge).symm code.2⟩
  prefixFree_assemble := by
    intro a b hab
    apply base.prefixFree_assemble
    intro heq
    apply hab
    apply Prod.ext
    · exact congrArg
        (fun x : Common ×
          ((q : Fin (mLeft + mRight)) → Bridge q) ↦ x.1) heq
    · apply (splitBridgeCodeEquiv Bridge).symm.injective
      exact congrArg
        (fun x : Common ×
          ((q : Fin (mLeft + mRight)) → Bridge q) ↦ x.2) heq
  prefixFree_leftBridge := fun i ↦
    base.prefixFree_bridge (Fin.castAdd mRight i)
  prefixFree_rightBridge := fun j ↦
    base.prefixFree_bridge (Fin.natAdd mLeft j)
  length_assemble := by
    intro code
    rw [base.length_assemble, Fin.sum_univ_add, Nat.add_assoc]
    simp [splitBridgeCodeEquiv]

@[simp] theorem ofComplementarySkeletonAtom_commonWeight
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge) :
    (SharedPrefixPairAtom.ofComplementarySkeletonAtom base).commonWeight =
      base.weight := rfl

@[simp] theorem ofComplementarySkeletonAtom_leftKernel
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge)
    (i : Fin mLeft) :
    (SharedPrefixPairAtom.ofComplementarySkeletonAtom base).leftKernel i =
      base.kernel (Fin.castAdd mRight i) := rfl

@[simp] theorem ofComplementarySkeletonAtom_rightKernel
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge)
    (j : Fin mRight) :
    (SharedPrefixPairAtom.ofComplementarySkeletonAtom base).rightKernel j =
      base.kernel (Fin.natAdd mLeft j) := rfl

/-- The canonical reindexing preserves the literal stopped-path event. -/
@[simp] theorem ofComplementarySkeletonAtom_event
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge) :
    (SharedPrefixPairAtom.ofComplementarySkeletonAtom base).event =
      base.event := by
  ext omega
  change omega ∈ ⋃ code : Common ×
      (((i : Fin mLeft) → Bridge (Fin.castAdd mRight i)) ×
        ((j : Fin mRight) → Bridge (Fin.natAdd mLeft j))), stoppedWordCylinder
      (base.assemble
        ⟨code.1, (splitBridgeCodeEquiv Bridge).symm code.2⟩) ↔
    omega ∈ ⋃ code : Common ×
      ((q : Fin (mLeft + mRight)) → Bridge q),
        stoppedWordCylinder (base.assemble code)
  constructor
  · intro homega
    obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr
      ⟨⟨code.1, (splitBridgeCodeEquiv Bridge).symm code.2⟩, hcode⟩
  · intro homega
    obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
    refine Set.mem_iUnion.mpr
      ⟨⟨code.1, splitBridgeCodeEquiv Bridge code.2⟩, ?_⟩
    simpa using hcode

/-- Exact split-product form for an existing flat complementary atom. -/
theorem fairSteps_complementarySkeletonAtom_event_eq_weight_mul_splitKernels
    {mLeft mRight : ℕ} {Common : Type*}
    {Bridge : Fin (mLeft + mRight) → Type*}
    [Countable Common] [∀ q, Countable (Bridge q)]
    (base : ComplementarySkeletonAtom (mLeft + mRight) Common Bridge) :
    fairSteps base.event = base.weight *
      ((∏ i : Fin mLeft, base.kernel (Fin.castAdd mRight i)) *
        ∏ j : Fin mRight, base.kernel (Fin.natAdd mLeft j)) := by
  let atom := SharedPrefixPairAtom.ofComplementarySkeletonAtom
    (mLeft := mLeft) (mRight := mRight) base
  rw [← ofComplementarySkeletonAtom_event base]
  simpa [atom] using fairSteps_event_eq_commonWeight_mul_pairKernels atom

/-! ## Rewriting the two products as concrete stopped events -/

/-- Replace each code-family kernel by the fair-walk mass of a concrete
stopped event.  The premises are pathwise coverage equalities, not probability
or measure equalities. -/
theorem fairSteps_event_eq_commonWeight_mul_stoppedEvents
    {mLeft mRight : ℕ}
    {Common : Type*}
    {LeftBridge : Fin mLeft → Type*}
    {RightBridge : Fin mRight → Type*}
    [Countable Common]
    [∀ i, Countable (LeftBridge i)]
    [∀ j, Countable (RightBridge j)]
    (atom : SharedPrefixPairAtom mLeft mRight Common LeftBridge RightBridge)
    (leftEvent : Fin mLeft → Set StepPath)
    (rightEvent : Fin mRight → Set StepPath)
    (hleft : ∀ i, leftEvent i = stoppedWordEvent (atom.leftBridgeWord i))
    (hright : ∀ j, rightEvent j = stoppedWordEvent (atom.rightBridgeWord j)) :
    fairSteps atom.event = atom.commonWeight *
      ((∏ i, fairSteps (leftEvent i)) * ∏ j, fairSteps (rightEvent j)) := by
  rw [fairSteps_event_eq_commonWeight_mul_pairKernels atom]
  congr 2
  · apply Finset.prod_congr rfl
    intro i _hi
    rw [hleft i, fairSteps_stoppedWordEvent (atom.prefixFree_leftBridge i)]
    rfl
  · apply Finset.prod_congr rfl
    intro j _hj
    rw [hright j, fairSteps_stoppedWordEvent (atom.prefixFree_rightBridge j)]
    rfl

/-! ## Canonical marked first-boundary specialization -/

/-- Canonical common-prefix pair factorization when both bridge families are
the actual marked first-boundary word codes.  The only compatibility premises
say that insertion uses the underlying finite word of each canonical code. -/
theorem fairSteps_event_eq_commonWeight_mul_canonical_markedKernels
    {mLeft mRight : ℕ} {Common : Type*} [Countable Common]
    (leftBoundary : Fin mLeft → Set Point)
    (leftTarget leftStart leftEndpoint : Fin mLeft → Point)
    (leftVisits : Fin mLeft → ℕ)
    (leftTargetInterior : ∀ i, leftTarget i ∉ leftBoundary i)
    (rightBoundary : Fin mRight → Set Point)
    (rightTarget rightStart rightEndpoint : Fin mRight → Point)
    (rightVisits : Fin mRight → ℕ)
    (rightTargetInterior : ∀ j, rightTarget j ∉ rightBoundary j)
    (atom : SharedPrefixPairAtom mLeft mRight Common
      (fun i ↦ BoundaryVisitExitWordCode (leftBoundary i) (leftTarget i)
        (leftStart i) (leftVisits i) (leftEndpoint i))
      (fun j ↦ BoundaryVisitExitWordCode (rightBoundary j) (rightTarget j)
        (rightStart j) (rightVisits j) (rightEndpoint j)))
    (hleftWord : ∀ i b, atom.leftBridgeWord i b = b.1)
    (hrightWord : ∀ j b, atom.rightBridgeWord j b = b.1) :
    fairSteps atom.event = atom.commonWeight *
      ((∏ i, fairSteps (boundaryVisitExitAtom (leftBoundary i) (leftTarget i)
          (leftStart i) (leftVisits i) (leftEndpoint i))) *
        ∏ j, fairSteps (boundaryVisitExitAtom (rightBoundary j) (rightTarget j)
          (rightStart j) (rightVisits j) (rightEndpoint j))) := by
  apply fairSteps_event_eq_commonWeight_mul_stoppedEvents atom
  · intro i
    calc
      boundaryVisitExitAtom (leftBoundary i) (leftTarget i) (leftStart i)
          (leftVisits i) (leftEndpoint i) =
          stoppedWordEvent
            (fun b : BoundaryVisitExitWordCode (leftBoundary i) (leftTarget i)
              (leftStart i) (leftVisits i) (leftEndpoint i) ↦ b.1) :=
        boundaryVisitExitAtom_eq_stoppedWordEvent
          (leftBoundary i) (leftTarget i) (leftStart i)
          (leftVisits i) (leftEndpoint i) (leftTargetInterior i)
      _ = stoppedWordEvent (atom.leftBridgeWord i) := by
        apply congrArg stoppedWordEvent
        funext b
        exact (hleftWord i b).symm
  · intro j
    calc
      boundaryVisitExitAtom (rightBoundary j) (rightTarget j) (rightStart j)
          (rightVisits j) (rightEndpoint j) =
          stoppedWordEvent
            (fun b : BoundaryVisitExitWordCode (rightBoundary j) (rightTarget j)
              (rightStart j) (rightVisits j) (rightEndpoint j) ↦ b.1) :=
        boundaryVisitExitAtom_eq_stoppedWordEvent
          (rightBoundary j) (rightTarget j) (rightStart j)
          (rightVisits j) (rightEndpoint j) (rightTargetInterior j)
      _ = stoppedWordEvent (atom.rightBridgeWord j) := by
        apply congrArg stoppedWordEvent
        funext b
        exact (hrightWord j b).symm

end

end Erdos1165.SharedPrefixPairFactorization

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.Hitting
import ErdosProblems.Erdos1165.TerminalSequentialVisitLaw

/-!
# Prefix-free factorization of omitted stopped bridges

The terminal HLOZ decomposition removes finitely many variable-length
inner-to-outer pieces from a stopped path and retains every other increment.
The retained word is allowed to contain the entire complementary skeleton,
including information occurring after any one of the removed pieces.  Thus
it must not be treated as an event measurable at the first entrance time.

This file proves the needed factorization by a literal finite-word insertion
argument.  A stopped word denotes its exact prefix cylinder.  A
`ComplementarySkeletonAtom` records a prefix-free insertion of one retained
word and finitely many bridge words into a complete stopped word, together
with the evident length identity.  No measure identity is a field of that
structure.  Exact fair-walk cylinder masses and countable additivity prove
the mass formula; Tonelli then separates the retained code from all bridge
codes.

The final two theorems rewrite the bridge-code masses as the concrete
unmarked and marked first-boundary atoms from `TerminalSequentialVisitLaw`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.MarkedBridgeFactorization

open Hitting
open BoundaryVisitLaw
open TerminalSequentialVisitLaw

noncomputable section

/-! ## Prefix-free stopped words -/

/-- A genuinely variable-length finite increment word. -/
abbrev StoppedWord := Σ n : ℕ, Fin n → Direction

/-- The exact prefix cylinder represented by a stopped word. -/
def stoppedWordCylinder (w : StoppedWord) : Set StepPath :=
  stepPrefix w.1 ⁻¹' {w.2}

/-- The fair-walk mass of the exact prefix represented by `w`. -/
def stoppedWordMass (w : StoppedWord) : ℝ≥0∞ :=
  (4 : ℝ≥0∞)⁻¹ ^ w.1

theorem measurableSet_stoppedWordCylinder (w : StoppedWord) :
    MeasurableSet (stoppedWordCylinder w) := by
  exact (measurable_stepPrefix w.1) (Set.to_countable ({w.2} : Set _)).measurableSet

theorem fairSteps_stoppedWordCylinder (w : StoppedWord) :
    fairSteps (stoppedWordCylinder w) = stoppedWordMass w := by
  change fairSteps (Hitting.prefixSteps w.1 ⁻¹' {w.2}) =
    (4 : ℝ≥0∞)⁻¹ ^ w.1
  simpa only [one_div, ENNReal.inv_pow] using
    Hitting.fairSteps_prefix_singleton w.1 w.2

/-- The event represented by a countable family of finite stopped words. -/
def stoppedWordEvent {Code : Type*} (word : Code → StoppedWord) : Set StepPath :=
  ⋃ c, stoppedWordCylinder (word c)

/-- Prefix-freeness in precisely the form required for countable additivity:
distinct codes specify disjoint exact stopped-prefix cylinders. -/
def PrefixFree {Code : Type*} (word : Code → StoppedWord) : Prop :=
  Pairwise fun c d ↦
    Disjoint (stoppedWordCylinder (word c)) (stoppedWordCylinder (word d))

theorem measurableSet_stoppedWordEvent {Code : Type*} [Countable Code]
    (word : Code → StoppedWord) : MeasurableSet (stoppedWordEvent word) := by
  exact MeasurableSet.iUnion fun c ↦ measurableSet_stoppedWordCylinder (word c)

/-- A prefix-free word family has mass equal to the sum of its literal
cylinder masses. -/
theorem fairSteps_stoppedWordEvent {Code : Type*} [Countable Code]
    {word : Code → StoppedWord} (hfree : PrefixFree word) :
    fairSteps (stoppedWordEvent word) = ∑' c, stoppedWordMass (word c) := by
  rw [stoppedWordEvent, measure_iUnion hfree]
  · simp_rw [fairSteps_stoppedWordCylinder]
  · exact fun c ↦ measurableSet_stoppedWordCylinder (word c)

/-! ## A concrete insertion interface -/

/-- Literal prefix-free insertion data for a fixed complementary skeleton
atom.  `Complement` codes all retained information, with no adaptedness
restriction.  `Bridge j` codes the omitted stopped word at coordinate `j`.
The `assemble` function is the concrete insertion map.  Its prefix-free field
is normally proved from an erasure/insertion inverse and uniqueness of the
stopping horizon; importantly, no probability or measure equality is assumed.
-/
structure ComplementarySkeletonAtom (m : ℕ)
    (Complement : Type*) (Bridge : Fin m → Type*) where
  complementWord : Complement → StoppedWord
  bridgeWord : (j : Fin m) → Bridge j → StoppedWord
  assemble : Complement × ((j : Fin m) → Bridge j) → StoppedWord
  prefixFree_assemble : PrefixFree assemble
  prefixFree_bridge : ∀ j, PrefixFree (bridgeWord j)
  length_assemble : ∀ code,
    (assemble code).1 = (complementWord code.1).1 +
      ∑ j, (bridgeWord j (code.2 j)).1

/-- The literal event obtained by inserting all omitted bridges. -/
def ComplementarySkeletonAtom.event {m : ℕ}
    {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge) : Set StepPath :=
  stoppedWordEvent atom.assemble

/-- Mass of the retained complementary-skeleton code. -/
def ComplementarySkeletonAtom.weight {m : ℕ}
    {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge) : ℝ≥0∞ :=
  ∑' c, stoppedWordMass (atom.complementWord c)

/-- Mass of the `j`-th bridge code family. -/
def ComplementarySkeletonAtom.kernel {m : ℕ}
    {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (j : Fin m) : ℝ≥0∞ :=
  ∑' b, stoppedWordMass (atom.bridgeWord j b)

private theorem stoppedWordMass_length_add
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (code : Complement × ((j : Fin m) → Bridge j)) :
    stoppedWordMass (atom.assemble code) =
      stoppedWordMass (atom.complementWord code.1) *
        ∏ j, stoppedWordMass (atom.bridgeWord j (code.2 j)) := by
  unfold stoppedWordMass
  rw [atom.length_assemble code, pow_add, Finset.prod_pow_eq_pow_sum]

/-- The mass of one fully assembled insertion word is the retained-word mass
times the product of the inserted bridge-word masses.  This public form is
useful when a later refinement selects a non-coordinatewise subtype of full
bridge tuples. -/
theorem stoppedWordMass_assemble
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (code : Complement × ((j : Fin m) → Bridge j)) :
    stoppedWordMass (atom.assemble code) =
      stoppedWordMass (atom.complementWord code.1) *
        ∏ j, stoppedWordMass (atom.bridgeWord j (code.2 j)) := by
  exact stoppedWordMass_length_add atom code

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

/-- Exact mass factorization for a fixed complementary skeleton atom.  The
complete future skeleton is retained in `atom.weight`; it was never required
to be measurable at any entrance clock. -/
theorem fairSteps_event_eq_weight_mul_prod_kernel
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [Countable Complement] [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge) :
    fairSteps atom.event = atom.weight * ∏ j, atom.kernel j := by
  rw [ComplementarySkeletonAtom.event,
    fairSteps_stoppedWordEvent atom.prefixFree_assemble]
  simp_rw [stoppedWordMass_length_add atom]
  calc
    (∑' code : Complement × ((j : Fin m) → Bridge j),
        stoppedWordMass (atom.complementWord code.1) *
          ∏ j, stoppedWordMass (atom.bridgeWord j (code.2 j))) =
        ∑' code : Complement × ((j : Fin m) → Bridge j),
          stoppedWordMass (atom.complementWord code.1) *
            ∏ j, stoppedWordMass (atom.bridgeWord j (code.2 j)) := rfl
    _ = ∑' c : Complement, ∑' b : (j : Fin m) → Bridge j,
          stoppedWordMass (atom.complementWord c) *
            ∏ j, stoppedWordMass (atom.bridgeWord j (b j)) :=
      (@ENNReal.tsum_prod Complement ((j : Fin m) → Bridge j)
        (fun c b ↦ stoppedWordMass (atom.complementWord c) *
          ∏ j, stoppedWordMass (atom.bridgeWord j (b j))))
    _ = ∑' c : Complement, stoppedWordMass (atom.complementWord c) *
          ∑' b : (j : Fin m) → Bridge j,
            ∏ j, stoppedWordMass (atom.bridgeWord j (b j)) := by
      congr 1
      funext c
      exact ENNReal.tsum_mul_left
    _ = (∑' c : Complement, stoppedWordMass (atom.complementWord c)) *
          ∑' b : (j : Fin m) → Bridge j,
            ∏ j, stoppedWordMass (atom.bridgeWord j (b j)) :=
      ENNReal.tsum_mul_right
    _ = atom.weight * ∏ j, atom.kernel j := by
      rw [tsum_pi_stoppedWordMass atom.bridgeWord]
      rfl

/-! ## Rewriting the factors as actual stopped bridge kernels -/

/-- A prefix-free code for a concrete measurable stopped event.  The equality
is a pathwise coverage statement, not a mass premise. -/
structure StoppedEventCode (event : Set StepPath) where
  Code : Type*
  countableCode : Countable Code
  word : Code → StoppedWord
  prefixFree_word : PrefixFree word
  event_eq : event = stoppedWordEvent word

attribute [instance] StoppedEventCode.countableCode

theorem StoppedEventCode.mass_eq {event : Set StepPath}
    (code : StoppedEventCode event) :
    fairSteps event = ∑' c, stoppedWordMass (code.word c) := by
  calc
    fairSteps event = fairSteps (stoppedWordEvent code.word) :=
      congrArg fairSteps code.event_eq
    _ = ∑' c, stoppedWordMass (code.word c) :=
      fairSteps_stoppedWordEvent code.prefixFree_word

/-! ## Canonical prefix codes for first-boundary atoms -/

/-- Extend a finite word by a harmless default direction.  Only the prefix
through the word's length is ever inspected. -/
def extendStoppedWord (w : StoppedWord) : StepPath := fun q ↦
  if hq : q < w.1 then w.2 ⟨q, hq⟩ else 0

@[simp] theorem stepPrefix_extendStoppedWord (w : StoppedWord) :
    stepPrefix w.1 (extendStoppedWord w) = w.2 := by
  funext q
  simp [stepPrefix, extendStoppedWord, q.isLt]

lemma trajectoryFrom_eq_extendStoppedWord_of_mem
    {w : StoppedWord} {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder w) (start : Point)
    {q : ℕ} (hq : q ≤ w.1) :
    PlanarPotential.trajectoryFrom start omega q =
      PlanarPotential.trajectoryFrom start (extendStoppedWord w) q := by
  have hprefix : stepPrefix w.1 omega = w.2 := homega
  unfold PlanarPotential.trajectoryFrom trajectory
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i < q := Finset.mem_range.mp hi
  have hin : i < w.1 := hiq.trans_le hq
  have hstep := congrFun hprefix ⟨i, hin⟩
  change directionVector (omega i) =
    directionVector (extendStoppedWord w i)
  rw [extendStoppedWord, dif_pos hin]
  exact congrArg directionVector (by simpa only [stepPrefix] using hstep)

lemma absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    {boundary : Set Point} {start : Point} {w : StoppedWord}
    {omega : StepPath} (homega : omega ∈ stoppedWordCylinder w)
    (hfirst : AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord w) w.1) :
    AbsoluteBoundaryFirstAt boundary start omega w.1 := by
  constructor
  · rw [trajectoryFrom_eq_extendStoppedWord_of_mem homega start le_rfl]
    exact hfirst.1
  · intro q hq
    rw [trajectoryFrom_eq_extendStoppedWord_of_mem homega start hq.le]
    exact hfirst.2 q hq

lemma targetVisitSum_eq_extendStoppedWord_of_mem
    {w : StoppedWord} {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder w) (start target : Point) :
    targetVisitSum start target omega w.1 =
      targetVisitSum start target (extendStoppedWord w) w.1 := by
  unfold targetVisitSum
  apply Finset.sum_congr rfl
  intro q hq
  rw [trajectoryFrom_eq_extendStoppedWord_of_mem homega start
    (Finset.mem_range.mp hq).le]

lemma absoluteBoundaryFirstAt_unique
    {boundary : Set Point} {start : Point} {omega : StepPath} {N M : ℕ}
    (hN : AbsoluteBoundaryFirstAt boundary start omega N)
    (hM : AbsoluteBoundaryFirstAt boundary start omega M) : N = M := by
  rcases lt_trichotomy N M with hlt | heq | hgt
  · exact (hM.2 N hlt hN.1).elim
  · exact heq
  · exact (hN.2 M hgt hM.1).elim

private theorem prefixFree_of_absoluteBoundaryFirstAt
    {Code : Type*} (word : Code → StoppedWord)
    (hword : Function.Injective word)
    (boundary : Set Point) (start : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (word c)) (word c).1) :
    PrefixFree word := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hc (hfirst c)
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hd (hfirst d)
  have hlen : (word c).1 = (word d).1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  apply hcd
  apply hword
  apply Sigma.ext hlen
  apply (Fin.heq_fun_iff hlen).2
  intro i
  change stepPrefix (word c).1 omega = (word c).2 at hc
  change stepPrefix (word d).1 omega = (word d).2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

/-- Finite first-boundary words ending at a prescribed endpoint. -/
abbrev BoundaryExitWordCode
    (boundary : Set Point) (start endpoint : Point) :=
  {w : StoppedWord //
    AbsoluteBoundaryFirstAt boundary start (extendStoppedWord w) w.1 ∧
      PlanarPotential.trajectoryFrom start (extendStoppedWord w) w.1 = endpoint}

/-- The canonical code family for `boundaryExitEndpointSteps` is prefix-free. -/
theorem prefixFree_boundaryExitWordCode
    (boundary : Set Point) (start endpoint : Point) :
    PrefixFree (fun c : BoundaryExitWordCode boundary start endpoint ↦ c.1) := by
  apply prefixFree_of_absoluteBoundaryFirstAt
    (fun c : BoundaryExitWordCode boundary start endpoint ↦ c.1)
    Subtype.val_injective boundary start
  exact fun c ↦ c.2.1

/-- Pathwise coverage of the unmarked first-boundary endpoint event by its
literal finite stopped words. -/
theorem boundaryExitEndpointSteps_eq_stoppedWordEvent
    (boundary : Set Point) (start endpoint : Point) :
    boundaryExitEndpointSteps boundary start endpoint =
      stoppedWordEvent
        (fun c : BoundaryExitWordCode boundary start endpoint ↦ c.1) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨N, hfirst, hendpoint⟩ := Set.mem_iUnion.mp homega
    let w : StoppedWord := ⟨N, stepPrefix N omega⟩
    have hwmem : omega ∈ stoppedWordCylinder w := by
      change stepPrefix N omega = stepPrefix N omega
      rfl
    have hwfirst : AbsoluteBoundaryFirstAt boundary start
        (extendStoppedWord w) N := by
      constructor
      · rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
        exact hfirst.1
      · intro q hq
        rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start hq.le]
        exact hfirst.2 q hq
    let c : BoundaryExitWordCode boundary start endpoint :=
      ⟨w, hwfirst, by
        rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
        exact hendpoint⟩
    exact Set.mem_iUnion.mpr ⟨c, hwmem⟩
  · intro homega
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp homega
    have hfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1
    have hendpoint : PlanarPotential.trajectoryFrom start omega c.1.1 = endpoint := by
      rw [trajectoryFrom_eq_extendStoppedWord_of_mem hc start le_rfl]
      exact c.2.2
    exact Set.mem_iUnion.mpr ⟨c.1.1, hfirst, hendpoint⟩

/-- A fully concrete stopped-event code for the unmarked endpoint kernel. -/
def boundaryExitStoppedEventCode
    (boundary : Set Point) (start endpoint : Point) :
    StoppedEventCode (boundaryExitEndpointSteps boundary start endpoint) where
  Code := BoundaryExitWordCode boundary start endpoint
  countableCode := inferInstance
  word := fun c ↦ c.1
  prefixFree_word := prefixFree_boundaryExitWordCode boundary start endpoint
  event_eq := boundaryExitEndpointSteps_eq_stoppedWordEvent boundary start endpoint

/-- First-boundary words carrying both their target-visit count and endpoint. -/
abbrev BoundaryVisitExitWordCode
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point) :=
  {w : StoppedWord //
    AbsoluteBoundaryFirstAt boundary start (extendStoppedWord w) w.1 ∧
      targetVisitSum start target (extendStoppedWord w) w.1 = k ∧
      PlanarPotential.trajectoryFrom start (extendStoppedWord w) w.1 = endpoint}

theorem prefixFree_boundaryVisitExitWordCode
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point) :
    PrefixFree (fun c : BoundaryVisitExitWordCode boundary target start k endpoint ↦
      c.1) := by
  apply prefixFree_of_absoluteBoundaryFirstAt
    (fun c : BoundaryVisitExitWordCode boundary target start k endpoint ↦ c.1)
    Subtype.val_injective boundary start
  exact fun c ↦ c.2.1

/-- Pathwise coverage of the marked visit-count/endpoint atom by its literal
finite stopped words. -/
theorem boundaryVisitExitAtom_eq_stoppedWordEvent
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point)
    (htarget : target ∉ boundary) :
    boundaryVisitExitAtom boundary target start k endpoint =
      stoppedWordEvent
        (fun c : BoundaryVisitExitWordCode boundary target start k endpoint ↦ c.1) := by
  ext omega
  constructor
  · rintro ⟨hvisit, hexit⟩
    obtain ⟨N, hfirst, hendpoint⟩ := Set.mem_iUnion.mp hexit
    have hcount : targetVisitSum start target omega N = k :=
      (mem_boundaryVisitAtom_iff_targetVisitSum htarget hfirst).1 hvisit
    let w : StoppedWord := ⟨N, stepPrefix N omega⟩
    have hwmem : omega ∈ stoppedWordCylinder w := by
      change stepPrefix N omega = stepPrefix N omega
      rfl
    have hwfirst : AbsoluteBoundaryFirstAt boundary start
        (extendStoppedWord w) N := by
      constructor
      · rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
        exact hfirst.1
      · intro q hq
        rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start hq.le]
        exact hfirst.2 q hq
    let c : BoundaryVisitExitWordCode boundary target start k endpoint :=
      ⟨w, hwfirst,
        (targetVisitSum_eq_extendStoppedWord_of_mem hwmem start target).symm.trans hcount,
        by
          rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
          exact hendpoint⟩
    exact Set.mem_iUnion.mpr ⟨c, hwmem⟩
  · intro homega
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp homega
    have hfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1
    have hcount : targetVisitSum start target omega c.1.1 = k := by
      rw [targetVisitSum_eq_extendStoppedWord_of_mem hc start target]
      exact c.2.2.1
    have hvisit : omega ∈ boundaryVisitAtom boundary target start k :=
      (mem_boundaryVisitAtom_iff_targetVisitSum htarget hfirst).2 hcount
    have hendpoint : PlanarPotential.trajectoryFrom start omega c.1.1 = endpoint := by
      rw [trajectoryFrom_eq_extendStoppedWord_of_mem hc start le_rfl]
      exact c.2.2.2
    exact ⟨hvisit, Set.mem_iUnion.mpr ⟨c.1.1, hfirst, hendpoint⟩⟩

/-- A fully concrete stopped-event code for the marked endpoint kernel. -/
def boundaryVisitExitStoppedEventCode
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point)
    (htarget : target ∉ boundary) :
    StoppedEventCode
      (boundaryVisitExitAtom boundary target start k endpoint) where
  Code := BoundaryVisitExitWordCode boundary target start k endpoint
  countableCode := inferInstance
  word := fun c ↦ c.1
  prefixFree_word :=
    prefixFree_boundaryVisitExitWordCode boundary target start k endpoint
  event_eq := boundaryVisitExitAtom_eq_stoppedWordEvent
    boundary target start k endpoint htarget

/-- Unmarked bridge factorization with the actual fixed-endpoint
first-boundary kernel `boundaryExitEndpointSteps`. -/
theorem fairSteps_event_eq_weight_mul_boundaryExitEndpointSteps
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [Countable Complement] [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (boundary : Fin m → Set Point)
    (start endpoint : Fin m → Point)
    (hbridge : ∀ j, boundaryExitEndpointSteps
      (boundary j) (start j) (endpoint j) =
        stoppedWordEvent (atom.bridgeWord j)) :
    fairSteps atom.event = atom.weight *
      ∏ j, fairSteps
        (boundaryExitEndpointSteps (boundary j) (start j) (endpoint j)) := by
  rw [fairSteps_event_eq_weight_mul_prod_kernel atom]
  apply congrArg (atom.weight * ·)
  apply Finset.prod_congr rfl
  intro j _hj
  rw [hbridge j, fairSteps_stoppedWordEvent (atom.prefixFree_bridge j)]
  rfl

/-- Marked bridge factorization with the actual joint visit-count/exit-point
atom `boundaryVisitExitAtom`. -/
theorem fairSteps_event_eq_weight_mul_boundaryVisitExitAtom
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [Countable Complement] [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (boundary : Fin m → Set Point)
    (target start endpoint : Fin m → Point)
    (visits : Fin m → ℕ)
    (hbridge : ∀ j, boundaryVisitExitAtom
      (boundary j) (target j) (start j) (visits j) (endpoint j) =
        stoppedWordEvent (atom.bridgeWord j)) :
    fairSteps atom.event = atom.weight *
      ∏ j, fairSteps
        (boundaryVisitExitAtom (boundary j) (target j) (start j)
          (visits j) (endpoint j)) := by
  rw [fairSteps_event_eq_weight_mul_prod_kernel atom]
  apply congrArg (atom.weight * ·)
  apply Finset.prod_congr rfl
  intro j _hj
  rw [hbridge j, fairSteps_stoppedWordEvent (atom.prefixFree_bridge j)]
  rfl

/-- Canonical unmarked form: bridge codes are the actual finite
first-boundary words, so the only compatibility premise says that insertion
uses their underlying word.  There is no event- or measure-level assumption. -/
theorem fairSteps_event_eq_weight_mul_canonical_unmarkedKernel
    {m : ℕ} {Complement : Type*} [Countable Complement]
    (boundary : Fin m → Set Point)
    (start endpoint : Fin m → Point)
    (atom : ComplementarySkeletonAtom m Complement
      (fun j ↦ BoundaryExitWordCode
        (boundary j) (start j) (endpoint j)))
    (hword : ∀ j b, atom.bridgeWord j b = b.1) :
    fairSteps atom.event = atom.weight *
      ∏ j, fairSteps
        (boundaryExitEndpointSteps (boundary j) (start j) (endpoint j)) := by
  apply fairSteps_event_eq_weight_mul_boundaryExitEndpointSteps atom
    boundary start endpoint
  intro j
  calc
    boundaryExitEndpointSteps (boundary j) (start j) (endpoint j) =
        stoppedWordEvent
          (fun c : BoundaryExitWordCode
            (boundary j) (start j) (endpoint j) ↦ c.1) :=
      boundaryExitEndpointSteps_eq_stoppedWordEvent
        (boundary j) (start j) (endpoint j)
    _ = stoppedWordEvent (atom.bridgeWord j) := by
      apply congrArg stoppedWordEvent
      funext b
      exact (hword j b).symm

/-- Canonical marked form: exact mass `W * ∏ K`, where each `K` is the
joint target-visit-count/outer-endpoint kernel of the literal stopped bridge. -/
theorem fairSteps_event_eq_weight_mul_canonical_markedKernel
    {m : ℕ} {Complement : Type*} [Countable Complement]
    (boundary : Fin m → Set Point)
    (target start endpoint : Fin m → Point)
    (visits : Fin m → ℕ)
    (htarget : ∀ j, target j ∉ boundary j)
    (atom : ComplementarySkeletonAtom m Complement
      (fun j ↦ BoundaryVisitExitWordCode
        (boundary j) (target j) (start j) (visits j) (endpoint j)))
    (hword : ∀ j b, atom.bridgeWord j b = b.1) :
    fairSteps atom.event = atom.weight *
      ∏ j, fairSteps
        (boundaryVisitExitAtom (boundary j) (target j) (start j)
          (visits j) (endpoint j)) := by
  apply fairSteps_event_eq_weight_mul_boundaryVisitExitAtom atom
    boundary target start endpoint visits
  intro j
  calc
    boundaryVisitExitAtom (boundary j) (target j) (start j)
        (visits j) (endpoint j) =
        stoppedWordEvent
          (fun c : BoundaryVisitExitWordCode (boundary j) (target j)
            (start j) (visits j) (endpoint j) ↦ c.1) :=
      boundaryVisitExitAtom_eq_stoppedWordEvent
        (boundary j) (target j) (start j) (visits j) (endpoint j) (htarget j)
    _ = stoppedWordEvent (atom.bridgeWord j) := by
      apply congrArg stoppedWordEvent
      funext b
      exact (hword j b).symm

end

end Erdos1165.MarkedBridgeFactorization

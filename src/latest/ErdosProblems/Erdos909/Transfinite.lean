/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Basic

/-!
# A continuum-length independent selector

This file isolates the transfinite counting argument in the construction of
Anderson and Keisler.  At every stage fewer than continuum many points have
already been chosen.  If every left and right fibre of a forbidden binary
relation is countable, then the points newly forbidden by the earlier choices
form a set of cardinality at most

`#(Set.Iio i) * Cardinal.aleph0 < Cardinal.continuum`.

The strict inequality does not use regularity of the continuum: multiplication
of two cardinals below an infinite cardinal is again below that cardinal.
-/

open Cardinal Set

namespace Erdos909

universe u

/-- The canonical well-ordered type of stages of cardinality continuum. -/
abbrev ContinuumStage : Type u :=
  (Cardinal.continuum : Cardinal.{u}).ord.ToType

section Selector

variable {X : Type u}

private def earlierForbidden
    (R : X → X → Prop) (i : ContinuumStage.{u})
    (previous : ∀ j, j < i → X) : Set X :=
  ⋃ j : Set.Iio i,
    {x | R x (previous j.1 j.2) ∨ R (previous j.1 j.2) x}

private theorem earlierForbidden_card_lt_continuum
    (R : X → X → Prop)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable)
    (i : ContinuumStage.{u}) (previous : ∀ j, j < i → X) :
    #(earlierForbidden R i previous) < Cardinal.continuum := by
  let fibre : Set.Iio i → Set X := fun j ↦
    {x | R x (previous j.1 j.2) ∨ R (previous j.1 j.2) x}
  have hfibre : ∀ j, #(fibre j) ≤ Cardinal.aleph0 := by
    intro j
    exact ((hleft _).union (hright _)).le_aleph0
  have hiSup : (⨆ j, #(fibre j)) ≤ Cardinal.aleph0 :=
    ciSup_le' hfibre
  calc
    #(earlierForbidden R i previous) = #(⋃ j, fibre j) := rfl
    _ ≤ #(Set.Iio i) * ⨆ j, #(fibre j) := Cardinal.mk_iUnion_le fibre
    _ ≤ #(Set.Iio i) * Cardinal.aleph0 :=
      mul_le_mul' le_rfl hiSup
    _ < Cardinal.continuum :=
      Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum
        (by simpa [ContinuumStage] using Cardinal.mk_Iio_lt i (by simp))
        Cardinal.aleph0_lt_continuum

private def forbiddenAt
    (avoid : Set X) (R : X → X → Prop) (i : ContinuumStage.{u})
    (previous : ∀ j, j < i → X) : Set X :=
  avoid ∪ {x | R x x} ∪ earlierForbidden R i previous

private theorem forbiddenAt_card_lt_continuum
    (avoid : Set X) (R : X → X → Prop)
    (havoid : avoid.Countable)
    (hdiag : {x | R x x}.Countable)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable)
    (i : ContinuumStage.{u}) (previous : ∀ j, j < i → X) :
    #(forbiddenAt avoid R i previous) < Cardinal.continuum := by
  have hcount : #(avoid ∪ {x | R x x} : Set X) ≤ Cardinal.aleph0 :=
    (havoid.union hdiag).le_aleph0
  calc
    #(forbiddenAt avoid R i previous) ≤
        #(avoid ∪ {x | R x x} : Set X) +
          #(earlierForbidden R i previous) :=
      Cardinal.mk_union_le _ _
    _ < Cardinal.continuum :=
      Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum
        (hcount.trans_lt Cardinal.aleph0_lt_continuum)
        (earlierForbidden_card_lt_continuum R hleft hright i previous)

private theorem exists_stage_choice
    (target : ContinuumStage.{u} → Set X) (avoid : Set X) (R : X → X → Prop)
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | R x x}.Countable)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable)
    (i : ContinuumStage.{u}) (previous : ∀ j, j < i → X) :
    ∃ x ∈ target i, x ∉ forbiddenAt avoid R i previous := by
  have hcard : #(forbiddenAt avoid R i previous) < #(target i) := by
    rw [htarget i]
    exact forbiddenAt_card_lt_continuum avoid R havoid hdiag hleft hright i previous
  exact (Cardinal.sdiff_nonempty_of_mk_lt_mk hcard)

/-- A choice made by well-founded recursion through the initial ordinal of
the continuum.  Its defining condition includes membership in the current
target, avoidance of the unary obstruction and diagonal obstruction, and
independence from all earlier choices in both orientations. -/
noncomputable def independentSelector
    (target : ContinuumStage.{u} → Set X) (avoid : Set X) (R : X → X → Prop)
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | R x x}.Countable)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable) :
    ContinuumStage.{u} → X :=
  wellFounded_lt.fix fun i previous ↦
    Classical.choose
      (exists_stage_choice target avoid R htarget havoid hdiag hleft hright i previous)

private theorem independentSelector_spec
    (target : ContinuumStage.{u} → Set X) (avoid : Set X) (R : X → X → Prop)
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | R x x}.Countable)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable)
    (i : ContinuumStage.{u}) :
    independentSelector target avoid R htarget havoid hdiag hleft hright i ∈ target i ∧
      independentSelector target avoid R htarget havoid hdiag hleft hright i ∉
        forbiddenAt avoid R i
          (fun j _ ↦ independentSelector target avoid R htarget havoid hdiag hleft hright j) := by
  rw [independentSelector, wellFounded_lt.fix_eq]
  exact Classical.choose_spec
    (exists_stage_choice target avoid R htarget havoid hdiag hleft hright i _)

/-- Transfinite independent-selector theorem used in the Anderson--Keisler
construction.  The selector visits every prescribed continuum-sized target,
avoids the countable unary obstruction, and no ordered pair of selected
points lies in the forbidden relation. -/
theorem exists_independent_selector
    (target : ContinuumStage.{u} → Set X) (avoid : Set X) (R : X → X → Prop)
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | R x x}.Countable)
    (hleft : ∀ y, {x | R x y}.Countable)
    (hright : ∀ y, {x | R y x}.Countable) :
    ∃ f : ContinuumStage.{u} → X,
      (∀ i, f i ∈ target i) ∧
      (∀ i, f i ∉ avoid) ∧
      ∀ i j, ¬R (f i) (f j) := by
  let f := independentSelector target avoid R htarget havoid hdiag hleft hright
  refine ⟨f, fun i ↦ (independentSelector_spec
    target avoid R htarget havoid hdiag hleft hright i).1, ?_, ?_⟩
  · intro i
    exact fun hi ↦ (independentSelector_spec
      target avoid R htarget havoid hdiag hleft hright i).2 (Or.inl (Or.inl hi))
  · intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · intro hR
      have hspec := (independentSelector_spec
        target avoid R htarget havoid hdiag hleft hright j).2
      apply hspec
      exact Or.inr (mem_iUnion.2 ⟨⟨i, hij⟩, Or.inr hR⟩)
    · intro hR
      have hspec := (independentSelector_spec
        target avoid R htarget havoid hdiag hleft hright i).2
      exact hspec (Or.inl (Or.inr hR))
    · intro hR
      have hspec := (independentSelector_spec
        target avoid R htarget havoid hdiag hleft hright i).2
      apply hspec
      exact Or.inr (mem_iUnion.2 ⟨⟨j, hji⟩, Or.inl hR⟩)

/-- Set-valued form of `exists_independent_selector`.  This is the interface
used by the geometric construction: `K` meets every target, is disjoint from
the unary obstruction, and `K × K` avoids the binary obstruction. -/
theorem exists_set_meeting_targets_avoiding
    (target : ContinuumStage.{u} → Set X) (avoid : Set X)
    (obstruction : Set (X × X))
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | (x, x) ∈ obstruction}.Countable)
    (hleft : ∀ y, {x | (x, y) ∈ obstruction}.Countable)
    (hright : ∀ y, {x | (y, x) ∈ obstruction}.Countable) :
    ∃ K : Set X,
      (∀ i, (K ∩ target i).Nonempty) ∧
      Disjoint K avoid ∧
      Disjoint (K ×ˢ K) obstruction := by
  obtain ⟨f, htarget_f, havoid_f, hR_f⟩ :=
    exists_independent_selector target avoid (fun x y ↦ (x, y) ∈ obstruction)
      htarget havoid hdiag hleft hright
  refine ⟨range f, ?_, ?_, ?_⟩
  · intro i
    exact ⟨f i, ⟨mem_range_self i, htarget_f i⟩⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ hi
    exact havoid_f i hi
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ hij
    exact hR_f i j hij

/-- A scheduling wrapper for an arbitrary nonempty family of at most
continuum many targets.  An embedding of the target indices into
`ContinuumStage` has a surjective inverse, so every target is scheduled at
least once during the continuum-length recursion. -/
theorem exists_set_meeting_indexed_targets_avoiding
    {ι : Type u} [Nonempty ι]
    (target : ι → Set X) (avoid : Set X) (obstruction : Set (X × X))
    (hι : #ι ≤ Cardinal.continuum)
    (htarget : ∀ i, #(target i) = Cardinal.continuum)
    (havoid : avoid.Countable)
    (hdiag : {x | (x, x) ∈ obstruction}.Countable)
    (hleft : ∀ y, {x | (x, y) ∈ obstruction}.Countable)
    (hright : ∀ y, {x | (y, x) ∈ obstruction}.Countable) :
    ∃ K : Set X,
      (∀ i, (K ∩ target i).Nonempty) ∧
      Disjoint K avoid ∧
      Disjoint (K ×ˢ K) obstruction := by
  have hι' : #ι ≤ #(ContinuumStage.{u}) := by
    simpa [ContinuumStage] using hι
  obtain ⟨e : ι ↪ ContinuumStage.{u}⟩ :=
    (Cardinal.le_def ι ContinuumStage.{u}).1 hι'
  let schedule : ContinuumStage.{u} → ι := Function.invFun e
  have hschedule : Function.Surjective schedule :=
    Function.invFun_surjective e.injective
  obtain ⟨K, hmeet, hKavoid, hKobstruction⟩ :=
    exists_set_meeting_targets_avoiding (target ∘ schedule) avoid obstruction
      (fun i ↦ htarget (schedule i)) havoid hdiag hleft hright
  refine ⟨K, ?_, hKavoid, hKobstruction⟩
  intro i
  obtain ⟨j, hj⟩ := hschedule i
  simpa [Function.comp_apply, hj] using hmeet j

end Selector

end Erdos909

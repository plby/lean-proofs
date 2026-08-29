/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.WarpLimits
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Erdős Problem 599: ordinal iterated arrow

This file supplies the recursion and order theory behind the transfinite
iterated-arrow construction used in Aharoni--Berger's Lemma 3.19.  It does
not assume that an arbitrary collection of paths has a graph-theoretically
valid limit.  Instead, a concrete development supplies a limit constructor
and proves, as hypotheses to the lemmas below, that it has the required
eventual-membership and forward-extension properties.

At a limit ordinal `o`, membership in `ordinalSetLiminf o s` means membership
in every sufficiently late stage strictly below `o`.  Thus this is the
bounded ordinal version of `WarpLimits.filterSetLiminf`, not a union or a
topological limit.
-/

namespace Erdos599
namespace IteratedArrow

open Set

universe u v w

/-! ## Eventual membership below an ordinal -/

/-- The eventual-membership limit of sets indexed strictly below `o`.

The witness `a < o` is the beginning of a tail.  A point belongs to the
limit exactly when it belongs to every stage `b` of that tail with `b < o`.
Writing the bound explicitly makes the definition useful even at `o = 0`,
where it gives the empty set. -/
def ordinalSetLiminf {X : Type u} (o : Ordinal.{v})
    (s : ∀ a : Ordinal.{v}, a < o → Set X) : Set X :=
  {x | ∃ a, ∃ _ha : a < o, ∀ b, (hb : b < o) → a ≤ b → x ∈ s b hb}

@[simp]
theorem mem_ordinalSetLiminf {X : Type u} {o : Ordinal.{v}}
    (s : ∀ a : Ordinal.{v}, a < o → Set X) (x : X) :
    x ∈ ordinalSetLiminf o s ↔
      ∃ a, ∃ _ha : a < o, ∀ b, (hb : b < o) → a ≤ b → x ∈ s b hb :=
  Iff.rfl

@[simp]
theorem ordinalSetLiminf_zero {X : Type u}
    (s : ∀ a : Ordinal.{v}, a < 0 → Set X) :
    ordinalSetLiminf 0 s = ∅ := by
  ext x
  simp

/-- Pointwise inclusion below the bound induces inclusion of ordinal
liminfs. -/
theorem ordinalSetLiminf_mono {X : Type u} {o : Ordinal.{v}}
    {s t : ∀ a : Ordinal.{v}, a < o → Set X}
    (h : ∀ a ha, s a ha ⊆ t a ha) :
    ordinalSetLiminf o s ⊆ ordinalSetLiminf o t := by
  rintro x ⟨a, ha, htail⟩
  exact ⟨a, ha, fun b hb hab ↦ h b hb (htail b hb hab)⟩

/-- A monotone bounded family has every stage contained in its eventual
limit. -/
theorem subset_ordinalSetLiminf_of_monotone {X : Type u} {o : Ordinal.{v}}
    (s : ∀ a : Ordinal.{v}, a < o → Set X)
    (hs : ∀ a b, (ha : a < o) → (hb : b < o) → a ≤ b →
      s a ha ⊆ s b hb)
    (a : Ordinal.{v}) (ha : a < o) :
    s a ha ⊆ ordinalSetLiminf o s := by
  intro x hx
  exact ⟨a, ha, fun b hb hab ↦ hs a b ha hb hab hx⟩

/-- For a monotone bounded family, eventual membership is the union of the
stages.  This is a derived fact; the definition remains the liminf. -/
theorem ordinalSetLiminf_eq_iUnion_of_monotone {X : Type u}
    {o : Ordinal.{v}} (s : ∀ a : Ordinal.{v}, a < o → Set X)
    (hs : ∀ a b, (ha : a < o) → (hb : b < o) → a ≤ b →
      s a ha ⊆ s b hb) :
    ordinalSetLiminf o s = ⋃ a : Set.Iio o, s a.1 a.2 := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, ha, htail⟩
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, htail a ha le_rfl⟩
  · intro x hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
    exact subset_ordinalSetLiminf_of_monotone s hs a.1 a.2 hxa

/-- The bounded ordinal definition agrees with the `atTop` filter liminf on
the subtype of stages below `o`, whenever that subtype is nonempty and
directed. -/
theorem ordinalSetLiminf_eq_filterSetLiminf {X : Type u}
    (o : Ordinal.{v}) (s : ∀ a : Ordinal.{v}, a < o → Set X)
    [Nonempty (Set.Iio o)] [IsDirectedOrder (Set.Iio o)] :
    ordinalSetLiminf o s =
      WarpLimits.filterSetLiminf Filter.atTop
        (fun a : Set.Iio o ↦ s a.1 a.2) := by
  ext x
  constructor
  · rintro ⟨a, ha, htail⟩
    rw [WarpLimits.mem_filterSetLiminf, Filter.eventually_atTop]
    exact ⟨⟨a, ha⟩, fun b hab ↦ htail b.1 b.2 hab⟩
  · intro hx
    rw [WarpLimits.mem_filterSetLiminf, Filter.eventually_atTop] at hx
    obtain ⟨a, htail⟩ := hx
    exact ⟨a.1, a.2, fun b hb hab ↦ htail ⟨b, hb⟩ hab⟩

/-! ## Transfinite arrow recursion -/

/-- The type of limit-stage constructors.  There are deliberately no laws
in this definition.  Graph-theoretic validity, observable liminf equations,
and extension properties are supplied separately to each theorem. -/
abbrev LimitBuilder (Family : Type u) :=
  ∀ o : Ordinal.{v}, Order.IsSuccLimit o →
    (∀ a : Ordinal.{v}, a < o → Family) → Family

/-- Transfinite iterated arrow.

`input` is the sequence to be accumulated.  Stage zero is `input 0`; at a
successor, the old accumulator is arrowed with the new input; and at a limit
the supplied limit constructor receives all earlier accumulators. -/
noncomputable def iteratedArrow {Family : Type u}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) (o : Ordinal.{v}) : Family :=
  Ordinal.limitRecOn o (input 0)
    (fun a accumulated ↦ arrow accumulated (input (a + 1)))
    limit

@[simp]
theorem iteratedArrow_zero {Family : Type u}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) :
    iteratedArrow input arrow limit 0 = input 0 := by
  simp [iteratedArrow]

@[simp]
theorem iteratedArrow_add_one {Family : Type u}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) (o : Ordinal.{v}) :
    iteratedArrow input arrow limit (o + 1) =
      arrow (iteratedArrow input arrow limit o) (input (o + 1)) := by
  simp [iteratedArrow]

theorem iteratedArrow_limit {Family : Type u}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) (o : Ordinal.{v})
    (ho : Order.IsSuccLimit o) :
    iteratedArrow input arrow limit o =
      limit o ho (fun a _ ↦ iteratedArrow input arrow limit a) := by
  simpa [iteratedArrow] using
    (Ordinal.limitRecOn_limit o (input 0)
      (fun a accumulated ↦ arrow accumulated (input (a + 1))) limit ho)

/-- Transfinite preservation of a property of path families.  This is the
generic induction pattern used to prove that every accumulated family is a
warp or a wave: prove it at zero, prove it is preserved by the actual
successor arrow, and prove it for a limit constructor from all earlier
instances. -/
theorem iteratedArrow_property {Family : Type u}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) (Good : Family → Prop)
    (hzero : Good (input 0))
    (hsucc : ∀ a accumulated, Good accumulated →
      Good (arrow accumulated (input (a + 1))))
    (hlimit : ∀ o ho prior, (∀ a ha, Good (prior a ha)) →
      Good (limit o ho prior)) :
    ∀ o, Good (iteratedArrow input arrow limit o) := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero => simpa using hzero
  | add_one o ih =>
      rw [iteratedArrow_add_one]
      exact hsucc o _ ih
  | limit o ho ih =>
      rw [iteratedArrow_limit input arrow limit o ho]
      exact hlimit o ho _ ih

/-- A limit constructor realizes eventual membership for one observable.
This property is intentionally a predicate passed to theorems, rather than
a field built into the recursion data. -/
def PreservesLiminf {Family : Type u} {X : Type w}
    (observe : Family → Set X) (limit : LimitBuilder Family) : Prop :=
  ∀ o ho prior,
    observe (limit o ho prior) =
      ordinalSetLiminf o (fun a ha ↦ observe (prior a ha))

/-- At a limit stage, an observed point belongs to the iterated arrow iff
it belongs to every sufficiently late earlier observed stage. -/
theorem mem_observe_iteratedArrow_limit_iff {Family : Type u} {X : Type w}
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family) (observe : Family → Set X)
    (hlimit : PreservesLiminf observe limit) (o : Ordinal.{v})
    (ho : Order.IsSuccLimit o) (x : X) :
    x ∈ observe (iteratedArrow input arrow limit o) ↔
      ∃ a, ∃ _ha : a < o, ∀ b, (hb : b < o) → a ≤ b →
        x ∈ observe (iteratedArrow input arrow limit b) := by
  rw [iteratedArrow_limit input arrow limit o ho, hlimit o ho]
  rfl

/-! ## Forward-extension preservation -/

/-- The accumulator is forward-extended by every successor arrow step. -/
def ArrowExtends {Family : Type u} (F : WarpLimits.ForwardSystem Family)
    (arrow : Family → Family → Family) : Prop :=
  ∀ accumulated next, F.Extends accumulated (arrow accumulated next)

/-- A limit constructor is above every earlier stage passed to it. -/
def LimitExtends {Family : Type u} (F : WarpLimits.ForwardSystem Family)
    (limit : LimitBuilder Family) : Prop :=
  ∀ o ho prior a ha, F.Extends (prior a ha) (limit o ho prior)

/-- All later iterated-arrow stages forward-extend all earlier stages.

Only the two local facts actually used by the transfinite induction are
assumed: an arrow extends its accumulator, and a limit extends each member
of the family from which it is built. -/
theorem iteratedArrow_forward {Family : Type u}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hlimit : LimitExtends F limit) :
    ∀ {a b : Ordinal.{v}}, a ≤ b →
      F.Extends (iteratedArrow input arrow limit a)
        (iteratedArrow input arrow limit b) := by
  intro a b hab
  induction b using Ordinal.limitRecOn with
  | zero =>
      have ha : a = 0 := nonpos_iff_eq_zero.mp hab
      subst a
      exact F.refl _
  | add_one b ih =>
      rcases hab.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).mp hab
        exact F.trans (ih hab')
          (by
            rw [iteratedArrow_add_one]
            exact harrow _ _)
      · exact F.refl _
  | limit b hb ih =>
      rcases hab.lt_or_eq with hab | rfl
      · rw [iteratedArrow_limit input arrow limit b hb]
        exact hlimit b hb
          (fun c _ ↦ iteratedArrow input arrow limit c) a hab
      · exact F.refl _

/-- The iterated-arrow stages below `o`, packaged as a `ForwardChain`. -/
noncomputable def forwardChainBelow {Family : Type u}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hlimit : LimitExtends F limit)
    (o : Ordinal.{v}) : WarpLimits.ForwardChain F (Set.Iio o) where
  stage a := iteratedArrow input arrow limit a.1
  forward := fun {_ _} hab ↦
    iteratedArrow_forward F input arrow limit harrow hlimit hab

/-- At a limit ordinal, the limit-stage accumulator is an upper bound for
the full forward chain of earlier accumulators. -/
theorem isUpperBound_iteratedArrow_limit {Family : Type u}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hlimit : LimitExtends F limit)
    (o : Ordinal.{v}) (_ho : Order.IsSuccLimit o) :
    F.IsUpperBound
      (forwardChainBelow F input arrow limit harrow hlimit o).stage
      (iteratedArrow input arrow limit o) := by
  intro a
  change F.Extends (iteratedArrow input arrow limit a.1)
    (iteratedArrow input arrow limit o)
  exact iteratedArrow_forward F input arrow limit harrow hlimit a.2.le

/-- More generally, every stage at or above a bound is an upper bound for
the iterated-arrow chain below that bound. -/
theorem isUpperBound_iteratedArrow_of_le {Family : Type u}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hlimit : LimitExtends F limit)
    {o z : Ordinal.{v}} (hoz : o ≤ z) :
    F.IsUpperBound
      (forwardChainBelow F input arrow limit harrow hlimit o).stage
      (iteratedArrow input arrow limit z) := by
  intro a
  change F.Extends (iteratedArrow input arrow limit a.1)
    (iteratedArrow input arrow limit z)
  exact iteratedArrow_forward F input arrow limit harrow hlimit
    (a.2.le.trans hoz)

/-- An observable respecting forward extension is monotone along the full
ordinal iterated-arrow sequence. -/
theorem observe_iteratedArrow_monotone {Family : Type u} {X : Type w}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hlimit : LimitExtends F limit)
    (observe : Family → Set X) (hobserve : F.Respects observe) :
    Monotone (fun o ↦ observe (iteratedArrow input arrow limit o)) := by
  intro a b hab
  exact hobserve
    (iteratedArrow_forward F input arrow limit harrow hlimit hab)

/-- If a concrete limit realizes the observable liminf, then at a limit
ordinal that observable is the union of the earlier observable stages.  The
union formula follows from forward monotonicity and is not used as the
definition of the limit. -/
theorem observe_iteratedArrow_limit_eq_iUnion {Family : Type u} {X : Type w}
    (F : WarpLimits.ForwardSystem Family)
    (input : Ordinal.{v} → Family) (arrow : Family → Family → Family)
    (limit : LimitBuilder Family)
    (harrow : ArrowExtends F arrow) (hforwardLimit : LimitExtends F limit)
    (observe : Family → Set X) (hobserve : F.Respects observe)
    (hobservableLimit : PreservesLiminf observe limit)
    (o : Ordinal.{v}) (ho : Order.IsSuccLimit o) :
    observe (iteratedArrow input arrow limit o) =
      ⋃ a : Set.Iio o, observe (iteratedArrow input arrow limit a.1) := by
  rw [iteratedArrow_limit input arrow limit o ho, hobservableLimit o ho]
  apply ordinalSetLiminf_eq_iUnion_of_monotone
  intro a b ha hb hab
  exact hobserve
    (iteratedArrow_forward F input arrow limit harrow hforwardLimit hab)

/-! ## The literal path-family liminf -/

/-- A concrete limit builder for families represented by sets.  It retains
exactly those members which occur at every sufficiently late earlier stage.
For graph-theoretic warp limits built instead from eventual vertex and edge
membership, use a concrete `LimitBuilder` and prove `PreservesLiminf` for
each desired observable. -/
def setFamilyLimit (o : Ordinal.{v}) (_ho : Order.IsSuccLimit o)
    (prior : ∀ a : Ordinal.{v}, a < o → Set X) : Set X :=
  ordinalSetLiminf o prior

theorem setFamilyLimit_preservesLiminf :
    PreservesLiminf (fun W : Set X ↦ W) (setFamilyLimit (X := X)) := by
  intro o ho prior
  rfl

/-- The literal set-family iterated arrow. -/
noncomputable def iteratedSetArrow (input : Ordinal.{v} → Set X)
    (arrow : Set X → Set X → Set X) (o : Ordinal.{v}) : Set X :=
  iteratedArrow input arrow (setFamilyLimit (X := X)) o

@[simp]
theorem iteratedSetArrow_zero (input : Ordinal.{v} → Set X)
    (arrow : Set X → Set X → Set X) :
    iteratedSetArrow input arrow 0 = input 0 := by
  simp [iteratedSetArrow]

@[simp]
theorem iteratedSetArrow_add_one (input : Ordinal.{v} → Set X)
    (arrow : Set X → Set X → Set X) (o : Ordinal.{v}) :
    iteratedSetArrow input arrow (o + 1) =
      arrow (iteratedSetArrow input arrow o) (input (o + 1)) := by
  simp [iteratedSetArrow]

theorem mem_iteratedSetArrow_limit_iff (input : Ordinal.{v} → Set X)
    (arrow : Set X → Set X → Set X) (o : Ordinal.{v})
    (ho : Order.IsSuccLimit o) (x : X) :
    x ∈ iteratedSetArrow input arrow o ↔
      ∃ a, ∃ _ha : a < o, ∀ b, (hb : b < o) → a ≤ b →
        x ∈ iteratedSetArrow input arrow b := by
  exact mem_observe_iteratedArrow_limit_iff input arrow
    (setFamilyLimit (X := X)) (fun W ↦ W)
    setFamilyLimit_preservesLiminf o ho x

end IteratedArrow
end Erdos599

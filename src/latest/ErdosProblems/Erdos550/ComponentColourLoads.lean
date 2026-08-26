import Mathlib
import ErdosProblems.Erdos550.ParityContactColor
import ErdosProblems.Erdos550.StatefulBlockGlue
import ErdosProblems.Erdos550.TauFineSumEncoding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact two-side loads of a parity-oriented component

The packedness invariant is updated by the two colour-class cardinalities of
the newly embedded component.  These lemmas turn the placement conclusion of
the rooted-pair step into those exact image cardinalities.
-/

open Finset

namespace Erdos550

open Classical

variable {A : Type} {V : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V]

/-- The global-colour load of one indexed shrub component.  This is the
source-side weight used by the whole-edge allocation theorem. -/
noncomputable def componentColourLoad
    (T : SimpleGraph A) (S : Finset A)
    (col : ShrubVertex T S → Bool) (side : Bool)
    (c : NonseedComponent T S) : ℝ :=
  ((Finset.univ.filter fun v : ShrubVertex T S =>
    shrubComponent T S v = c ∧ col v = side).card : ℝ)

lemma componentColourLoad_nonneg
    (T : SimpleGraph A) (S : Finset A)
    (col : ShrubVertex T S → Bool) (side : Bool)
    (c : NonseedComponent T S) :
    0 ≤ componentColourLoad T S col side c := by
  exact Nat.cast_nonneg _

lemma componentColourLoad_false_add_true
    (T : SimpleGraph A) (S : Finset A)
    (col : ShrubVertex T S → Bool)
    (c : NonseedComponent T S) :
    componentColourLoad T S col false c +
        componentColourLoad T S col true c =
      ((componentNonseedVertices T S c.1).card : ℝ) := by
  let F := Finset.univ.filter fun v : ShrubVertex T S =>
    shrubComponent T S v = c ∧ col v = false
  let R := Finset.univ.filter fun v : ShrubVertex T S =>
    shrubComponent T S v = c ∧ col v = true
  let C := Finset.univ.filter fun v : ShrubVertex T S =>
    shrubComponent T S v = c
  have hdisj : Disjoint F R := by
    rw [Finset.disjoint_left]
    intro v hvF hvR
    have hf := (Finset.mem_filter.mp hvF).2.2
    have hr := (Finset.mem_filter.mp hvR).2.2
    simp_all
  have hunion : F ∪ R = C := by
    ext v
    cases h : col v <;> simp [F, R, C, h]
  have hcard :
      F.card + R.card =
        (componentNonseedVertices T S c.1).card := by
    calc
      F.card + R.card = (F ∪ R).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = C.card := by rw [hunion]
      _ = (componentNonseedVertices T S c.1).card := by
        simpa [C] using! shrubComponent_fiber_card T S c
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcard
  simpa only [componentColourLoad, F, R, Nat.cast_add] using! hcast

noncomputable def componentSideCount
    (T : SimpleGraph A) (S : Finset A)
    (col : A → Bool) (c : NonseedComponent T S)
    (root : A) (side : Bool) : ℕ :=
  (Finset.univ.filter fun x : RootedComponentVertex T S c =>
    relativeComponentColor col root x.1 = side).card

lemma componentSideCount_false_add_true
    (T : SimpleGraph A) (S : Finset A)
    (col : A → Bool) (c : NonseedComponent T S)
    (root : A) :
    componentSideCount T S col c root false +
        componentSideCount T S col c root true =
      Fintype.card (RootedComponentVertex T S c) := by
  let F := Finset.univ.filter fun x : RootedComponentVertex T S c =>
    relativeComponentColor col root x.1 = false
  let R := Finset.univ.filter fun x : RootedComponentVertex T S c =>
    relativeComponentColor col root x.1 = true
  have hdisj : Disjoint F R := by
    rw [Finset.disjoint_left]
    intro x hxF hxR
    have hf := (Finset.mem_filter.mp hxF).2
    have hr := (Finset.mem_filter.mp hxR).2
    simp_all
  have hunion :
      F ∪ R =
        (Finset.univ : Finset (RootedComponentVertex T S c)) := by
    ext x
    simp only [F, R, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      cases h : relativeComponentColor col root x.1 with
      | false => exact Or.inl rfl
      | true => exact Or.inr rfl
  calc
    componentSideCount T S col c root false +
        componentSideCount T S col c root true =
      F.card + R.card := by rfl
    _ = (F ∪ R).card := (Finset.card_union_of_disjoint hdisj).symm
    _ = Fintype.card (RootedComponentVertex T S c) := by
      rw [hunion, Finset.card_univ]

/-- If the two target sides are disjoint, a colour-respecting injective local
embedding contributes exactly the corresponding two colour-class sizes. -/
lemma component_image_side_cards
    (T : SimpleGraph A) (S : Finset A)
    (col : A → Bool) (c : NonseedComponent T S)
    (root : A)
    (f : RootedComponentVertex T S c → V)
    (hfinj : Function.Injective f)
    (rootSide otherSide freeRoot freeOther : Finset V)
    (hdisj : Disjoint rootSide otherSide)
    (hfreeRoot : freeRoot ⊆ rootSide)
    (hfreeOther : freeOther ⊆ otherSide)
    (hfside : ∀ x, f x ∈
      (if relativeComponentColor col root x.1
        then freeOther else freeRoot)) :
    ((Finset.univ.image f) ∩ rootSide).card =
        componentSideCount T S col c root false ∧
      ((Finset.univ.image f) ∩ otherSide).card =
        componentSideCount T S col c root true := by
  have hrootFilter :
      (Finset.univ.filter fun x : RootedComponentVertex T S c =>
          f x ∈ rootSide) =
        Finset.univ.filter fun x =>
          relativeComponentColor col root x.1 = false := by
    ext x
    cases hx : relativeComponentColor col root x.1 with
    | false =>
        have hmem : f x ∈ rootSide := hfreeRoot (by
          simpa [hx] using! hfside x)
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        simp [hx, hmem]
    | true =>
        have hother : f x ∈ otherSide := hfreeOther (by
          simpa [hx] using! hfside x)
        have hnot : f x ∉ rootSide :=
          fun hroot => Finset.disjoint_left.mp hdisj hroot hother
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        simp [hx, hnot]
  have hotherFilter :
      (Finset.univ.filter fun x : RootedComponentVertex T S c =>
          f x ∈ otherSide) =
        Finset.univ.filter fun x =>
          relativeComponentColor col root x.1 = true := by
    ext x
    cases hx : relativeComponentColor col root x.1 with
    | false =>
        have hroot : f x ∈ rootSide := hfreeRoot (by
          simpa [hx] using! hfside x)
        have hnot : f x ∉ otherSide :=
          fun hother => Finset.disjoint_left.mp hdisj hroot hother
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        simp [hx, hnot]
    | true =>
        have hmem : f x ∈ otherSide := hfreeOther (by
          simpa [hx] using! hfside x)
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        simp [hx, hmem]
  constructor
  · rw [card_image_inter_eq_card_filter Finset.univ f rootSide
      (fun _ _ _ _ h => hfinj h), hrootFilter]
    rfl
  · rw [card_image_inter_eq_card_filter Finset.univ f otherSide
      (fun _ _ _ _ h => hfinj h), hotherFilter]
    rfl

end Erdos550

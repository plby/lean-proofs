import Mathlib.Data.Set.Countable
import Mathlib.Order.Directed
import Mathlib.Order.WellFounded

/-!
# Meeting requirements along a well-order with countable initial segments

This is the transfinite bookkeeping lemma used in the CH back-and-forth.
The extension property is an explicit input to this general lemma; it must be
proved for the density algebras before the lemma can yield their isomorphism.
-/

namespace Erdos1123

open Set

universe u v

/-- Countable extensions and directed unions meet all requirements along a
well-order whose strict initial segments are countable. -/
theorem exists_good_meeting_all
    {α : Type u} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    (hI : ∀ i : I, (Set.Iio i).Countable)
    (Good : Set α → Prop) (Requirement : I → Set α → Prop)
    (hStart : ∃ s, s.Countable ∧ Good s)
    (hUnion : ∀ {κ : Type v} (f : κ → Set α), Directed (· ⊆ ·) f →
      (∀ i, Good (f i)) → Good (⋃ i, f i))
    (hReq : ∀ i {s t}, s ⊆ t → Requirement i s → Requirement i t)
    (hExtend : ∀ s, s.Countable → Good s → ∀ i,
      ∃ t, t.Countable ∧ Good t ∧ s ⊆ t ∧ Requirement i t) :
    ∃ s, Good s ∧ ∀ i, Requirement i s := by
  classical
  let Stage := {s : Set α // s.Countable ∧ Good s}
  let initial : Stage := ⟨Classical.choose hStart, Classical.choose_spec hStart⟩
  let step (i : I) (previous : ∀ j, j < i → Stage) : Stage :=
    let u : Set α := ⋃ j : Set.Iio i, (previous j j.property).val
    have hu : u.Countable := by
      let : Countable (Set.Iio i) := (hI i).to_subtype
      exact Set.countable_iUnion fun j => (previous j j.property).property.1
    if hg : Good u then
      let ht := hExtend u hu hg i
      ⟨Classical.choose ht, (Classical.choose_spec ht).1,
        (Classical.choose_spec ht).2.1⟩
    else initial
  let stages : I → Stage := WellFounded.fix wellFounded_lt step
  have hstages (i : I) : stages i = step i (fun j _ => stages j) :=
    WellFounded.fix_eq wellFounded_lt step i
  have hstep (i : I) (previous : ∀ j, j < i → Stage)
      (hg : Good (⋃ j : Set.Iio i, (previous j j.property).val)) :
      (⋃ j : Set.Iio i, (previous j j.property).val) ⊆ (step i previous).val ∧
        Requirement i (step i previous).val := by
    dsimp only [step]
    rw [dif_pos hg]
    let : Countable (Set.Iio i) := (hI i).to_subtype
    have hu : (⋃ j : Set.Iio i, (previous j j.property).val).Countable :=
      Set.countable_iUnion fun j => (previous j j.property).property.1
    exact (Classical.choose_spec (hExtend _ hu hg i)).2.2
  have hst (i : I) :
      (∀ j, j < i → (stages j).val ⊆ (stages i).val) ∧
        Requirement i (stages i).val := by
    apply (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).induction i
    intro i ih
    let previous : Set.Iio i → Set α := fun j => (stages j).val
    have hm : Monotone previous := by
      intro j k hjk
      rcases lt_or_eq_of_le hjk with hjk | rfl
      · exact (ih k k.property).1 j hjk
      · exact Set.Subset.refl _
    have hg : Good (⋃ j, previous j) :=
      hUnion previous hm.directed_le (fun j => (stages j).property.2)
    have hs := hstep i (fun j _ => stages j) hg
    rw [← hstages i] at hs
    refine ⟨fun j hj => ?_, hs.2⟩
    exact (Set.subset_iUnion (fun k : Set.Iio i => (stages k).val) ⟨j, hj⟩).trans hs.1
  have hm : Monotone (fun i => (stages i).val) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact (hst j).1 i hij
    · exact Set.Subset.refl _
  refine ⟨⋃ i, (stages i).val, hUnion _ hm.directed_le (fun i => (stages i).property.2), ?_⟩
  intro i
  exact hReq i (Set.subset_iUnion _ i) (hst i).2

end Erdos1123

import Mathlib

open Function Set

universe u v

namespace Erdos965

variable {α : Type u} {β : Type v}

/-- An uncountable set mapped to a countable type has an uncountable fibre. -/
theorem uncountable_fiber_of_countable_range [Countable β]
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ b, ¬ {x ∈ I | f x = b}.Countable := by
  by_contra! h
  apply hI
  refine (Set.countable_iUnion h).mono ?_
  intro x hx
  exact Set.mem_iUnion.2 ⟨f x, hx, rfl⟩

/-- If all relative fibres of a map are countable, its restriction to an
uncountable set has uncountable range. -/
theorem image_uncountable_of_countable_fibers
    (f : α → β) {I : Set α} (hI : ¬ I.Countable)
    (hfib : ∀ b, {x ∈ I | f x = b}.Countable) :
    ¬ (f '' I).Countable := by
  intro him
  apply hI
  refine (him.biUnion fun b hb ↦ hfib b).mono ?_
  rintro x hx
  refine Set.mem_iUnion.2 ⟨f x, Set.mem_iUnion.2 ⟨⟨x, hx, rfl⟩, hx, rfl⟩⟩

/-- On an uncountable set, every map is constant on an uncountable subset or
injective on an uncountable subset. -/
theorem uncountable_constant_or_injective
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ((∃ b, ∀ x ∈ J, f x = b) ∨ InjOn f J) := by
  classical
  by_cases hbig : ∃ b, ¬ {x ∈ I | f x = b}.Countable
  · obtain ⟨b, hb⟩ := hbig
    refine ⟨{x ∈ I | f x = b}, fun _ hx ↦ hx.1, hb, Or.inl ⟨b, ?_⟩⟩
    intro x hx
    exact hx.2
  · push Not at hbig
    have himage : ¬ (f '' I).Countable :=
      image_uncountable_of_countable_fibers f hI hbig
    let R := f '' I
    have hsec : ∀ b : R, ∃ x ∈ I, f x = b := by
      rintro ⟨b, x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    choose g hgI hgf using hsec
    let J : Set α := Set.range g
    have hg_inj : Injective g := by
      intro b c hbc
      apply Subtype.ext
      rw [← hgf b, ← hgf c, hbc]
    have hJsub : J ⊆ I := by
      rintro x ⟨b, rfl⟩
      exact hgI b
    have hJunc : ¬ J.Countable := by
      intro hJ
      apply himage
      rw [← Set.countable_coe_iff]
      let _ : Countable J := hJ.to_subtype
      let gj : R → J := fun b ↦ ⟨g b, Set.mem_range_self b⟩
      exact (show Injective gj from fun b c hbc ↦
        hg_inj (congrArg Subtype.val hbc)).countable
    refine ⟨J, hJsub, hJunc, Or.inr ?_⟩
    rintro x ⟨b, rfl⟩ y ⟨c, rfl⟩ hxy
    exact congrArg g (Subtype.ext ((hgf b).symm.trans (hxy.trans (hgf c))))

/-- The union of all countable relative fibres of a map to a countable type is
countable.  Equivalently, after deleting this set, every surviving fibre is
uncountable. -/
theorem countable_union_of_countable_fibers [Countable β]
    (f : α → β) (I : Set α) :
    {x ∈ I | {y ∈ I | f y = f x}.Countable}.Countable := by
  classical
  let C : β → Set α := fun b ↦
    if {x ∈ I | f x = b}.Countable then {x ∈ I | f x = b} else ∅
  have hC : ∀ b, (C b).Countable := by
    intro b
    by_cases h : {x ∈ I | f x = b}.Countable
    · change (if {x ∈ I | f x = b}.Countable then
          {x ∈ I | f x = b} else ∅).Countable
      rw [if_pos h]
      exact h
    · simp [C, h]
  refine (Set.countable_iUnion hC).mono ?_
  intro x hx
  refine Set.mem_iUnion.2 ⟨f x, ?_⟩
  simp [C, hx.2, hx.1]

/-- Removing a countable set from an uncountable set leaves an uncountable
set. -/
theorem uncountable_sdiff_countable {I C : Set α}
    (hI : ¬ I.Countable) (hC : C.Countable) :
    ¬ (I \ C).Countable := by
  intro hdiff
  apply hI
  exact (hdiff.union hC).mono (Set.subset_sdiff_union I C)

/-- A point can be chosen outside any countable exceptional subset of an
uncountable set. -/
theorem exists_mem_not_mem_of_uncountable_of_countable
    {I C : Set α} (hI : ¬ I.Countable) (hC : C.Countable) :
    ∃ x ∈ I, x ∉ C := by
  by_contra! h
  exact hI (hC.mono h)

/-- Delete precisely the points lying in countable relative fibres.  What
remains is uncountable, and every fibre represented there is uncountable. -/
theorem uncountable_after_deleting_countable_fibers [Countable β]
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ x ∈ J, ¬ {y ∈ I | f y = f x}.Countable := by
  let C : Set α := {x ∈ I | {y ∈ I | f y = f x}.Countable}
  refine ⟨I \ C, fun _ hx ↦ hx.1, ?_, ?_⟩
  · exact uncountable_sdiff_countable hI
      (countable_union_of_countable_fibers f I)
  · intro x hx hxfib
    exact hx.2 ⟨hx.1, hxfib⟩

/-- Lower-countable normalization of an injective map into a well-order.  The
resulting uncountable set has only countably many earlier elements below each
of its members (where earlier is measured after applying `p`). -/
theorem uncountable_lowerNormalized {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {I : Set α} (hI : ¬ I.Countable) (hp : InjOn p I) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ x ∈ J, {y ∈ J | r (p y) (p x)}.Countable := by
  classical
  let P : Set β := p '' I
  let Bad : Set β := {x ∈ P | ¬ {y ∈ P | r y x}.Countable}
  by_cases hBad : Bad.Nonempty
  · let wf : WellFounded r := IsWellFounded.wf
    let m : β := wf.min Bad hBad
    have hmBad : m ∈ Bad := wf.min_mem Bad hBad
    have hmmin : ∀ z ∈ Bad, ¬ r z m := fun z hz ↦
      wf.not_lt_min Bad hz
    let J : Set α := {x ∈ I | r (p x) m}
    have hJsub : J ⊆ I := fun _ hx ↦ hx.1
    have hpred_image : {y ∈ P | r y m} ⊆ p '' J := by
      rintro y ⟨⟨x, hxI, rfl⟩, hxm⟩
      exact ⟨x, ⟨hxI, hxm⟩, rfl⟩
    have hJunc : ¬ J.Countable := by
      intro hJ
      apply hmBad.2
      exact (hJ.image p).mono hpred_image
    refine ⟨J, hJsub, hJunc, ?_⟩
    intro x hxJ
    have hpxP : p x ∈ P := ⟨x, hxJ.1, rfl⟩
    have hpxNotBad : p x ∉ Bad := by
      intro hpxBad
      exact hmmin (p x) hpxBad hxJ.2
    have hpredP : {y ∈ P | r y (p x)}.Countable := by
      by_contra hnot
      exact hpxNotBad ⟨hpxP, hnot⟩
    have himage : (p '' {y ∈ J | r (p y) (p x)}).Countable := by
      refine hpredP.mono ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨⟨y, hJsub hy.1, rfl⟩, hy.2⟩
    exact Set.countable_of_injective_of_countable_image
      (hp.mono fun _ hy ↦ hJsub hy.1) himage
  ·
    refine ⟨I, Set.Subset.rfl, hI, ?_⟩
    intro x hxI
    have hpxP : p x ∈ P := ⟨x, hxI, rfl⟩
    have hpredP : {y ∈ P | r y (p x)}.Countable := by
      by_contra hnot
      exact hBad ⟨p x, hpxP, hnot⟩
    have himage : (p '' {y ∈ I | r (p y) (p x)}).Countable := by
      refine hpredP.mono ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.1, rfl⟩, hy.2⟩
    exact Set.countable_of_injective_of_countable_image
      (hp.mono fun _ hy ↦ hy.1) himage

/-- From two uncountable subsets of a lower-normalized set, choose a cross
pair in the forward well-order orientation. -/
theorem exists_cross_forward {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {D U V : Set α} (hp : InjOn p D)
    (hlower : ∀ x ∈ D, {y ∈ D | r (p y) (p x)}.Countable)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    ∃ u ∈ U, ∃ v ∈ V, r (p u) (p v) := by
  have hUne : U.Nonempty := by
    by_contra hn
    exact hU (Set.not_nonempty_iff_eq_empty.mp hn ▸ Set.countable_empty)
  obtain ⟨u, huU⟩ := hUne
  have hlowerV : {v ∈ V | r (p v) (p u)}.Countable := by
    refine Set.Countable.mono ?_ (hlower u (hUD huU))
    intro v hv
    exact And.intro (hVD hv.1) hv.2
  have hexception : ({v ∈ V | r (p v) (p u)} ∪ {u}).Countable :=
    hlowerV.union (Set.countable_singleton u)
  obtain ⟨v, hvV, hv⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hV hexception
  refine ⟨u, huU, v, hvV, ?_⟩
  have hnvu : v ≠ u := by
    intro hvu
    apply hv
    exact Or.inr hvu
  have hpne : p u ≠ p v := fun huv ↦
    hnvu (hp (hVD hvV) (hUD huU) huv.symm)
  rcases trichotomous_of r (p u) (p v) with huv | huv | hvu
  · exact huv
  · exact (hpne huv).elim
  · exact (hv (Or.inl ⟨hvV, hvu⟩)).elim

/-- Both well-order orientations occur between any two uncountable subsets
of a lower-normalized set. -/
theorem exists_cross_orientations {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {D U V : Set α} (hp : InjOn p D)
    (hlower : ∀ x ∈ D, {y ∈ D | r (p y) (p x)}.Countable)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    (∃ u ∈ U, ∃ v ∈ V, r (p u) (p v)) ∧
      ∃ u ∈ U, ∃ v ∈ V, r (p v) (p u) := by
  constructor
  · exact exists_cross_forward p hp hlower hUD hVD hU hV
  · obtain ⟨v, hv, u, hu, hvu⟩ :=
      exists_cross_forward p hp hlower hVD hUD hV hU
    exact ⟨u, hu, v, hv, hvu⟩

end Erdos965

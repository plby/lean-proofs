import Mathlib

/-!
# Erdős Problem 632: basic definitions and finite-set lemmas

This file contains the palette-polymorphic definition of multiple list
colouring used by the formalization, together with elementary finite-set
lemmas used throughout the Dvořák--Hu--Sereni construction.
-/

namespace Erdos632

open Finset

universe u v

section Coloring

variable {V : Type u} {Color : Type v}

/-- A set-valued proper colouring of a simple graph: adjacent vertices receive
disjoint finite sets of colours. -/
def IsSetColoring (G : SimpleGraph V) (phi : V → Finset Color) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → Disjoint (phi u) (phi v)

/-- A set-valued proper colouring selecting exactly `b` colours from each
assigned list. -/
def IsLMulticoloring (G : SimpleGraph V) (L phi : V → Finset Color) (b : ℕ) : Prop :=
  IsSetColoring G phi ∧ ∀ v, phi v ⊆ L v ∧ (phi v).card = b

/-- `G` is `(a,b)`-choosable if it admits a `b`-fold list colouring for every
assignment of `a`-element finite lists, over every colour palette. -/
def IsABChoosable (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ (Color : Type v) [DecidableEq Color] (L : V → Finset Color),
    (∀ v, (L v).card = a) → ∃ phi, IsLMulticoloring G L phi b

/-- The ordinary notion of a proper list colouring, presented as a function
choosing one colour at each vertex. -/
def IsLColoring (G : SimpleGraph V) (L : V → Finset Color) (c : V → Color) : Prop :=
  (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧ ∀ v, c v ∈ L v

/-- Existence of an ordinary list colouring for the assignment `L`. -/
def HasLColoring (G : SimpleGraph V) (L : V → Finset Color) : Prop :=
  ∃ c, IsLColoring G L c

/-- A graph is ordinarily `a`-choosable if every `a`-list assignment over
every palette has a proper single-colour selection. -/
def IsAChoosable (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ (Color : Type v) [DecidableEq Color] (L : V → Finset Color),
    (∀ v, (L v).card = a) → HasLColoring G L

/-- Singleton-valued multicolourings are exactly ordinary list colourings. -/
lemma isLMulticoloring_singleton_iff (G : SimpleGraph V) (L : V → Finset Color)
    (c : V → Color) :
    IsLMulticoloring G L (fun v ↦ {c v}) 1 ↔ IsLColoring G L c := by
  simp [IsLMulticoloring, IsSetColoring, IsLColoring]

/-- Selecting one colour as a finite set at each vertex is equivalent to
ordinary list colourability. -/
lemma exists_isLMulticoloring_one_iff_hasLColoring (G : SimpleGraph V)
    (L : V → Finset Color) :
    (∃ phi, IsLMulticoloring G L phi 1) ↔ HasLColoring G L := by
  constructor
  · rintro ⟨phi, hphi⟩
    choose c hc using fun v ↦ Finset.card_eq_one.mp (hphi.2 v).2
    refine ⟨c, (isLMulticoloring_singleton_iff G L c).mp ?_⟩
    have hfun : (fun v ↦ {c v}) = phi := funext fun v ↦ (hc v).symm
    rwa [hfun]
  · rintro ⟨c, hc⟩
    exact ⟨fun v ↦ {c v}, (isLMulticoloring_singleton_iff G L c).mpr hc⟩

/-- Consequently, `(a,1)`-choosability is precisely ordinary
`a`-choosability. -/
lemma isABChoosable_one_iff_isAChoosable (G : SimpleGraph V) (a : ℕ) :
    IsABChoosable.{u, v} G a 1 ↔ IsAChoosable.{u, v} G a := by
  constructor
  · intro h Color _ L hL
    rw [← exists_isLMulticoloring_one_iff_hasLColoring]
    exact h Color L hL
  · intro h Color _ L hL
    rw [exists_isLMulticoloring_one_iff_hasLColoring]
    exact h Color L hL

/-- Long-form aliases for clients which prefer the standard terminology. -/
abbrev IsListColoring := @IsLColoring
abbrev HasListColoring := @HasLColoring

end Coloring

section FinsetLemmas

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- A larger finite set contains an element outside a smaller finite set. -/
lemma exists_mem_sdiff_of_card_lt {A F : Finset α} (h : F.card < A.card) :
    ∃ x, x ∈ A ∧ x ∉ F := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) (Finset.card_le_card fun x hx ↦ hn x hx)

/-- Deleting a forbidden set loses no more elements than the size of that
forbidden set. -/
lemma card_sub_card_le_card_sdiff (A F : Finset α) :
    A.card - F.card ≤ (A \ F).card := by
  rw [Finset.card_sdiff]
  exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) A.card

/-- Exact cardinality after deleting a subset. -/
lemma card_sdiff_eq_sub_of_subset {A F : Finset α} (hFA : F ⊆ A) :
    (A \ F).card = A.card - F.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFA]

omit [DecidableEq α] in
/-- A conveniently named wrapper around Mathlib's finite-set thinning lemma. -/
lemma exists_subset_card_eq {A : Finset α} {k : ℕ} (h : k ≤ A.card) :
    ∃ A' ⊆ A, A'.card = k :=
  Finset.exists_subset_card_eq h

omit [DecidableEq α] in
/-- A prescribed colour at the third vertex of a triangle can be extended
from two unequal lists of size at least two. -/
lemma triangle_extend_fixed {A B : Finset α} (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (hAB : A ≠ B) (q : α) :
    ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a ≠ q ∧ b ≠ q := by
  classical
  obtain ⟨a₀, ha₀A, ha₀q⟩ := Finset.exists_mem_ne (lt_of_lt_of_le (by omega) hA) q
  by_cases hgood : ∃ b ∈ B, b ≠ q ∧ b ≠ a₀
  · obtain ⟨b, hbB, hbq, hba₀⟩ := hgood
    exact ⟨a₀, ha₀A, b, hbB, hba₀.symm, ha₀q, hbq⟩
  · have hBsub : B ⊆ {q, a₀} := by
      intro b hbB
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hbq : b = q
      · exact Or.inl hbq
      · exact Or.inr (not_not.mp fun hba₀ ↦ hgood ⟨b, hbB, hbq, hba₀⟩)
    have hpair : ({q, a₀} : Finset α).card = 2 := by simp [Ne.symm ha₀q]
    have hBeq : B = {q, a₀} :=
      Finset.eq_of_subset_of_card_le hBsub (by omega)
    have hAnsub : ¬ A ⊆ B := by
      intro hAsub
      apply hAB
      apply Finset.eq_of_subset_of_card_le hAsub
      rw [hBeq, hpair]
      exact hA
    rw [← Finset.sdiff_nonempty] at hAnsub
    obtain ⟨a, ha⟩ := hAnsub
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have haB : a ∉ B := (Finset.mem_sdiff.mp ha).2
    have ha₀B : a₀ ∈ B := by rw [hBeq]; simp
    have haq : a ≠ q := by
      intro haq
      apply haB
      rw [haq, hBeq]
      simp
    have haa₀ : a ≠ a₀ := by
      intro haa₀
      exact haB (haa₀ ▸ ha₀B)
    exact ⟨a, haA, a₀, ha₀B, haa₀, haq, ha₀q⟩

/-- With a three-element set `A` and a two-element set `B`, at most one
singleton deletion from `A` can equal `B`. -/
lemma card_three_delete_eq_card_two_unique {A B : Finset α}
    (hA : A.card = 3) (hB : B.card = 2) {c d : α}
    (hc : A \ {c} = B) (hd : A \ {d} = B) : c = d := by
  have hcA : c ∈ A := by
    by_contra hcnA
    have hsdiff : A \ {c} = A :=
      (Finset.sdiff_singleton_eq_erase c A).trans (Finset.erase_eq_self.mpr hcnA)
    have hcard := congrArg Finset.card (hsdiff.symm.trans hc)
    omega
  have hdA : d ∈ A := by
    by_contra hdnA
    have hsdiff : A \ {d} = A :=
      (Finset.sdiff_singleton_eq_erase d A).trans (Finset.erase_eq_self.mpr hdnA)
    have hcard := congrArg Finset.card (hsdiff.symm.trans hd)
    omega
  by_contra hcd
  have hdleft : d ∈ A \ {c} := by simp [hdA, Ne.symm hcd]
  have hdinB : d ∈ B := hc ▸ hdleft
  have hdnotB : d ∉ B := by
    rw [← hd]
    simp
  exact hdnotB hdinB

/-- A two-element set of candidate colours cannot consist entirely of bad
deletions from a three-list down to one fixed two-list. -/
lemma exists_delete_ne_of_two_le_card {A B X : Finset α}
    (hA : A.card = 3) (hB : B.card = 2) (hX : 2 ≤ X.card) :
    ∃ c ∈ X, A \ {c} ≠ B := by
  by_contra hn
  push Not at hn
  have hX' : 1 < X.card := by omega
  obtain ⟨c, hcX, d, hdX, hcd⟩ := Finset.one_lt_card.mp hX'
  exact hcd (card_three_delete_eq_card_two_unique hA hB (hn c hcX) (hn d hdX))

/-- Three candidate colours contain one which simultaneously avoids two
bad singleton-deletion conditions. -/
lemma exists_delete_ne_delete_ne_of_three_le_card
    {A₁ B₁ A₂ B₂ X : Finset α}
    (hA₁ : A₁.card = 3) (hB₁ : B₁.card = 2)
    (hA₂ : A₂.card = 3) (hB₂ : B₂.card = 2)
    (hX : 3 ≤ X.card) :
    ∃ c ∈ X, A₁ \ {c} ≠ B₁ ∧ A₂ \ {c} ≠ B₂ := by
  classical
  let D₁ := X.filter fun c ↦ A₁ \ {c} = B₁
  let D₂ := X.filter fun c ↦ A₂ \ {c} = B₂
  have hD₁ : D₁.card ≤ 1 := by
    by_contra hn
    have hlt : 1 < D₁.card := by omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hlt
    exact hcd (card_three_delete_eq_card_two_unique hA₁ hB₁
      (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2)
  have hD₂ : D₂.card ≤ 1 := by
    by_contra hn
    have hlt : 1 < D₂.card := by omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hlt
    exact hcd (card_three_delete_eq_card_two_unique hA₂ hB₂
      (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2)
  by_contra hn
  push Not at hn
  have hsub : X ⊆ D₁ ∪ D₂ := by
    intro c hcX
    simp only [D₁, D₂, Finset.mem_union, Finset.mem_filter]
    by_cases hbad : A₁ \ {c} = B₁
    · exact Or.inl ⟨hcX, hbad⟩
    · exact Or.inr ⟨hcX, hn c hcX hbad⟩
  have hcard : X.card ≤ D₁.card + D₂.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le D₁ D₂)
  omega

/-- Two disjoint two-element sets have a four-element union. -/
lemma card_union_eq_four_of_disjoint_of_card_two {A B : Finset α}
    (hdis : Disjoint A B) (hA : A.card = 2) (hB : B.card = 2) :
    (A ∪ B).card = 4 := by
  rw [Finset.card_union_of_disjoint hdis, hA, hB]

/-- Disjoint two-subsets of a four-element universe partition that universe. -/
lemma union_eq_of_disjoint_of_card_two_of_subset_four {A B U : Finset α}
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hdis : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 2) (hU : U.card = 4) :
    A ∪ B = U := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset hAU hBU
  · rw [card_union_eq_four_of_disjoint_of_card_two hdis hA hB, hU]

/-- In the situation above, either pair is the complement of the other in
the four-element universe. -/
lemma sdiff_eq_of_disjoint_of_card_two_of_subset_four {A B U : Finset α}
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hdis : Disjoint A B)
    (hA : A.card = 2) (hB : B.card = 2) (hU : U.card = 4) :
    U \ A = B := by
  have hunion := union_eq_of_disjoint_of_card_two_of_subset_four
    hAU hBU hdis hA hB hU
  ext x
  constructor
  · intro hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxnotA := (Finset.mem_sdiff.mp hx).2
    have hxunion : x ∈ A ∪ B := by rwa [hunion]
    rcases Finset.mem_union.mp hxunion with hxA | hxB
    · exact False.elim (hxnotA hxA)
    · exact hxB
  · intro hxB
    exact Finset.mem_sdiff.mpr ⟨hBU hxB,
      fun hxA ↦ (Finset.disjoint_left.mp hdis hxA) hxB⟩

end FinsetLemmas

end Erdos632

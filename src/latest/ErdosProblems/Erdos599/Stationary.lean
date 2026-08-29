/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import ErdosProblems.Erdos110.PCF.Background.Club

/-!
# Club and stationary-set tools for Erdős Problem 599

Mathlib's club API is formulated for a well-ordered type.  For a cardinal
`κ`, the type `Below κ = Set.Iio κ.ord` is the canonical type of ordinals
below its initial ordinal.  This file supplies small adapters for that
carrier, records the completeness of the nonstationary ideal, and proves a
pressing-down lemma in the ordinal formulation used by the transfinite part
of the Erdős--Menger argument.

The pressing-down proof uses the diagonal-intersection theorem proved in
`ErdosProblems.Erdos110.PCF.Background.Club`.  Mathlib v4.33.0 contains the
ordinary intersection and union API for clubs and stationary sets, but does
not yet contain diagonal intersections or Fodor's lemma.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Stationary

universe u v

/-- The canonical well-order whose elements are the ordinals below the
initial ordinal of `κ`. -/
abbrev Below (κ : Cardinal.{u}) := Set.Iio κ.ord

/-- Mathlib's club predicate, specialized to the ordinals below `κ`. -/
abbrev IsClubBelow (κ : Cardinal.{u}) (C : Set (Below κ)) : Prop :=
  IsClub C

/-- Mathlib's stationary predicate, specialized to the ordinals below `κ`. -/
abbrev IsStationaryBelow (κ : Cardinal.{u}) (S : Set (Below κ)) : Prop :=
  IsStationary S

/-- Regard a set of ordinals as a set in the subtype of ordinals below `κ`. -/
def restrictBelow (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Set (Below κ) :=
  {a | a.1 ∈ S}

/-- Forget the upper-bound proofs in a set of ordinals below `κ`. -/
def ordinalsOfBelow (κ : Cardinal.{u}) (S : Set (Below κ)) : Set Ordinal.{u} :=
  Subtype.val '' S

@[simp]
theorem mem_restrictBelow {κ : Cardinal.{u}} {S : Set Ordinal.{u}} {a : Below κ} :
    a ∈ restrictBelow κ S ↔ a.1 ∈ S :=
  Iff.rfl

@[simp]
theorem mem_ordinalsOfBelow {κ : Cardinal.{u}} {S : Set (Below κ)} {a : Ordinal.{u}} :
    a ∈ ordinalsOfBelow κ S ↔ ∃ h : a < κ.ord, (⟨a, h⟩ : Below κ) ∈ S := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨ha, hS⟩
    exact ⟨⟨a, ha⟩, hS, rfl⟩

@[simp]
theorem restrictBelow_ordinalsOfBelow {κ : Cardinal.{u}} (S : Set (Below κ)) :
    restrictBelow κ (ordinalsOfBelow κ S) = S := by
  ext a
  change a.1 ∈ Subtype.val '' S ↔ a ∈ S
  constructor
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    simpa [this] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

@[simp]
theorem ordinalsOfBelow_restrictBelow {κ : Cardinal.{u}} (S : Set Ordinal.{u}) :
    ordinalsOfBelow κ (restrictBelow κ S) = S ∩ Set.Iio κ.ord := by
  ext a
  simp [and_comm]

/-- The cofinality of the canonical order below a regular cardinal is the
lift of that cardinal to the universe of `Ordinal`. -/
theorem cof_below_eq_lift {κ : Cardinal.{u}} (hκ : κ.IsRegular) :
    Order.cof (Below κ) = Cardinal.lift.{u + 1, u} κ := by
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hκ.cof_ord]

/-- The canonical order below `κ` has cardinality the lift of `κ`. -/
@[simp]
theorem mk_below (κ : Cardinal.{u}) :
    #(Below κ) = Cardinal.lift.{u + 1, u} κ := by
  rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

/-! ## Club tails, bounded sets, and cardinality -/

/-- Every closed final interval in a linear order is club.  This elementary
fact is useful for turning an upper bound into a witness of
nonstationarity. -/
theorem isClub_Ici {α : Type v} [LinearOrder α] (a : α) :
    IsClub (Set.Ici a) := by
  constructor
  · exact (isUpperSet_Ici a).dirSupClosed
  · intro b
    exact ⟨max a b, le_max_left _ _, le_max_right _ _⟩

/-- A set lying strictly below one point is nonstationary. -/
theorem not_isStationary_of_subset_Iio {α : Type v} [LinearOrder α]
    {S : Set α} {a : α} (hS : S ⊆ Set.Iio a) :
    ¬ IsStationary S := by
  rw [not_isStationary_iff]
  refine ⟨Set.Ici a, isClub_Ici a, Set.disjoint_left.2 ?_⟩
  intro x hxS hax
  exact (not_lt_of_ge hax) (hS hxS)

/-- Every noncofinal subset of a linear order is nonstationary. -/
theorem not_isStationary_of_not_isCofinal {α : Type v} [LinearOrder α]
    {S : Set α} (hS : ¬ IsCofinal S) :
    ¬ IsStationary S := by
  obtain ⟨a, ha⟩ := not_isCofinal_iff.mp hS
  exact not_isStationary_of_subset_Iio (fun x hx ↦ ha x hx)

/-- A stationary subset of a linear order is cofinal. -/
theorem isCofinal_of_isStationary {α : Type v} [LinearOrder α]
    {S : Set α} (hS : IsStationary S) :
    IsCofinal S := by
  by_contra h
  exact not_isStationary_of_not_isCofinal h hS

/-- A set of cardinality below the cofinality of the ambient order is
nonstationary. -/
theorem not_isStationary_of_mk_lt_cof {α : Type v} [LinearOrder α]
    {S : Set α} (hS : #S < Order.cof α) :
    ¬ IsStationary S := by
  intro hstat
  exact hS.2 (Order.cof_le (isCofinal_of_isStationary hstat))

/-- Below a regular cardinal, every set of size less than the cardinal is
nonstationary. -/
theorem not_isStationaryBelow_of_mk_lt {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {S : Set (Below κ)}
    (hS : #S < Cardinal.lift.{u + 1, u} κ) :
    ¬ IsStationaryBelow κ S := by
  apply not_isStationary_of_mk_lt_cof
  simpa [cof_below_eq_lift hκ] using hS

/-- A stationary subset below a regular cardinal has the full cardinality
of that cardinal. -/
theorem mk_eq_lift_of_isStationaryBelow {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {S : Set (Below κ)}
    (hS : IsStationaryBelow κ S) :
    #S = Cardinal.lift.{u + 1, u} κ := by
  apply le_antisymm
  · exact (Cardinal.mk_set_le S).trans_eq (mk_below κ)
  · rw [← cof_below_eq_lift hκ]
    exact Order.cof_le (isCofinal_of_isStationary hS)

/-- A club contains a point weakly above every prescribed point. -/
theorem exists_mem_club_above {κ : Cardinal.{u}} {C : Set (Below κ)}
    (hC : IsClubBelow κ C) (a : Below κ) :
    ∃ b ∈ C, a ≤ b :=
  hC.isCofinal a

/-- A club below a regular cardinal contains a point strictly above every
prescribed point. -/
theorem exists_mem_club_strictlyAbove {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : Set (Below κ)}
    (hC : IsClubBelow κ C) (a : Below κ) :
    ∃ b ∈ C, a < b := by
  have hlim : IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hκ.aleph0_le
  let a' : Below κ := ⟨succ a.1, hlim.succ_lt a.2⟩
  obtain ⟨b, hbC, hab⟩ := hC.isCofinal a'
  exact ⟨b, hbC, (lt_succ a.1).trans_le hab⟩

/-- Closure of a club, exposed with the exact `IsLUB` interface used in
transfinite recursive constructions. -/
theorem mem_club_of_isLUB {κ : Cardinal.{u}} {C D : Set (Below κ)}
    {a : Below κ} (hC : IsClubBelow κ C) (hDC : D ⊆ C)
    (hD : D.Nonempty) (ha : IsLUB D a) :
    a ∈ C :=
  hC.isLUB_mem hDC hD ha

/-- The supremum of fewer than `κ` ordinals below a regular cardinal is
again below its initial ordinal. -/
theorem iSup_lt_ord_of_lt {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {ι : Type u} {f : ι → Ordinal.{u}} (hι : #ι < κ)
    (hf : ∀ i, f i < κ.ord) :
    iSup f < κ.ord := by
  apply Ordinal.iSup_lt_of_lt_cof
  · simpa [hκ.cof_ord] using hι
  · exact hf

/-- The supremum of the successors of fewer than `κ` ordinals below a
regular cardinal is still below its initial ordinal. -/
theorem iSup_add_one_lt_ord_of_lt {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {ι : Type u} {f : ι → Ordinal.{u}} (hι : #ι < κ)
    (hf : ∀ i, f i < κ.ord) :
    iSup (fun i ↦ f i + 1) < κ.ord := by
  apply Ordinal.iSup_add_one_lt_of_lt_cof
  · simpa [hκ.cof_ord] using hι
  · exact hf

/-- Universe-polymorphic form of `iSup_lt_ord_of_lt`. -/
theorem lift_iSup_lt_ord_of_lt {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {ι : Type v} {f : ι → Ordinal.{u}}
    (hι : Cardinal.lift.{u} #ι < Cardinal.lift.{v} κ)
    (hf : ∀ i, f i < κ.ord) :
    iSup f < κ.ord := by
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · have hκ' : (Cardinal.lift.{v} κ).IsRegular := hκ.lift
    rw [Cardinal.lift_ord, hκ'.cof_ord]
    exact hι
  · exact hf

/-- Universe-polymorphic bound for the supremum of successors. -/
theorem lift_iSup_add_one_lt_ord_of_lt {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {ι : Type v} {f : ι → Ordinal.{u}}
    (hι : Cardinal.lift.{u} #ι < Cardinal.lift.{v} κ)
    (hf : ∀ i, f i < κ.ord) :
    iSup (fun i ↦ f i + 1) < κ.ord := by
  apply Ordinal.lift_iSup_add_one_lt_of_lt_cof
  · have hκ' : (Cardinal.lift.{v} κ).IsRegular := hκ.lift
    rw [Cardinal.lift_ord, hκ'.cof_ord]
    exact hι
  · exact hf

/-- The supremum of a set of fewer than `κ` ordinals below `κ.ord` is
still below `κ.ord`. -/
theorem sSup_lt_ord_of_mk_lt {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {S : Set Ordinal.{u}}
    (hS : #S < Cardinal.lift.{u + 1, u} κ)
    (hbelow : ∀ a ∈ S, a < κ.ord) :
    sSup S < κ.ord := by
  apply Ordinal.sSup_lt_of_lt_cof
  · have hκ' : (Cardinal.lift.{u + 1} κ).IsRegular := hκ.lift
    rw [Cardinal.lift_ord, hκ'.cof_ord]
    exact hS
  · exact hbelow

/-- A family of fewer than `κ` elements of `Below κ` has a strict upper
bound in `Below κ`. -/
theorem exists_strictUpperBound_of_mk_lt {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {ι : Type u} (f : ι → Below κ)
    (hι : #ι < κ) :
    ∃ a : Below κ, ∀ i, f i < a := by
  let a : Ordinal.{u} := iSup (fun i ↦ (f i).1 + 1)
  have haκ : a < κ.ord :=
    iSup_add_one_lt_ord_of_lt hκ hι (fun i ↦ (f i).2)
  refine ⟨⟨a, haκ⟩, fun i ↦ ?_⟩
  change (f i).1 < a
  exact (lt_succ (f i).1).trans_le (Ordinal.le_iSup (fun j ↦ (f j).1 + 1) i)

/-- A Mathlib club on `Below κ` gives a club of ordinals below `κ` in the
ordinal formulation. -/
theorem ordinal_isClub_ordinalsOfBelow {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : Set (Below κ)}
    (hC : IsClubBelow κ C) :
    Ordinal.IsClub (ordinalsOfBelow κ C) κ.ord := by
  constructor
  · rw [Ordinal.isClosedBelow_iff]
    intro p hpκ hp
    let p' : Below κ := ⟨p, hpκ⟩
    let d : Set (Below κ) := C ∩ Set.Iio p'
    have hdC : d ⊆ C := Set.inter_subset_left
    have hdne : d.Nonempty := by
      obtain ⟨q, hqC, _hq0, hqp⟩ := hp.forall_lt 0 hp.pos
      obtain ⟨hqκ, hqC'⟩ := mem_ordinalsOfBelow.mp hqC
      exact ⟨⟨q, hqκ⟩, hqC', hqp⟩
    have hdLUB : IsLUB d p' := by
      constructor
      · intro q hq
        exact hq.2.le
      · intro q hq
        by_contra hpq
        have hqp : q.1 < p := lt_of_not_ge hpq
        obtain ⟨r, hrC, hqr, hrp⟩ := hp.forall_lt q.1 hqp
        obtain ⟨hrκ, hrC'⟩ := mem_ordinalsOfBelow.mp hrC
        exact (not_le_of_gt hqr) (hq ⟨hrC', hrp⟩)
    have hpC : p' ∈ C :=
      hC.dirSupClosed hdC hdne (DirectedOn.of_linearOrder d) hdLUB
    exact ⟨p', hpC, rfl⟩
  · rw [Ordinal.isAcc_iff]
    refine ⟨hκ.ord_pos.ne', fun a haκ ↦ ?_⟩
    have hlim : IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
    let a' : Below κ := ⟨succ a, hlim.succ_lt haκ⟩
    obtain ⟨b, hbC, hab⟩ := hC.isCofinal a'
    exact ⟨b.1, ⟨⟨b, hbC, rfl⟩, (lt_succ a).trans_le hab, b.2⟩⟩

/-- Restricting an ordinal club below `κ` gives a Mathlib club on `Below κ`.
The regularity hypothesis is stronger than necessary here, but keeps this
adapter paired with `ordinal_isClub_ordinalsOfBelow`. -/
theorem isClubBelow_restrictBelow {κ : Cardinal.{u}}
    (_hκ : κ.IsRegular) {C : Set Ordinal.{u}}
    (hC : Ordinal.IsClub C κ.ord) :
    IsClubBelow κ (restrictBelow κ C) := by
  constructor
  · intro d hdC hdne _hdDirected a ha
    by_cases had : a ∈ d
    · exact hdC had
    have haAcc : Ordinal.IsAcc a.1 C := by
      rw [Ordinal.isAcc_iff]
      constructor
      · intro ha0
        obtain ⟨b, hb⟩ := hdne
        have hba : b ≤ a := ha.1 hb
        have hba_val : b.1 ≤ a.1 := hba
        have hb0 : b.1 = 0 := le_antisymm (ha0 ▸ hba_val) bot_le
        have hba' : b = a := Subtype.ext (hb0.trans ha0.symm)
        exact had (hba' ▸ hb)
      · intro p hpa
        let p' : Below κ := ⟨p, hpa.trans a.2⟩
        have hex : ∃ b ∈ d, ¬ b ≤ p' := by
          by_contra h
          have hap : a ≤ p' := ha.2 <| by
            intro b hb
            by_contra hbp
            exact h ⟨b, hb, hbp⟩
          exact (not_le_of_gt hpa) hap
        obtain ⟨b, hb, hbp⟩ := hex
        have hp'b : p' < b := lt_of_not_ge hbp
        have hba : b ≤ a := ha.1 hb
        have hba_ne : b ≠ a := fun hba' ↦ had (hba' ▸ hb)
        have hba_lt : b < a := lt_of_le_of_ne hba hba_ne
        exact ⟨b.1, hdC hb, hp'b, hba_lt⟩
    exact hC.mem_of_isAcc a.2 haAcc
  · intro a
    obtain ⟨b, hbC, hab, hbκ⟩ := hC.isAcc.forall_lt a.1 a.2
    exact ⟨⟨b, hbκ⟩, hbC, hab.le⟩

/-- Mathlib stationarity on `Below κ` is equivalent to stationarity of the
corresponding set of ordinals below `κ`. -/
theorem isStationaryBelow_iff_ordinal {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {S : Set (Below κ)} :
    IsStationaryBelow κ S ↔
      Ordinal.IsStationary (ordinalsOfBelow κ S) κ.ord := by
  constructor
  · intro hS C hC
    obtain ⟨a, haS, haC⟩ := hS (isClubBelow_restrictBelow hκ hC)
    exact ⟨a.1, ⟨a, haS, rfl⟩, haC⟩
  · intro hS C hC
    obtain ⟨a, haS, haC⟩ := hS _ (ordinal_isClub_ordinalsOfBelow hκ hC)
    obtain ⟨haκ, haS'⟩ := mem_ordinalsOfBelow.mp haS
    obtain ⟨_haκ', haC'⟩ := mem_ordinalsOfBelow.mp haC
    exact ⟨⟨a, haκ⟩, haS', haC'⟩

/-! ## Completeness of the nonstationary ideal -/

/-- A union of fewer than `cof α` nonstationary sets is nonstationary.

This is the negated form of Mathlib's `isStationary_iUnion_iff`; it is often
the form needed in transfinite constructions. -/
theorem not_isStationary_iUnion_of_lt_cof {α : Type v} [LinearOrder α]
    [WellFoundedLT α] {ι : Type u} {f : ι → Set α}
    (hα : Order.cof α ≠ ℵ₀)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (Order.cof α))
    (hf : ∀ i, ¬ IsStationary (f i)) :
    ¬ IsStationary (⋃ i, f i) := by
  intro h
  rw [isStationary_iUnion_iff hα hι] at h
  obtain ⟨i, hi⟩ := h
  exact hf i hi

/-- A countable union of nonstationary sets is nonstationary whenever the
ambient cofinality is not countable. -/
theorem not_isStationary_iUnion_of_countable {α : Type v} [LinearOrder α]
    [WellFoundedLT α] {ι : Sort u} [Countable ι] {f : ι → Set α}
    (hα : Order.cof α ≠ ℵ₀) (hf : ∀ i, ¬ IsStationary (f i)) :
    ¬ IsStationary (⋃ i, f i) := by
  intro h
  rw [isStationary_iUnion_iff_of_countable hα] at h
  obtain ⟨i, hi⟩ := h
  exact hf i hi

/-- A union of fewer than `cof α` members of a set of nonstationary sets is
nonstationary. -/
theorem not_isStationary_sUnion_of_lt_cof {α : Type v} [LinearOrder α]
    [WellFoundedLT α] {𝒮 : Set (Set α)}
    (hα : Order.cof α ≠ ℵ₀) (h𝒮 : #𝒮 < Order.cof α)
    (hn : ∀ S ∈ 𝒮, ¬ IsStationary S) :
    ¬ IsStationary (⋃₀ 𝒮) := by
  intro h
  rw [isStationary_sUnion_iff hα h𝒮] at h
  obtain ⟨S, hS, hstat⟩ := h
  exact hn S hS hstat

/-- A countable union of nonstationary sets is nonstationary, in `sUnion`
form. -/
theorem not_isStationary_sUnion_of_countable {α : Type v} [LinearOrder α]
    [WellFoundedLT α] {𝒮 : Set (Set α)}
    (hα : Order.cof α ≠ ℵ₀) (h𝒮 : 𝒮.Countable)
    (hn : ∀ S ∈ 𝒮, ¬ IsStationary S) :
    ¬ IsStationary (⋃₀ 𝒮) := by
  intro h
  rw [isStationary_sUnion_iff_of_countable hα h𝒮] at h
  obtain ⟨S, hS, hstat⟩ := h
  exact hn S hS hstat

/-- On the canonical order below a regular uncountable cardinal, fewer than
`κ` nonstationary sets have nonstationary union.  The index type is placed in
the same universe as `Below κ`, which avoids exposing lift bookkeeping to
callers. -/
theorem not_isStationaryBelow_iUnion_of_lt {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκ_uncountable : ℵ₀ < κ)
    {ι : Type (u + 1)} {f : ι → Set (Below κ)}
    (hι : #ι < Cardinal.lift.{u + 1, u} κ)
    (hf : ∀ i, ¬ IsStationaryBelow κ (f i)) :
    ¬ IsStationaryBelow κ (⋃ i, f i) := by
  apply not_isStationary_iUnion_of_lt_cof
  · rw [cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκ_uncountable).ne'
  · simpa [cof_below_eq_lift hκ] using hι
  · exact hf

/-- Countable completeness of the nonstationary ideal below a regular
uncountable cardinal. -/
theorem not_isStationaryBelow_iUnion_of_countable {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκ_uncountable : ℵ₀ < κ)
    {ι : Sort v} [Countable ι] {f : ι → Set (Below κ)}
    (hf : ∀ i, ¬ IsStationaryBelow κ (f i)) :
    ¬ IsStationaryBelow κ (⋃ i, f i) := by
  apply not_isStationary_iUnion_of_countable
  · rw [cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκ_uncountable).ne'
  · exact hf

/-- The `sUnion` form of the completeness of the nonstationary ideal below
a regular uncountable cardinal. -/
theorem not_isStationaryBelow_sUnion_of_lt {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκ_uncountable : ℵ₀ < κ)
    {𝒮 : Set (Set (Below κ))}
    (h𝒮 : #𝒮 < Cardinal.lift.{u + 1, u} κ)
    (hn : ∀ S ∈ 𝒮, ¬ IsStationaryBelow κ S) :
    ¬ IsStationaryBelow κ (⋃₀ 𝒮) := by
  apply not_isStationary_sUnion_of_lt_cof
  · rw [cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκ_uncountable).ne'
  · simpa [cof_below_eq_lift hκ] using h𝒮
  · exact hn

/-- Countable completeness of the nonstationary ideal, in `sUnion` form. -/
theorem not_isStationaryBelow_sUnion_of_countable {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκ_uncountable : ℵ₀ < κ)
    {𝒮 : Set (Set (Below κ))} (h𝒮 : 𝒮.Countable)
    (hn : ∀ S ∈ 𝒮, ¬ IsStationaryBelow κ S) :
    ¬ IsStationaryBelow κ (⋃₀ 𝒮) := by
  apply not_isStationary_sUnion_of_countable
  · rw [cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκ_uncountable).ne'
  · exact h𝒮
  · exact hn

/-- Every countable subset of a regular uncountable cardinal is
nonstationary. -/
theorem not_isStationaryBelow_of_countable {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hκ_uncountable : ℵ₀ < κ)
    {S : Set (Below κ)} (hS : S.Countable) :
    ¬ IsStationaryBelow κ S := by
  apply not_isStationaryBelow_of_mk_lt hκ
  have hcard : #S ≤ ℵ₀ := by
    rwa [le_aleph0_iff_set_countable]
  exact hcard.trans_lt <| by
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact Cardinal.lift_lt.mpr hκ_uncountable

/-! ## Diagonal intersection and pressing down -/

/-- The diagonal intersection of a family of subsets of the canonical order
below `κ`. -/
def diagonalInterBelow {κ : Cardinal.{u}}
    (C : Below κ → Set (Below κ)) : Set (Below κ) :=
  {a | ∀ i, i < a → a ∈ C i}

@[simp]
theorem mem_diagonalInterBelow {κ : Cardinal.{u}}
    {C : Below κ → Set (Below κ)} {a : Below κ} :
    a ∈ diagonalInterBelow C ↔ ∀ i, i < a → a ∈ C i :=
  Iff.rfl

/-- Above the index `i`, the diagonal intersection is contained in the
`i`-th member of the family. -/
theorem diagonalInterBelow_inter_Ioi_subset {κ : Cardinal.{u}}
    (i : Below κ) (C : Below κ → Set (Below κ)) :
    diagonalInterBelow C ∩ Set.Ioi i ⊆ C i := by
  intro a ha
  exact ha.1 i ha.2

/-- The diagonal intersection of a family indexed below an ordinal. -/
abbrev diagonalInter {o : Ordinal} (C : Set.Iio o → Set Ordinal) : Set Ordinal :=
  Ordinal.diagInter C

/-- The ordinal/subtype adapters commute with diagonal intersection. -/
theorem restrictBelow_diagonalInter_ordinalsOfBelow {κ : Cardinal.{u}}
    (C : Below κ → Set (Below κ)) :
    restrictBelow κ
        (diagonalInter (fun i ↦ ordinalsOfBelow κ (C i))) =
      diagonalInterBelow C := by
  ext a
  constructor
  · intro ha i hi
    have hai : a.1 ∈ ordinalsOfBelow κ (C i) := ha i hi
    obtain ⟨_haκ, haiC⟩ := mem_ordinalsOfBelow.mp hai
    simpa only [Subtype.coe_eta] using haiC
  · intro ha i hi
    apply mem_ordinalsOfBelow.mpr
    exact ⟨a.2, ha i hi⟩

/-- The diagonal intersection of clubs below a regular uncountable cardinal
is club.  This is a named adapter around the checked ordinal theorem in the
PCF background library. -/
theorem ordinal_isClub_diagonalInter {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {C : Set.Iio κ.ord → Set Ordinal.{u}}
    (hC : ∀ i, Ordinal.IsClub (C i) κ.ord) :
    Ordinal.IsClub (diagonalInter C) κ.ord :=
  Ordinal.IsClub.diagInter hκ_uncountable hκ hC

/-- The diagonal intersection of clubs on `Below κ` is club. -/
theorem isClubBelow_diagonalInter {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {C : Below κ → Set (Below κ)}
    (hC : ∀ i, IsClubBelow κ (C i)) :
    IsClubBelow κ (diagonalInterBelow C) := by
  have hord : ∀ i, Ordinal.IsClub (ordinalsOfBelow κ (C i)) κ.ord :=
    fun i ↦ ordinal_isClub_ordinalsOfBelow hκ (hC i)
  have hdiag : Ordinal.IsClub
      (diagonalInter (fun i ↦ ordinalsOfBelow κ (C i))) κ.ord :=
    ordinal_isClub_diagonalInter hκ_uncountable hκ hord
  have hrestrict := isClubBelow_restrictBelow hκ hdiag
  rwa [restrictBelow_diagonalInter_ordinalsOfBelow] at hrestrict

/-- **Fodor's pressing-down lemma**, in the ordinal club formulation.

If `S` is stationary below a regular uncountable cardinal and `f` is
regressive on `S`, then one fiber of `f` is stationary. -/
theorem ordinal_pressingDown {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {S : Set Ordinal.{u}} {f : Ordinal.{u} → Ordinal.{u}}
    (hS : Ordinal.IsStationary S κ.ord)
    (hf : ∀ a ∈ S, f a < a) :
    ∃ i : Ordinal.{u}, Ordinal.IsStationary (S ∩ {a | f a = i}) κ.ord := by
  classical
  by_contra h
  have hnonstat : ∀ i : Set.Iio κ.ord,
      ¬ Ordinal.IsStationary (S ∩ {a | f a = i.1}) κ.ord :=
    fun i hi ↦ h ⟨i.1, hi⟩
  have hclub : ∀ i : Set.Iio κ.ord,
      ∃ C : Set Ordinal.{u}, Ordinal.IsClub C κ.ord ∧
        ¬ ((S ∩ {a | f a = i.1}) ∩ C).Nonempty := by
    intro i
    unfold Ordinal.IsStationary at hnonstat
    push Not at hnonstat
    obtain ⟨C, hC, hdisj⟩ := hnonstat i
    exact ⟨C, hC, by simpa only [not_nonempty_iff_eq_empty] using hdisj⟩
  choose C hCclub hCdisj using hclub
  have hdiag : Ordinal.IsClub (diagonalInter C) κ.ord :=
    ordinal_isClub_diagonalInter hκ_uncountable hκ hCclub
  obtain ⟨a, haS, haDiag, haκ⟩ := hS _ hdiag.inter_Iio
  let i : Set.Iio κ.ord := ⟨f a, (hf a haS).trans haκ⟩
  have hai : a ∈ C i := haDiag i (hf a haS)
  exact hCdisj i ⟨a, ⟨haS, rfl⟩, hai⟩

/-- A function on ordinals below `κ` is regressive on `S` if its value is
strictly below its argument at every point of `S`. -/
def IsRegressiveOn {κ : Cardinal.{u}} (S : Set (Below κ))
    (f : Below κ → Below κ) : Prop :=
  ∀ a ∈ S, f a < a

/-- **Fodor's pressing-down lemma**, stated using Mathlib's
`IsStationary` predicate on the canonical order `Below κ`.

The fiber is written as an intersection so that it can be used directly by
the nonstationary-ideal lemmas above. -/
theorem pressingDown {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {S : Set (Below κ)} {f : Below κ → Below κ}
    (hS : IsStationaryBelow κ S) (hf : IsRegressiveOn S f) :
    ∃ i : Below κ, IsStationaryBelow κ (S ∩ {a | f a = i}) := by
  classical
  let F : Ordinal.{u} → Ordinal.{u} := fun a ↦
    if ha : a < κ.ord then (f ⟨a, ha⟩).1 else 0
  have F_eq (a : Ordinal.{u}) (ha : a < κ.ord) :
      F a = (f ⟨a, ha⟩).1 := by
    dsimp only [F]
    rw [dif_pos ha]
  have hSord : Ordinal.IsStationary (ordinalsOfBelow κ S) κ.ord :=
    (isStationaryBelow_iff_ordinal hκ).mp hS
  have hF : ∀ a ∈ ordinalsOfBelow κ S, F a < a := by
    intro a ha
    obtain ⟨haκ, haS⟩ := mem_ordinalsOfBelow.mp ha
    have hreg := hf ⟨a, haκ⟩ haS
    change (f ⟨a, haκ⟩).1 < a at hreg
    rw [F_eq a haκ]
    exact hreg
  obtain ⟨i, hi⟩ := ordinal_pressingDown hκ_uncountable hκ hSord hF
  have hIio : Ordinal.IsClub (Set.Iio κ.ord) κ.ord := by
    simpa only [Set.univ_inter] using
      (Ordinal.isClub_univ (Cardinal.isSuccLimit_ord hκ.aleph0_le)).inter_Iio
  have hiκ : i < κ.ord := by
    obtain ⟨a, ⟨_haS, hFai⟩, haκ⟩ := hi _ hIio
    change F a = i at hFai
    have hfi : (f ⟨a, haκ⟩).1 = i := (F_eq a haκ) ▸ hFai
    exact hfi ▸ (f ⟨a, haκ⟩).2
  let i' : Below κ := ⟨i, hiκ⟩
  refine ⟨i', (isStationaryBelow_iff_ordinal hκ).mpr ?_⟩
  intro C hC
  obtain ⟨a, ⟨haSord, hFai⟩, haC⟩ := hi C hC
  obtain ⟨haκ, haS⟩ := mem_ordinalsOfBelow.mp haSord
  change F a = i at hFai
  have hfi : f ⟨a, haκ⟩ = i' := by
    apply Subtype.ext
    exact (F_eq a haκ) ▸ hFai
  exact ⟨a, mem_ordinalsOfBelow.mpr ⟨haκ, haS, hfi⟩, haC⟩

/-- The domain of an injective regressive map below a regular uncountable
cardinal is nonstationary.

Indeed, pressing down makes the map constant on a stationary subset, while
injectivity makes that subset a singleton; singletons have cardinality below
the cofinality. -/
theorem not_isStationaryBelow_of_injOn_regressive {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {S : Set (Below κ)} {f : Below κ → Below κ}
    (hf : IsRegressiveOn S f) (hinj : Set.InjOn f S) :
    ¬ IsStationaryBelow κ S := by
  intro hS
  obtain ⟨i, hi⟩ := pressingDown hκ_uncountable hκ hS hf
  obtain ⟨a, ha⟩ := hi.nonempty
  have hsub : S ∩ {x | f x = i} ⊆ ({a} : Set (Below κ)) := by
    intro b hb
    have hba : b = a := hinj hb.1 ha.1 (hb.2.trans ha.2.symm)
    simpa [hba]
  have hsingleton : IsStationaryBelow κ ({a} : Set (Below κ)) :=
    hi.mono hsub
  have honeκ : (1 : Cardinal.{u}) < κ :=
    Cardinal.one_lt_aleph0.trans hκ_uncountable
  have hlift : Cardinal.lift.{u + 1, u} (1 : Cardinal.{u}) <
      Cardinal.lift.{u + 1, u} κ :=
    Cardinal.lift_lt.mpr honeκ
  have hsmall : #({a} : Set (Below κ)) <
      Cardinal.lift.{u + 1, u} κ := by
    simpa using hlift
  exact (not_isStationaryBelow_of_mk_lt hκ hsmall) hsingleton

/-- A convenient global-injectivity variant of
`not_isStationaryBelow_of_injOn_regressive`. -/
theorem not_isStationaryBelow_of_injective_regressive {κ : Cardinal.{u}}
    (hκ_uncountable : ℵ₀ < κ) (hκ : κ.IsRegular)
    {S : Set (Below κ)} {f : Below κ → Below κ}
    (hf : IsRegressiveOn S f) (hinj : Function.Injective f) :
    ¬ IsStationaryBelow κ S :=
  not_isStationaryBelow_of_injOn_regressive hκ_uncountable hκ hf hinj.injOn

end Stationary
end Erdos599

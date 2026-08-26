/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Measure algebras as complete Boolean algebras.
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.AEDisjoint
import ErdosProblems.Erdos501.Flypitch4.ToMathlib

set_option relaxedAutoImplicit true

/-!
# Measure algebras

Given a finite measure `μ` on a measurable space `X`, the *measure algebra* of `μ` is the
Boolean algebra of measurable subsets of `X` modulo `μ`-null sets.  It is a classical fact
that this is a *complete* Boolean algebra: it is σ-complete (countable unions of measurable
sets are measurable), and it satisfies the countable chain condition (a family of pairwise
a.e.-disjoint sets of positive measure is countable, because a finite measure cannot contain
uncountably many disjoint sets of measure `> 1/n`), so that arbitrary suprema can be computed
as suprema of countable subfamilies of "essentially maximal measure".

This file constructs the measure algebra `MeasureAlgebra μ` and equips it with a
`NontrivialCompleteBooleanAlgebra` structure (the class used throughout Flypitch for
Boolean-valued models of set theory), and proves that it satisfies `CCC`.

The particular instance used to force `¬CH` is the *random algebra*: the measure algebra of the
product of `ℵ₂` copies of the fair-coin measure on Cantor space, see `RandomAlgebra.lean`.

## Main definitions

* `Flypitch.MeasureAlgebra μ` — measurable sets modulo `μ`-null sets.
* `Flypitch.MeasureAlgebra.mk μ s hs` — the class of a measurable set `s`.
* `Flypitch.MeasureAlgebra.meas` — the measure, descended to the measure algebra.

## Main results

* `Flypitch.MeasureAlgebra.instCompleteBooleanAlgebra` — the measure algebra of a finite measure
  is a complete Boolean algebra.
* `Flypitch.MeasureAlgebra.iSup_mk`, `Flypitch.MeasureAlgebra.iInf_mk` — countable suprema and
  infima are computed by unions and intersections.
* `Flypitch.MeasureAlgebra.CCC_measureAlgebra` — the measure algebra of a finite measure
  satisfies the countable chain condition.
-/

universe u

open MeasureTheory Filter Set Function
open scoped ENNReal Cardinal

namespace Flypitch

variable {X : Type u} [MeasurableSpace X]

/-- The type of measurable subsets of `X`. -/
abbrev MSet (X : Type u) [MeasurableSpace X] : Type u := {s : Set X // MeasurableSet s}

/-- Two measurable sets are equivalent if they differ by a `μ`-null set. -/
def aeSetoid (μ : Measure X) : Setoid (MSet X) where
  r s t := s.1 =ᵐ[μ] t.1
  iseqv := ⟨fun _ => EventuallyEq.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The measure algebra of `μ`: measurable sets modulo `μ`-null sets. -/
def MeasureAlgebra (μ : Measure X) : Type u := Quotient (aeSetoid μ)

namespace MeasureAlgebra

variable {μ : Measure X}

/-- The class of a measurable set in the measure algebra. -/
def mk (μ : Measure X) (s : Set X) (hs : MeasurableSet s) : MeasureAlgebra μ :=
  Quotient.mk (aeSetoid μ) ⟨s, hs⟩

@[elab_as_elim]
protected lemma ind {p : MeasureAlgebra μ → Prop} (h : ∀ s hs, p (mk μ s hs))
    (a : MeasureAlgebra μ) : p a :=
  Quotient.ind (s := aeSetoid μ) (fun x => h x.1 x.2) a

lemma exists_rep (a : MeasureAlgebra μ) : ∃ (s : Set X) (hs : MeasurableSet s), mk μ s hs = a := by
  induction a using MeasureAlgebra.ind with
  | h s hs => exact ⟨s, hs, rfl⟩

lemma mk_eq_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs = mk μ t ht ↔ s =ᵐ[μ] t :=
  Quotient.eq

lemma sound {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} (h : s =ᵐ[μ] t) :
    mk μ s hs = mk μ t ht :=
  Quotient.sound h

/-- `s ≤ᵐ[μ] t` for sets, unfolded to a pointwise a.e. implication. -/
lemma ae_le_set_iff_ae_imp {s t : Set X} : s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl

/-! ### The Boolean algebra structure

We first define the operations on the quotient, and then package them into a single
`BooleanAlgebra` instance (so that all order-theoretic instances on `MeasureAlgebra μ` derive
from one source).
-/

/-- The order on the measure algebra: a.e. inclusion. -/
protected def le' : MeasureAlgebra μ → MeasureAlgebra μ → Prop :=
  Quotient.lift₂ (s₁ := aeSetoid μ) (s₂ := aeSetoid μ) (fun s t => s.1 ≤ᵐ[μ] t.1)
    (fun s t s' t' hs ht => by
      have hs : s.1 =ᵐ[μ] s'.1 := hs
      have ht : t.1 =ᵐ[μ] t'.1 := ht
      exact propext ⟨fun h => hs.symm.le.trans (h.trans ht.le),
        fun h => hs.le.trans (h.trans ht.symm.le)⟩)

/-- Union on the measure algebra. -/
protected def sup' : MeasureAlgebra μ → MeasureAlgebra μ → MeasureAlgebra μ :=
  Quotient.map₂ (sa := aeSetoid μ) (sb := aeSetoid μ) (sc := aeSetoid μ)
    (fun s t => ⟨s.1 ∪ t.1, s.2.union t.2⟩) (fun s s' hs t t' ht => by
      have hs : s.1 =ᵐ[μ] s'.1 := hs
      have ht : t.1 =ᵐ[μ] t'.1 := ht
      exact (hs.union ht : (s.1 ∪ t.1 : Set X) =ᵐ[μ] (s'.1 ∪ t'.1 : Set X)))

/-- Intersection on the measure algebra. -/
protected def inf' : MeasureAlgebra μ → MeasureAlgebra μ → MeasureAlgebra μ :=
  Quotient.map₂ (sa := aeSetoid μ) (sb := aeSetoid μ) (sc := aeSetoid μ)
    (fun s t => ⟨s.1 ∩ t.1, s.2.inter t.2⟩) (fun s s' hs t t' ht => by
      have hs : s.1 =ᵐ[μ] s'.1 := hs
      have ht : t.1 =ᵐ[μ] t'.1 := ht
      exact (hs.inter ht : (s.1 ∩ t.1 : Set X) =ᵐ[μ] (s'.1 ∩ t'.1 : Set X)))

/-- Complement on the measure algebra. -/
protected def compl' : MeasureAlgebra μ → MeasureAlgebra μ :=
  Quotient.map (sa := aeSetoid μ) (sb := aeSetoid μ)
    (fun s => ⟨s.1ᶜ, s.2.compl⟩) (fun s s' hs => by
      have hs : s.1 =ᵐ[μ] s'.1 := hs
      exact (hs.compl : (s.1ᶜ : Set X) =ᵐ[μ] (s'.1ᶜ : Set X)))

private lemma le'_mk_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    MeasureAlgebra.le' (mk μ s hs) (mk μ t ht) ↔ s ≤ᵐ[μ] t := Iff.rfl

private lemma sup'_mk_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    MeasureAlgebra.sup' (mk μ s hs) (mk μ t ht) = mk μ (s ∪ t) (hs.union ht) := rfl

private lemma inf'_mk_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    MeasureAlgebra.inf' (mk μ s hs) (mk μ t ht) = mk μ (s ∩ t) (hs.inter ht) := rfl

private lemma compl'_mk {s : Set X} {hs : MeasurableSet s} :
    MeasureAlgebra.compl' (mk μ s hs) = mk μ sᶜ hs.compl := rfl

noncomputable instance instBooleanAlgebra : BooleanAlgebra (MeasureAlgebra μ) where
  le := MeasureAlgebra.le'
  sup := MeasureAlgebra.sup'
  inf := MeasureAlgebra.inf'
  compl := MeasureAlgebra.compl'
  top := mk μ univ MeasurableSet.univ
  bot := mk μ ∅ MeasurableSet.empty
  sdiff a b := MeasureAlgebra.inf' a (MeasureAlgebra.compl' b)
  himp a b := MeasureAlgebra.sup' b (MeasureAlgebra.compl' a)
  le_refl a := by
    induction a using MeasureAlgebra.ind with
    | h s hs => exact EventuallyLE.rfl
  le_trans a b c hab hbc := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht => induction c using MeasureAlgebra.ind with
        | h u hu => exact (le'_mk_mk.mp hab).trans (le'_mk_mk.mp hbc)
  le_antisymm a b hab hba := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht => exact sound ((le'_mk_mk.mp hab).antisymm (le'_mk_mk.mp hba))
  le_sup_left a b := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht =>
        rw [sup'_mk_mk, le'_mk_mk]
        exact (subset_union_left (s := s) (t := t)).eventuallyLE
  le_sup_right a b := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht =>
        rw [sup'_mk_mk, le'_mk_mk]
        exact (subset_union_right (s := s) (t := t)).eventuallyLE
  sup_le a b c hac hbc := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht => induction c using MeasureAlgebra.ind with
        | h u hu =>
          rw [sup'_mk_mk, le'_mk_mk, ae_le_set_iff_ae_imp]
          rw [le'_mk_mk, ae_le_set_iff_ae_imp] at hac hbc
          filter_upwards [hac, hbc] with x hx₁ hx₂
          rintro (hx | hx)
          · exact hx₁ hx
          · exact hx₂ hx
  inf_le_left a b := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht =>
        rw [inf'_mk_mk, le'_mk_mk]
        exact (inter_subset_left (s := s) (t := t)).eventuallyLE
  inf_le_right a b := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht =>
        rw [inf'_mk_mk, le'_mk_mk]
        exact (inter_subset_right (s := s) (t := t)).eventuallyLE
  le_inf a b c hab hac := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht => induction c using MeasureAlgebra.ind with
        | h u hu =>
          rw [inf'_mk_mk, le'_mk_mk, ae_le_set_iff_ae_imp]
          rw [le'_mk_mk, ae_le_set_iff_ae_imp] at hab hac
          filter_upwards [hab, hac] with x hx₁ hx₂
          exact fun hx => ⟨hx₁ hx, hx₂ hx⟩
  le_sup_inf a b c := by
    induction a using MeasureAlgebra.ind with
    | h s hs => induction b using MeasureAlgebra.ind with
      | h t ht => induction c using MeasureAlgebra.ind with
        | h u hu =>
          show MeasureAlgebra.le' (MeasureAlgebra.inf' (MeasureAlgebra.sup' (mk μ s hs) (mk μ t ht))
            (MeasureAlgebra.sup' (mk μ s hs) (mk μ u hu)))
            (MeasureAlgebra.sup' (mk μ s hs) (MeasureAlgebra.inf' (mk μ t ht) (mk μ u hu)))
          rw [sup'_mk_mk, sup'_mk_mk, inf'_mk_mk, inf'_mk_mk, sup'_mk_mk, le'_mk_mk,
            ae_le_set_iff_ae_imp]
          exact Eventually.of_forall fun x hx => by
            simp only [mem_inter_iff, mem_union] at hx ⊢
            tauto
  inf_compl_le_bot a := by
    induction a using MeasureAlgebra.ind with
    | h s hs =>
      show MeasureAlgebra.le' (MeasureAlgebra.inf' (mk μ s hs) (MeasureAlgebra.compl' (mk μ s hs)))
        (mk μ ∅ MeasurableSet.empty)
      rw [compl'_mk, inf'_mk_mk, le'_mk_mk, ae_le_set_iff_ae_imp]
      exact Eventually.of_forall fun x hx => (hx.2 hx.1).elim
  top_le_sup_compl a := by
    induction a using MeasureAlgebra.ind with
    | h s hs =>
      show MeasureAlgebra.le' (mk μ univ MeasurableSet.univ)
        (MeasureAlgebra.sup' (mk μ s hs) (MeasureAlgebra.compl' (mk μ s hs)))
      rw [compl'_mk, sup'_mk_mk, le'_mk_mk, ae_le_set_iff_ae_imp]
      exact Eventually.of_forall fun x _ => by
        simp only [mem_union, mem_compl_iff]; tauto
  le_top a := by
    induction a using MeasureAlgebra.ind with
    | h s hs =>
      show MeasureAlgebra.le' (mk μ s hs) (mk μ univ MeasurableSet.univ)
      exact (subset_univ s).eventuallyLE
  bot_le a := by
    induction a using MeasureAlgebra.ind with
    | h s hs =>
      show MeasureAlgebra.le' (mk μ ∅ MeasurableSet.empty) (mk μ s hs)
      exact (empty_subset s).eventuallyLE
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

lemma mk_le_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs ≤ mk μ t ht ↔ s ≤ᵐ[μ] t :=
  Iff.rfl

@[simp] lemma mk_sup {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs ⊔ mk μ t ht = mk μ (s ∪ t) (hs.union ht) := rfl

@[simp] lemma mk_inf {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs ⊓ mk μ t ht = mk μ (s ∩ t) (hs.inter ht) := rfl

@[simp] lemma mk_compl {s : Set X} {hs : MeasurableSet s} :
    (mk μ s hs)ᶜ = mk μ sᶜ hs.compl := rfl

lemma top_def : (⊤ : MeasureAlgebra μ) = mk μ univ MeasurableSet.univ := rfl

lemma bot_def : (⊥ : MeasureAlgebra μ) = mk μ ∅ MeasurableSet.empty := rfl

/-! ### The measure on the measure algebra -/

/-- The measure `μ`, descended to the measure algebra. -/
noncomputable def meas (μ : Measure X) : MeasureAlgebra μ → ℝ≥0∞ :=
  Quotient.lift (s := aeSetoid μ) (fun s => μ s.1) (fun _ _ h => measure_congr h)

@[simp] lemma meas_mk {s : Set X} {hs : MeasurableSet s} : meas μ (mk μ s hs) = μ s := rfl

lemma meas_mono {a b : MeasureAlgebra μ} (h : a ≤ b) : meas μ a ≤ meas μ b := by
  induction a using MeasureAlgebra.ind with
  | h s hs => induction b using MeasureAlgebra.ind with
    | h t ht => exact measure_mono_ae (mk_le_mk.mp h)

lemma meas_eq_zero_iff {a : MeasureAlgebra μ} : meas μ a = 0 ↔ a = ⊥ := by
  induction a using MeasureAlgebra.ind with
  | h s hs => rw [meas_mk, bot_def, mk_eq_mk, ae_eq_empty]

lemma le_bot_iff_meas_eq_zero {a : MeasureAlgebra μ} : a ≤ ⊥ ↔ meas μ a = 0 := by
  rw [meas_eq_zero_iff, le_bot_iff]

lemma bot_lt_iff_meas_pos {a : MeasureAlgebra μ} : ⊥ < a ↔ 0 < meas μ a := by
  rw [bot_lt_iff_ne_bot, pos_iff_ne_zero, Ne, Ne, meas_eq_zero_iff]

lemma meas_top : meas μ (⊤ : MeasureAlgebra μ) = μ univ := rfl

/-! ### The countable chain condition -/

/-- The measure algebra of a finite measure satisfies the countable chain condition: any family
of pairwise disjoint nonzero elements is countable. -/
theorem CCC_measureAlgebra [IsFiniteMeasure μ] : CCC (MeasureAlgebra μ) := by
  intro ι 𝓐 h_pos h_disj
  choose s hs hs_eq using fun i => exists_rep (𝓐 i)
  have h_ae_disj : Pairwise (AEDisjoint μ on s) := by
    intro i j hij
    have h := h_disj i j hij
    rw [← hs_eq i, ← hs_eq j, mk_inf, le_bot_iff_meas_eq_zero, meas_mk] at h
    exact h
  have h_count : Set.Countable {i : ι | 0 < μ (s i)} :=
    Measure.countable_meas_pos_of_disjoint_iUnion₀ (fun i => (hs i).nullMeasurableSet) h_ae_disj
  have h_univ : {i : ι | 0 < μ (s i)} = univ := by
    ext i
    simp only [mem_setOf_eq, mem_univ, iff_true]
    have h := h_pos i
    rwa [← hs_eq i, bot_lt_iff_meas_pos, meas_mk] at h
  rw [Cardinal.mk_le_aleph0_iff, ← Set.countable_univ_iff, ← h_univ]
  exact h_count

/-! ### Completeness

For a set `S` of classes, we choose a countable family `T` of representatives of members of `S`
whose union has the largest possible measure; then every member of `S` is a.e. contained in
`⋃ T`, and `⋃ T` is a least upper bound of `S`.
-/

section complete

/-- The measurable representatives of the members of a set of classes. -/
def reps (S : Set (MeasureAlgebra μ)) : Set (MSet X) := {s | mk μ s.1 s.2 ∈ S}

/-- The union of a family of measurable sets. -/
def sUnion' (T : Set (MSet X)) : Set X := ⋃ t ∈ T, t.1

lemma measurableSet_sUnion' {T : Set (MSet X)} (hT : T.Countable) :
    MeasurableSet (sUnion' T) :=
  MeasurableSet.biUnion hT (fun t _ => t.2)

lemma sUnion'_mono {T T' : Set (MSet X)} (h : T ⊆ T') : sUnion' T ⊆ sUnion' T' :=
  biUnion_subset_biUnion_left h

lemma sUnion'_insert (t : MSet X) (T : Set (MSet X)) :
    sUnion' (insert t T) = t.1 ∪ sUnion' T :=
  biUnion_insert t T (fun t : MSet X => t.1)

/-- If every member of a countable family `T` is a.e. below `u`, so is `⋃ T`. -/
lemma sUnion'_ae_le {T : Set (MSet X)} (hT : T.Countable) {u : Set X}
    (h : ∀ t ∈ T, t.1 ≤ᵐ[μ] u) : sUnion' T ≤ᵐ[μ] u := by
  rw [ae_le_set]
  have : sUnion' T \ u = ⋃ t ∈ T, (t.1 \ u) := by
    simp only [sUnion', iUnion_diff]
  rw [this, measure_biUnion_null_iff hT]
  intro t ht
  exact ae_le_set.mp (h t ht)

variable [IsFiniteMeasure μ]

/-- The key lemma: for every set `S` of classes there is a countable family `T` of
representatives of members of `S` such that every member of `S` is a.e. contained in `⋃ T`. -/
theorem exists_countable_essUnion (S : Set (MeasureAlgebra μ)) :
    ∃ T : Set (MSet X), T ⊆ reps S ∧ T.Countable ∧
      ∀ s ∈ reps S, s.1 ≤ᵐ[μ] sUnion' T := by
  classical
  -- the countable subfamilies of `reps S`
  let 𝒞 : Set (Set (MSet X)) := {T | T ⊆ reps S ∧ T.Countable}
  -- the supremum of the measures of their unions
  let m : ℝ≥0∞ := ⨆ T : 𝒞, μ (sUnion' T.1)
  have hm_le : ∀ T ∈ 𝒞, μ (sUnion' T) ≤ m := fun T hT =>
    le_iSup (fun T : 𝒞 => μ (sUnion' T.1)) ⟨T, hT⟩
  -- for every rational `q < m` choose a countable subfamily whose union has measure `> q`
  have hq : ∀ q : ℚ, ∃ T ∈ 𝒞, ((Real.toNNReal q : ℝ≥0∞) < m → (Real.toNNReal q : ℝ≥0∞) <
      μ (sUnion' T)) := by
    intro q
    by_cases hqm : (Real.toNNReal q : ℝ≥0∞) < m
    · obtain ⟨⟨T, hT⟩, hTq⟩ := lt_iSup_iff.mp hqm
      exact ⟨T, hT, fun _ => hTq⟩
    · exact ⟨∅, ⟨empty_subset _, countable_empty⟩, fun h => (hqm h).elim⟩
  choose T hT𝒞 hTq using hq
  -- `U := ⋃ q, T q` is again a countable subfamily
  let U : Set (MSet X) := ⋃ q, T q
  have hU_sub : U ⊆ reps S := iUnion_subset fun q => (hT𝒞 q).1
  have hU_count : U.Countable := countable_iUnion fun q => (hT𝒞 q).2
  have hU𝒞 : U ∈ 𝒞 := ⟨hU_sub, hU_count⟩
  have hU_meas : MeasurableSet (sUnion' U) := measurableSet_sUnion' hU_count
  -- its union has measure exactly `m`
  have hUm : μ (sUnion' U) = m := by
    refine le_antisymm (hm_le U hU𝒞) ?_
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q, -, hq₁, hq₂⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    have h₁ := hTq q hq₂
    have h₂ : μ (sUnion' (T q)) ≤ μ (sUnion' U) :=
      measure_mono (sUnion'_mono (subset_iUnion T q))
    exact absurd (h₁.trans_le h₂) (not_lt.mpr hq₁.le)
  refine ⟨U, hU_sub, hU_count, ?_⟩
  -- every representative is a.e. contained in `⋃ U`: otherwise adding it would increase the
  -- measure beyond `m`
  intro s hs
  rw [ae_le_set]
  by_contra hpos
  have hpos : 0 < μ (s.1 \ sUnion' U) := pos_iff_ne_zero.mpr hpos
  have hU'𝒞 : insert s U ∈ 𝒞 := ⟨insert_subset hs hU_sub, hU_count.insert s⟩
  have h_eq : μ (sUnion' (insert s U)) = μ (sUnion' U) + μ (s.1 \ sUnion' U) := by
    rw [sUnion'_insert, union_comm, ← union_diff_self,
      measure_union disjoint_sdiff_right (s.2.diff hU_meas)]
  have h_lt : μ (sUnion' U) < μ (sUnion' (insert s U)) := by
    rw [h_eq]
    exact ENNReal.lt_add_right (measure_ne_top μ _) hpos.ne'
  exact absurd (hm_le _ hU'𝒞) (not_le.mpr (hUm ▸ h_lt))

/-- A countable family of representatives of `S` whose union is an essential union of `S`. -/
noncomputable def essFamily (S : Set (MeasureAlgebra μ)) : Set (MSet X) :=
  Classical.choose (exists_countable_essUnion S)

lemma essFamily_subset (S : Set (MeasureAlgebra μ)) : essFamily S ⊆ reps S :=
  (Classical.choose_spec (exists_countable_essUnion S)).1

lemma essFamily_countable (S : Set (MeasureAlgebra μ)) : (essFamily S).Countable :=
  (Classical.choose_spec (exists_countable_essUnion S)).2.1

lemma ae_le_sUnion'_essFamily (S : Set (MeasureAlgebra μ)) {s : MSet X} (hs : s ∈ reps S) :
    s.1 ≤ᵐ[μ] sUnion' (essFamily S) :=
  (Classical.choose_spec (exists_countable_essUnion S)).2.2 s hs

/-- The essential union of a set of classes: the supremum in the measure algebra. -/
noncomputable def sSup' (S : Set (MeasureAlgebra μ)) : MeasureAlgebra μ :=
  mk μ (sUnion' (essFamily S)) (measurableSet_sUnion' (essFamily_countable S))

theorem isLUB_sSup' (S : Set (MeasureAlgebra μ)) : IsLUB S (sSup' S) := by
  constructor
  · intro a ha
    induction a using MeasureAlgebra.ind with
    | h s hs => exact mk_le_mk.mpr (ae_le_sUnion'_essFamily S (s := ⟨s, hs⟩) ha)
  · intro b hb
    induction b using MeasureAlgebra.ind with
    | h u hu =>
      apply mk_le_mk.mpr
      apply sUnion'_ae_le (essFamily_countable S)
      intro t ht
      exact mk_le_mk.mp (hb (essFamily_subset S ht))

/-- The infimum, defined via complements. -/
noncomputable def sInf' (S : Set (MeasureAlgebra μ)) : MeasureAlgebra μ :=
  (sSup' ((·ᶜ) '' S))ᶜ

theorem isGLB_sInf' (S : Set (MeasureAlgebra μ)) : IsGLB S (sInf' S) := by
  have h := isLUB_sSup' ((·ᶜ) '' S)
  constructor
  · intro a ha
    exact compl_le_of_compl_le (h.1 (mem_image_of_mem _ ha))
  · intro b hb
    apply le_compl_of_le_compl
    apply h.2
    rintro _ ⟨a, ha, rfl⟩
    exact compl_le_compl (hb ha)

noncomputable instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra (MeasureAlgebra μ) where
  __ := instBooleanAlgebra (μ := μ)
  sSup := sSup'
  isLUB_sSup := isLUB_sSup'
  sInf := sInf'
  isGLB_sInf := isGLB_sInf'

/-- Countable suprema in the measure algebra are computed by unions. -/
theorem iSup_mk {ι : Sort*} [Countable ι] (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    ⨆ i, mk μ (s i) (hs i) = mk μ (⋃ i, s i) (MeasurableSet.iUnion hs) := by
  apply IsLUB.unique isLUB_iSup
  constructor
  · rintro _ ⟨i, rfl⟩
    exact mk_le_mk.mpr (subset_iUnion s i).eventuallyLE
  · intro b hb
    induction b using MeasureAlgebra.ind with
    | h u hu =>
      apply mk_le_mk.mpr
      rw [ae_le_set, iUnion_diff, measure_iUnion_null_iff]
      intro i
      exact ae_le_set.mp (mk_le_mk.mp (hb (mem_range_self i)))

/-- Countable infima in the measure algebra are computed by intersections. -/
theorem iInf_mk {ι : Sort*} [Countable ι] (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    ⨅ i, mk μ (s i) (hs i) = mk μ (⋂ i, s i) (MeasurableSet.iInter hs) := by
  apply IsGLB.unique isGLB_iInf
  constructor
  · rintro _ ⟨i, rfl⟩
    exact mk_le_mk.mpr (iInter_subset s i).eventuallyLE
  · intro b hb
    induction b using MeasureAlgebra.ind with
    | h u hu =>
      apply mk_le_mk.mpr
      rw [ae_le_set, diff_iInter, measure_iUnion_null_iff]
      intro i
      exact ae_le_set.mp (mk_le_mk.mp (hb (mem_range_self i)))

/-- The measure algebra of a probability measure is a nontrivial complete Boolean algebra. -/
noncomputable instance instNontrivialCompleteBooleanAlgebra [IsProbabilityMeasure μ] :
    NontrivialCompleteBooleanAlgebra (MeasureAlgebra μ) where
  __ := instCompleteBooleanAlgebra (μ := μ)
  bot_lt_top := by
    rw [bot_lt_iff_meas_pos, meas_top, measure_univ]
    exact zero_lt_one

end complete

end MeasureAlgebra

end Flypitch

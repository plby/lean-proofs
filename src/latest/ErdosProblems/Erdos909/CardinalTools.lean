import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Cardinal tools for the Anderson--Keisler recursion

The transfinite recursion used in the solution of Erdos problem 909 has length continuum.
At a stage of cardinality `κ < 𝔠`, every new forbidden set is bounded by
`max ℵ₀ κ`.  This file records the elementary cardinal arithmetic behind that observation.
In particular, none of the results below assumes that the continuum is regular.
-/

open Set
open scoped Cardinal

namespace Erdos909

universe u

/-- A canonical well-ordered type of cardinality continuum. -/
abbrev ContinuumIndex : Type u := (Cardinal.continuum.{u}).ord.ToType

theorem mk_continuumIndex : Cardinal.mk (ContinuumIndex.{u}) = Cardinal.continuum := by
  exact Cardinal.mk_ord_toType Cardinal.continuum

/-- Every initial segment of the canonical continuum index has size strictly below continuum. -/
theorem mk_Iio_continuumIndex_lt (i : ContinuumIndex.{u}) :
    Cardinal.mk (Iio i) < Cardinal.continuum := by
  simpa using Cardinal.mk_Iio_lt i (by simp)

/-- A type of cardinality continuum can be enumerated by `ContinuumIndex`. -/
noncomputable def continuumEquiv {α : Type u} (hα : Cardinal.mk α = Cardinal.continuum) :
    ContinuumIndex.{u} ≃ α := by
  apply Classical.choice
  rw [← Cardinal.lift_mk_eq']
  simpa only [Cardinal.lift_id] using (mk_continuumIndex.trans hα.symm)

theorem continuumEquiv_bijective {α : Type u} (hα : Cardinal.mk α = Cardinal.continuum) :
    Function.Bijective (continuumEquiv hα) :=
  (continuumEquiv hα).bijective

/-- Every nonempty type of cardinality at most continuum admits a continuum-length schedule
in which every element occurs. -/
theorem exists_surjective_continuumIndex {α : Type u} [Nonempty α]
    (hα : Cardinal.mk α ≤ Cardinal.continuum) :
    ∃ schedule : ContinuumIndex.{u} → α, Function.Surjective schedule := by
  rw [Function.exists_surjective_iff]
  refine ⟨inferInstance, ?_⟩
  rw [← Cardinal.le_def]
  simpa only [mk_continuumIndex] using hα

/-- `max ℵ₀ κ` is still strictly below continuum when `κ` is. -/
theorem max_aleph0_lt_continuum {κ : Cardinal.{u}} (hκ : κ < Cardinal.continuum) :
    max Cardinal.aleph0 κ < Cardinal.continuum :=
  max_lt Cardinal.aleph0_lt_continuum hκ

/-- Finite words over `α` have cardinality at most `max ℵ₀ #α`, including when `α` is empty. -/
theorem mk_list_le_max_aleph0 (α : Type u) :
    Cardinal.mk (List α) ≤ max Cardinal.aleph0 (Cardinal.mk α) := by
  rw [Cardinal.mk_list_eq_sum_pow]
  exact Cardinal.sum_pow_le_max_aleph0 _

/-- Finite words over a type of cardinality at most `κ` also satisfy the stage bound. -/
theorem mk_list_le_max_aleph0_of_mk_le {α : Type u} {κ : Cardinal.{u}}
    (hα : Cardinal.mk α ≤ κ) :
    Cardinal.mk (List α) ≤ max Cardinal.aleph0 κ :=
  (mk_list_le_max_aleph0 α).trans (max_le_max le_rfl hα)

/-- Finite words over a type smaller than continuum still form a type smaller than continuum. -/
theorem mk_list_lt_continuum {α : Type u} (hα : Cardinal.mk α < Cardinal.continuum) :
    Cardinal.mk (List α) < Cardinal.continuum :=
  (mk_list_le_max_aleph0 α).trans_lt (max_aleph0_lt_continuum hα)

/-- The product of two cardinals bounded by `max ℵ₀ κ` has the same bound. -/
theorem mul_le_max_aleph0 {a b κ : Cardinal.{u}}
    (ha : a ≤ max Cardinal.aleph0 κ) (hb : b ≤ max Cardinal.aleph0 κ) :
    a * b ≤ max Cardinal.aleph0 κ := by
  calc
    a * b ≤ max Cardinal.aleph0 κ * max Cardinal.aleph0 κ := mul_le_mul' ha hb
    _ = max Cardinal.aleph0 κ := Cardinal.mul_eq_self (le_max_left _ _)

/-- A union of at most `max ℵ₀ κ` sets, each of size at most `max ℵ₀ κ`, has that size. -/
theorem mk_iUnion_le_max_aleph0 {α ι : Type u} (f : ι → Set α) {κ : Cardinal.{u}}
    (hι : Cardinal.mk ι ≤ max Cardinal.aleph0 κ)
    (hf : ∀ i, Cardinal.mk (f i) ≤ max Cardinal.aleph0 κ) :
    Cardinal.mk (⋃ i, f i) ≤ max Cardinal.aleph0 κ := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact mul_le_max_aleph0 hι (ciSup_le' hf)

/-- A uniformly `max ℵ₀ κ`-bounded family with at most that many members has union below
continuum when `κ < 𝔠`.  This form allows the individual bad sets to grow with the stage. -/
theorem mk_iUnion_lt_continuum_of_le_max_aleph0 {α ι : Type u} (f : ι → Set α)
    {κ : Cardinal.{u}} (hκ : κ < Cardinal.continuum)
    (hι : Cardinal.mk ι ≤ max Cardinal.aleph0 κ)
    (hf : ∀ i, Cardinal.mk (f i) ≤ max Cardinal.aleph0 κ) :
    Cardinal.mk (⋃ i, f i) < Cardinal.continuum :=
  (mk_iUnion_le_max_aleph0 f hι hf).trans_lt (max_aleph0_lt_continuum hκ)

/-- Convenient specialization: at most `κ` many countable sets have union of size
`≤ max ℵ₀ κ`. -/
theorem mk_iUnion_le_max_aleph0_of_countable {α ι : Type u} (f : ι → Set α)
    {κ : Cardinal.{u}} (hι : Cardinal.mk ι ≤ κ)
    (hf : ∀ i, Cardinal.mk (f i) ≤ Cardinal.aleph0) :
    Cardinal.mk (⋃ i, f i) ≤ max Cardinal.aleph0 κ := by
  apply mk_iUnion_le_max_aleph0 f
  · exact hι.trans (le_max_right _ _)
  · intro i
    exact (hf i).trans (le_max_left _ _)

/-- The preceding union is strictly smaller than continuum whenever `κ < 𝔠`.
This is the precise form used at a stage of the recursion, and does not use regularity of `𝔠`. -/
theorem mk_iUnion_lt_continuum_of_countable {α ι : Type u} (f : ι → Set α)
    {κ : Cardinal.{u}} (hκ : κ < Cardinal.continuum) (hι : Cardinal.mk ι ≤ κ)
    (hf : ∀ i, Cardinal.mk (f i) ≤ Cardinal.aleph0) :
    Cardinal.mk (⋃ i, f i) < Cardinal.continuum :=
  (mk_iUnion_le_max_aleph0_of_countable f hι hf).trans_lt
    (max_aleph0_lt_continuum hκ)

/-- A family of fewer than continuum many countable sets has union smaller than continuum. -/
theorem mk_iUnion_lt_continuum {α ι : Type u} (f : ι → Set α)
    (hι : Cardinal.mk ι < Cardinal.continuum)
    (hf : ∀ i, Cardinal.mk (f i) ≤ Cardinal.aleph0) :
    Cardinal.mk (⋃ i, f i) < Cardinal.continuum :=
  mk_iUnion_lt_continuum_of_countable f hι le_rfl hf

/-- A target set of strictly larger cardinality than a bad set contains a good point. -/
theorem exists_mem_not_mem_of_mk_lt {α : Type u} {bad target : Set α}
    (h : Cardinal.mk bad < Cardinal.mk target) :
    ∃ x, x ∈ target ∧ x ∉ bad := by
  simpa only [Set.nonempty_def, Set.mem_sdiff] using Cardinal.sdiff_nonempty_of_mk_lt_mk h

/-- Selection outside a bad set of size below continuum, from a continuum-sized target. -/
theorem exists_mem_not_mem_of_mk_lt_continuum {α : Type u} {bad target : Set α}
    (hbad : Cardinal.mk bad < Cardinal.continuum)
    (htarget : Cardinal.mk target = Cardinal.continuum) :
    ∃ x, x ∈ target ∧ x ∉ bad :=
  exists_mem_not_mem_of_mk_lt (hbad.trans_eq htarget.symm)

/-- Selection outside a union of at most `κ < 𝔠` countable bad sets. -/
theorem exists_mem_avoid_iUnion_countable {α ι : Type u} (bad : ι → Set α)
    {target : Set α} {κ : Cardinal.{u}} (hκ : κ < Cardinal.continuum)
    (hι : Cardinal.mk ι ≤ κ) (hbad : ∀ i, Cardinal.mk (bad i) ≤ Cardinal.aleph0)
    (htarget : Cardinal.mk target = Cardinal.continuum) :
    ∃ x, x ∈ target ∧ x ∉ ⋃ i, bad i :=
  exists_mem_not_mem_of_mk_lt_continuum
    (mk_iUnion_lt_continuum_of_countable bad hκ hι hbad) htarget

/-- Selection outside a uniformly stage-bounded union. -/
theorem exists_mem_avoid_iUnion_le_max_aleph0 {α ι : Type u} (bad : ι → Set α)
    {target : Set α} {κ : Cardinal.{u}} (hκ : κ < Cardinal.continuum)
    (hι : Cardinal.mk ι ≤ max Cardinal.aleph0 κ)
    (hbad : ∀ i, Cardinal.mk (bad i) ≤ max Cardinal.aleph0 κ)
    (htarget : Cardinal.mk target = Cardinal.continuum) :
    ∃ x, x ∈ target ∧ x ∉ ⋃ i, bad i :=
  exists_mem_not_mem_of_mk_lt_continuum
    (mk_iUnion_lt_continuum_of_le_max_aleph0 bad hκ hι hbad) htarget

/-- At a canonical continuum stage, a union of countable sets indexed by earlier stages is small. -/
theorem mk_iUnion_Iio_continuumIndex_lt_of_countable {α : Type u}
    (i : ContinuumIndex.{u}) (bad : Iio i → Set α)
    (hbad : ∀ j, Cardinal.mk (bad j) ≤ Cardinal.aleph0) :
    Cardinal.mk (⋃ j, bad j) < Cardinal.continuum :=
  mk_iUnion_lt_continuum_of_countable bad (mk_Iio_continuumIndex_lt i) le_rfl hbad

end Erdos909

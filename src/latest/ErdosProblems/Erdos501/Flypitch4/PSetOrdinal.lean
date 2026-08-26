/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/pSet_ordinal.lean (lines 1-500) — Task 6a -/

import ErdosProblems.Erdos501.Flypitch4.ToMathlib
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option relaxedAutoImplicit true

/-!
## Port notes (src/pSet_ordinal.lean → Flypitch4.PSetOrdinal)

### Key API renames

- `tactic.tidy` → `aesop` / `simp` / hand proofs
- `ordinal.limit_rec_on` → `induction η using Ordinal.limitRecOn`
- `ordinal.is_limit` → `Order.IsSuccLimit`
- `ordinal.lt_succ` / `lt_succ_self` → `Order.lt_succ`
- `ordinal.succ η` → `Order.succ η`
- `pSet` → `PSet`; `pSet.equiv` → `PSet.Equiv`; `pSet.mem.mk` → `PSet.Mem.mk`
- `pSet.succ x = insert x x` → `PSet.succ_ord x`
- `ordinal.mk` (Lean 3) → `Ordinal.toPSet` (mathlib4, aliased as `PSet.ordinalMk`)
- `mem_Union` → `PSet.mem_sUnion`
- `Set` (Lean 3 ZFC quotient) → `ZFSet`
- `Set.regularity` → `ZFSet.regularity`
- `push_neg` → `push Not` (deprecated, warning only)
- `ZFSet.not_mem_empty` → `ZFSet.notMem_empty`
- `⟦x⟧ : ZFSet` → `ZFSet.mk x` (more reliable elaboration)
- `typein` (in PSet namespace) → `Ordinal.typein` (fully qualified)
- `PSet.Type ∅ = PEmpty` (not `ULift Empty` as in Lean 3)
- `ordinal.mk_zero_type` etc: adapted to mathlib4 universe conventions

### Namespace choices for 6b, 6c

All declarations in `namespace PSet`.
`ordinalMk = Ordinal.toPSet`.
`succ_ord = insert x x`.
-/

universe u

noncomputable section

-- ============================================================
-- Ordinal namespace: tiny helper
-- ============================================================

namespace Ordinal

lemma lt_zero_false {x : Ordinal} : x < 0 → False :=
  fun h => absurd h (not_lt.mpr (bot_le (a := x)))

end Ordinal

-- ============================================================
-- PSet namespace
-- Lines 30+ of src/pSet_ordinal.lean
-- ============================================================

namespace PSet

-- `ordinalMk η` = `Ordinal.toPSet η` (the von Neumann ordinal as a pre-set).
abbrev ordinalMk : Ordinal.{u} → PSet.{u} := Ordinal.toPSet

-- `succ_ord x = insert x x` — the pre-set ordinal successor.
-- Named `succ_ord` to avoid collision with `Order.succ`.
@[reducible] def succ_ord (x : PSet) : PSet := insert x x

/-! ### Basic structural lemmas -/

lemma powerset_type {x : PSet} : (powerset x).Type = Set (x.Type) := by
  cases x; rfl

@[simp] lemma mem_mk' {x : PSet} {i} : x.Func i ∈ x := PSet.func_mem x i

lemma mem_unfold {x y : PSet} : x ∈ y ↔ ∃ j : y.Type, Equiv x (y.Func j) := by
  cases y; rfl

lemma ext_iff {x y : PSet} : Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  PSet.equiv_iff_mem

lemma mem_mem_false {x y : PSet.{u}} (H₁ : x ∈ y) (H₂ : y ∈ x) : False :=
  PSet.mem_asymm H₂ H₁

@[simp] lemma mem_self {x : PSet.{u}} (H : x ∈ x) : False :=
  PSet.mem_irrefl x H

-- typein of out.r is less than the ordinal itself
lemma typein_lt_type' {ξ : Ordinal} {i : ξ.out.α} :
    @Ordinal.typein _ ξ.out.r ξ.out.wo i < ξ := by
  have h := @Ordinal.typein_lt_type _ ξ.out.r ξ.out.wo i
  -- h : Ordinal.typein ξ.out.r i < Ordinal.type ξ.out.r
  -- Ordinal.type ξ.out.r = ξ (by out_eq: type of the canonical well-order on ξ.ToType = ξ)
  rwa [show Ordinal.type ξ.out.r = ξ from ξ.out_eq] at h

/-! ### Key facts about ordinalMk = Ordinal.toPSet -/

-- The type of `ordinalMk η` is `η.ToType`
@[simp] lemma ordinalMk_type {η : Ordinal} : (ordinalMk η).Type = η.ToType :=
  Ordinal.type_toPSet η

-- Membership characterization (the main tool)
lemma mem_ordinalMk_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk η ↔ ∃ a < η, Equiv x (ordinalMk a) :=
  Ordinal.mem_toPSet_iff

-- Elementary membership
lemma mk_mem_mk_of_lt {ξ η : Ordinal} (H_lt : ξ < η) :
    ordinalMk ξ ∈ ordinalMk η :=
  mem_ordinalMk_iff.mpr ⟨ξ, H_lt, PSet.Equiv.refl _⟩

-- The zero case: ordinalMk 0 ≡ ∅ (extensionally equivalent)
-- Note: this is Equiv, not equality, since Ordinal.ToType 0 ≠ PEmpty definitionally
lemma ordinalMk_zero_equiv : PSet.Equiv (ordinalMk (0 : Ordinal.{u})) (∅ : PSet.{u}) := by
  apply PSet.Mem.ext; intro z
  simp [mem_ordinalMk_iff]

-- For convenience in downstream proofs, state the simp lemma for ZFSet
@[simp] lemma ordinalMk_zero_zfset : ZFSet.mk (ordinalMk (0 : Ordinal.{u})) = ∅ := by
  rw [ZFSet.eq_empty]
  intro y hy
  -- y ∈ ZFSet.mk (ordinalMk 0) means ∃ a < 0, y = ZFSet.mk (ordinalMk a)
  induction y using Quotient.inductionOn with
  | h p =>
    -- ⟦p⟧ = ZFSet.mk p (definitional)
    -- hy : ⟦p⟧ ∈ ZFSet.mk (ordinalMk 0)
    rw [show (⟦p⟧ : ZFSet) = ZFSet.mk p from rfl] at hy
    rw [ZFSet.mk_mem_iff] at hy
    rw [mem_ordinalMk_iff] at hy
    obtain ⟨a, ha, _⟩ := hy
    exact absurd ha (not_lt.mpr (bot_le))

-- For 6b/6c: type of ordinalMk 0 is empty.
-- Note: `Ordinal.ToType 0` is the empty type (mathlib provides
-- `isEmpty_toType_zero`) but it is not definitionally `PEmpty`, so we state
-- the result as `IsEmpty` rather than `= PEmpty`.
lemma ordinalMk_zero_type : IsEmpty (ordinalMk (0 : Ordinal.{u})).Type := by
  rw [ordinalMk_type]
  exact Ordinal.isEmpty_toType_zero

-- Successor: membership in ordinalMk(succ η) ↔ in ordinalMk η or ≡ ordinalMk η
lemma ordinalMk_succ_mem_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk (Order.succ η) ↔ x ∈ ordinalMk η ∨ Equiv x (ordinalMk η) := by
  rw [mem_ordinalMk_iff, mem_ordinalMk_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [Order.lt_succ_iff] at ha
    rcases ha.eq_or_lt with rfl | hlt
    · right; exact heq
    · left; exact ⟨a, hlt, heq⟩
  · rintro (⟨a, ha, heq⟩ | heq)
    · exact ⟨a, ha.trans (Order.lt_succ η), heq⟩
    · exact ⟨η, Order.lt_succ η, heq⟩

-- `succ_ord`: the type is Option
@[simp] lemma succ_ord_type {x : PSet} : (succ_ord x).Type = Option (x.Type) := by
  cases x; rfl

@[simp] lemma option_succ_ord_type {x : PSet} :
    Option (succ_ord x).Type = Option (Option (x.Type)) := by simp

def succ_type_cast {x : PSet} : (succ_ord x).Type → Option (x.Type) := cast succ_ord_type
def succ_type_cast' {x : PSet} : Option (x.Type) → (succ_ord x).Type := cast succ_ord_type.symm

def option_cast' {x : PSet} : Option (Option x.Type) → Option (succ_ord x).Type :=
  cast option_succ_ord_type.symm

@[simp] lemma succ_ord_func_none {x : PSet} :
    (succ_ord x).Func (succ_type_cast' none) = x := by cases x; rfl

@[simp] lemma succ_ord_func_some {x : PSet} {i} :
    (succ_ord x).Func (succ_type_cast' (some i)) = x.Func i := by cases x; rfl

lemma succ_type_forall {x : PSet} {P : (succ_ord x).Type → Prop} :
    (∀ (i : (succ_ord x).Type), P i) = ∀ (i : Option (x.Type)), P (succ_type_cast' i) := by
  cases x; rfl

lemma succ_type_exists {x : PSet} {P : (succ_ord x).Type → Prop} :
    (∃ (i : (succ_ord x).Type), P i) = ∃ (i : Option (x.Type)), P (succ_type_cast' i) := by
  cases x; rfl

lemma option_succ_type_forall {x : PSet} {P : Option (succ_ord x).Type → Prop} :
    (∀ i : Option (succ_ord x).Type, P i) =
    ∀ (i : Option (Option x.Type)), P (option_cast' i) := by
  cases x; rfl

-- The type of ordinalMk for a limit ordinal is η.ToType
@[simp] lemma ordinalMk_limit_type {η : Ordinal} (H_limit : Order.IsSuccLimit η) :
    (ordinalMk η).Type = η.ToType :=
  ordinalMk_type

@[simp] lemma mem_mk_limit_of_lt {η : Ordinal} (_H_limit : Order.IsSuccLimit η)
    (ξ : Ordinal) (Hξ : ξ < η) : ordinalMk ξ ∈ ordinalMk η :=
  mk_mem_mk_of_lt Hξ

/-! ### Epsilon well-orders and pre-set ordinals -/

def epsilon_well_orders (x : PSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (Equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (Equiv u (∅ : PSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : PSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : PSet) : Prop := epsilon_well_orders x ∧ is_transitive x

@[simp] lemma is_transitive_of_Ord {x} (H : Ord x) : is_transitive x := H.right

@[simp] lemma is_ewo_of_Ord {x} (H : Ord x) : epsilon_well_orders x := H.left

@[simp, refl] lemma equiv_refl' {x : PSet} : PSet.Equiv x x := PSet.Equiv.refl _

lemma equiv_of_eq {x y : PSet} : ZFSet.mk x = ZFSet.mk y → PSet.Equiv x y :=
  ZFSet.exact

lemma equiv_iff_eq {x y : PSet} : Equiv x y ↔ ZFSet.mk x = ZFSet.mk y :=
  ⟨ZFSet.sound, ZFSet.exact⟩

-- PSet membership ↔ ZFSet membership
lemma mem_iff {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := by
  simp [ZFSet.mk_mem_iff]

lemma not_mem_iff {x y : PSet} : x ∉ y ↔ ¬ (ZFSet.mk x ∈ ZFSet.mk y) := by
  simp [ZFSet.mk_mem_iff]

lemma mem_sound {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := mem_iff

-- Helpers for insert membership
lemma mem_insert_mem {x y z : PSet} (H : x ∈ insert y z) : Equiv x y ∨ x ∈ z :=
  PSet.mem_insert_iff.mp H

lemma mem_insert_intro {x y z : PSet} (H : Equiv x y ∨ x ∈ z) : x ∈ insert y z :=
  PSet.mem_insert_iff.mpr H

@[simp] lemma mem_succ_ord (x : PSet) : x ∈ succ_ord x :=
  PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))

lemma subset_of_all_mem {x y : PSet} (H : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
  PSet.subset_iff.mpr (fun _ hz => H _ hz)

lemma all_mem_of_subset {x y : PSet} (H : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
  fun z hz => PSet.mem_of_subset H hz

lemma subset_iff_all_mem {x y : PSet} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
  PSet.subset_iff

lemma ZFSet_mem_mk' {x : PSet} {i} : ZFSet.mk (x.Func i) ∈ ZFSet.mk x := by
  rw [← mem_iff]; exact mem_mk' (x := x) (i := i)

lemma mem_trans_of_transitive {x y z : PSet} (H₁ : x ∈ y) (H₂ : y ∈ z)
    (H_trans : is_transitive z) : x ∈ z :=
  all_mem_of_subset (H_trans y H₂) x H₁

lemma empty_empty : (∅ : ZFSet) = ZFSet.mk (∅ : PSet) := rfl

-- Type of empty PSet is PEmpty (mathlib4: `PSet.empty = ⟨_, PEmpty.elim⟩`)
@[simp] lemma empty_type : PSet.Type (∅ : PSet) = PEmpty := by
  rw [PSet.empty_def]; rfl

lemma exists_mem_of_nonempty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) : ∃ y, y ∈ x := by
  by_contra h
  push_neg at h
  exact H (PSet.Mem.ext (fun w => ⟨fun hw => absurd hw (h w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩))

lemma not_empty_of_not_equiv_empty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) :
    ZFSet.mk x ≠ ∅ := by
  intro H'
  apply H
  -- ZFSet.mk x = ∅ = ZFSet.mk ∅, so exact ZFSet.exact H'
  have : ZFSet.mk x = ZFSet.mk (∅ : PSet.{u}) := by
    rw [H']; rfl
  exact ZFSet.exact this

lemma is_epsilon_well_founded (x : PSet.{u}) :
    ∀ (u : PSet.{u}), u ⊆ x → ¬ Equiv u (∅ : PSet.{u}) →
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  intro u _Hu Hu_ne_empty
  classical
  by_contra h
  push_neg at h
  -- h : ∀ y ∈ u, ∃ z ∈ u, z ∈ y
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty Hu_ne_empty
  obtain ⟨y, Hy₁, Hy₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  -- y is a ZFSet with y ∈ ZFSet.mk u and (ZFSet.mk u) ∩ y = ∅
  -- Get a PSet representative: y.out is a PSet with ZFSet.mk y.out = y
  have Hy₁' : y.out ∈ u := by
    have : ZFSet.mk y.out ∈ ZFSet.mk u := by
      rw [ZFSet.mk_out y]; exact Hy₁
    exact mem_iff.mpr this
  obtain ⟨z, Hz₁, Hz₂⟩ := h y.out Hy₁'
  -- z ∈ u and z ∈ y.out → contradiction since ZFSet.mk u ∩ y = ∅
  apply ZFSet.notMem_empty (ZFSet.mk z)
  rw [← Hy₂]
  apply ZFSet.mem_inter.mpr
  exact ⟨mem_iff.mp Hz₁, by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz₂⟩

@[simp] lemma Ord_empty : Ord (∅ : PSet.{u}) := by
  refine ⟨⟨fun y hy => absurd hy (PSet.notMem_empty y), ?_⟩,
    fun y hy => absurd hy (PSet.notMem_empty y)⟩
  intro u Hu H₂
  exact absurd (PSet.Mem.ext (fun w => ⟨
    fun hw => absurd (all_mem_of_subset Hu w hw) (PSet.notMem_empty w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩)) H₂

lemma well_founded (u : PSet.{u}) (H_nonempty : ¬ Equiv u (∅ : PSet.{u})) :
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty H_nonempty
  obtain ⟨y, H₁, H₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  refine ⟨y.out, ?_, ?_⟩
  · have : ZFSet.mk y.out ∈ ZFSet.mk u := by rw [ZFSet.mk_out y]; exact H₁
    exact mem_iff.mpr this
  · intro z' Hz' Hz''
    apply ZFSet.notMem_empty (ZFSet.mk z')
    rw [← H₂]
    exact ZFSet.mem_inter.mpr
      ⟨mem_iff.mp Hz', by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz''⟩

lemma transitive_succ_ord (x : PSet) (H : is_transitive x) : is_transitive (succ_ord x) := by
  intro y Hy
  rcases mem_insert_mem Hy with heq | hin
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr ((PSet.Mem.congr_right heq).mp hz))
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr (all_mem_of_subset (H y hin) z hz))

@[simp] lemma Ord_succ_ord (x : PSet) (H : Ord x) : Ord (succ_ord x) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y Hy z Hz
    rcases mem_insert_mem Hy with heq1 | hin1 <;>
    rcases mem_insert_mem Hz with heq2 | hin2
    · left; exact PSet.Equiv.trans heq1 heq2.symm
    · right; right; exact (PSet.Mem.congr_right heq1).mpr hin2
    · right; left; exact (PSet.Mem.congr_right heq2).mpr hin1
    · exact H.left.left y hin1 z hin2
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · exact transitive_succ_ord x H.right

lemma ordinalMk_lt_of_mem {ξ η : Ordinal} (H : ordinalMk ξ ∈ ordinalMk η) : ξ < η := by
  rw [mem_ordinalMk_iff] at H
  obtain ⟨a, ha, heq⟩ := H
  rcases lt_trichotomy ξ a with h | rfl | h
  · exact h.trans ha
  · exact ha
  · exfalso
    have h1 : ordinalMk a ∈ ordinalMk ξ := mk_mem_mk_of_lt h
    -- heq : Equiv (ordinalMk ξ) (ordinalMk a)
    -- Mem.congr_right heq : ∀ {w}, w ∈ ordinalMk ξ ↔ w ∈ ordinalMk a
    have h2 : ordinalMk a ∈ ordinalMk a := (PSet.Mem.congr_right heq).mp h1
    exact PSet.mem_irrefl _ h2

lemma transitive_Union (x : PSet) (H : ∀ y ∈ x, is_transitive y) : is_transitive (⋃₀ x) := by
  intro z Hz
  apply subset_of_all_mem; intro w Hw
  rw [PSet.mem_sUnion] at Hz ⊢
  obtain ⟨y, Hy, Hz'⟩ := Hz
  exact ⟨y, Hy, all_mem_of_subset (H y Hy z Hz') w Hw⟩

lemma equiv_mk_of_mem_mk {η : Ordinal} :
    ∀ x, x ∈ ordinalMk η → ∃ ρ < η, Equiv x (ordinalMk ρ) :=
  fun x hx => mem_ordinalMk_iff.mp hx

lemma Ord_limit : ∀ (o : Ordinal), Order.IsSuccLimit o →
    (∀ (o' : Ordinal), o' < o → Ord (ordinalMk o')) → Ord (ordinalMk o) := by
  intro η _Hη _ih
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x Hx z Hz
    obtain ⟨ξ₁, H₁, H₂⟩ := equiv_mk_of_mem_mk x Hx
    obtain ⟨ξ₂, H₁', H₂'⟩ := equiv_mk_of_mem_mk z Hz
    rcases lt_trichotomy ξ₁ ξ₂ with hlt | rfl | hlt
    · right; left
      rw [PSet.Mem.congr_left H₂, PSet.Mem.congr_right H₂']
      exact mk_mem_mk_of_lt hlt
    · left; exact PSet.Equiv.trans H₂ H₂'.symm
    · right; right
      rw [PSet.Mem.congr_right H₂, PSet.Mem.congr_left H₂']
      exact mk_mem_mk_of_lt hlt
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · intro y Hy
    obtain ⟨ρ, Hρ, Heq⟩ := equiv_mk_of_mem_mk y Hy
    rw [PSet.Subset.congr_left Heq]
    apply subset_of_all_mem; intro z Hz
    obtain ⟨σ, Hσ, Heq'⟩ := equiv_mk_of_mem_mk z Hz
    rw [PSet.Mem.congr_left Heq']
    exact mk_mem_mk_of_lt (Hσ.trans Hρ)

-- Ord is invariant under PSet.Equiv
lemma Ord_equiv {x y : PSet.{u}} (hxy : PSet.Equiv x y) (hx : Ord x) : Ord y := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- trichotomy: a ∈ y, b ∈ y → a and b are trichotomous
    intro a Ha b Hb
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    have Hb' : b ∈ x := (PSet.Mem.congr_right hxy.symm).mp Hb
    exact hx.left.left a Ha' b Hb'
  · -- well-foundedness
    intro u _Hu H_ne; exact well_founded u H_ne
  · -- transitivity: a ∈ y → a ⊆ y
    intro a Ha
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    -- a ⊆ x (from hx.right)
    have hax : a ⊆ x := hx.right a Ha'
    -- a ⊆ y: for w ∈ a, w ∈ x, so w ∈ y
    apply subset_of_all_mem
    intro w Hw
    exact (PSet.Mem.congr_right hxy).mp (all_mem_of_subset hax w Hw)

-- Key: ordinalMk (Order.succ η) ≡ succ_ord (ordinalMk η)
lemma ordinalMk_succ_equiv {η : Ordinal} :
    PSet.Equiv (ordinalMk (Order.succ η)) (succ_ord (ordinalMk η)) := by
  apply PSet.Mem.ext; intro z
  rw [ordinalMk_succ_mem_iff, PSet.mem_insert_iff]
  tauto

@[simp] lemma Ord_mk (η : Ordinal) : Ord (ordinalMk η) := by
  induction η using Ordinal.limitRecOn with
  | zero => exact Ord_equiv ordinalMk_zero_equiv.symm Ord_empty
  | add_one η ih =>
    -- ordinalMk_succ_equiv : Equiv (ordinalMk (succ η)) (succ_ord (ordinalMk η))
    -- Ord_succ_ord _ ih : Ord (succ_ord (ordinalMk η))
    -- Apply Ord_equiv in reverse: Equiv y x → Ord y → Ord x
    rw [Ordinal.add_one_eq_succ]
    exact Ord_equiv ordinalMk_succ_equiv.symm (Ord_succ_ord _ ih)
  | limit η H_limit ih => exact Ord_limit η H_limit ih

lemma mem_mem_mem_false {x y z : PSet.{u}} (H₁ : x ∈ y) (H₂ : y ∈ z) (H₃ : z ∈ x) : False := by
  -- Use the ZFSet regularity axiom on {⟦x⟧, ⟦y⟧, ⟦z⟧}
  set S : ZFSet := {ZFSet.mk x, ZFSet.mk y, ZFSet.mk z}
  have H_nonempty : S ≠ ∅ := by
    intro h
    have hmem : ZFSet.mk x ∈ S := by simp [S]
    exact ZFSet.notMem_empty _ (h ▸ hmem)
  obtain ⟨w, Hw₁, Hw₂⟩ := ZFSet.regularity S H_nonempty
  -- w ∈ S and S ∩ w = ∅
  simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, S] at Hw₁
  -- In each case, find an element in S ∩ w to get contradiction with Hw₂
  have contradiction : ∃ q, q ∈ S ∩ w := by
    rcases Hw₁ with rfl | rfl | rfl
    · -- w = mk x, need q ∈ {mk x, mk y, mk z} ∩ mk x
      -- q = mk z works since H₃ : z ∈ x
      exact ⟨ZFSet.mk z, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₃⟩⟩
    · -- w = mk y, need q ∈ {mk x, mk y, mk z} ∩ mk y
      -- q = mk x works since H₁ : x ∈ y
      exact ⟨ZFSet.mk x, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₁⟩⟩
    · -- w = mk z, need q ∈ {mk x, mk y, mk z} ∩ mk z
      -- q = mk y works since H₂ : y ∈ z
      exact ⟨ZFSet.mk y, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₂⟩⟩
  obtain ⟨q, hq⟩ := contradiction
  exact ZFSet.notMem_empty q (Hw₂ ▸ hq)

def mem_witness {y w : PSet.{u}} (H : w ∈ y) : Σ' (y_a : y.Type), (Equiv w (y.Func y_a)) := by
  rw [PSet.mem_def] at H
  obtain ⟨a, ha⟩ := Classical.indefiniteDescription _ H
  exact ⟨a, ha⟩

lemma transitive_of_mem_Ord (y x : PSet.{u}) (H : Ord x) (H_mem : y ∈ x) : is_transitive y := by
  intro w Hw
  apply subset_of_all_mem; intro z Hz
  have H_w_in_x : w ∈ x := all_mem_of_subset (H.right y H_mem) w Hw
  have H_z_in_x : z ∈ x := all_mem_of_subset (H.right w H_w_in_x) z Hz
  by_contra hzny
  rcases H.left.left y H_mem z H_z_in_x with heq | hin | hin
  · -- heq : Equiv y z, Hw : w ∈ y, Hz : z ∈ w → w ∈ z → w ∈ w contradiction
    exact mem_mem_false ((PSet.Mem.congr_right heq).mp Hw) Hz
  · -- hin : y ∈ z, Hz : z ∈ w, Hw : w ∈ y → cycle y ∈ z, z ∈ w, w ∈ y
    exact mem_mem_mem_false hin Hz Hw
  · -- hin : z ∈ y, but hzny : z ∉ y
    exact hzny hin

lemma mk_equiv_of_eq {β₁ β₂ : Ordinal.{u}} (H : β₁ = β₂) :
    Equiv (ordinalMk β₁) (ordinalMk β₂) := H ▸ PSet.Equiv.refl _

lemma mk_mem_succ {η : Ordinal.{u}} : ordinalMk η ∈ ordinalMk (Order.succ η) :=
  mk_mem_mk_of_lt (Order.lt_succ η)

lemma subset_Union {x y : PSet.{u}} (H : y ∈ x) : y ⊆ ⋃₀ x :=
  subset_of_all_mem fun z Hz => PSet.mem_sUnion.mpr ⟨y, H, Hz⟩

-- card_ex: cardinal → PSet via ordinal
def card_ex : Cardinal.{u} → PSet.{u} := fun κ => ordinalMk (Cardinal.ord κ)

-- WARNING: is_func corresponds to bSet.is_function, not bSet.is_func
-- f ⊆ prod x y ∧ ∀z ∈ x, ∃! w, pair z w ∈ f
@[reducible] def is_func (x y f : PSet.{u}) : Prop :=
  ZFSet.IsFunc (ZFSet.mk x) (ZFSet.mk y) (ZFSet.mk f)

@[reducible] def is_weak_func (x y f : PSet.{u}) : Prop :=
  ∀ z, z ∈ ZFSet.mk x → ∃! w, w ∈ ZFSet.mk y ∧ ZFSet.pair z w ∈ ZFSet.mk f

@[reducible] def is_extensional (f : PSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂,
    ZFSet.pair (ZFSet.mk w₁) (ZFSet.mk v₁) ∈ ZFSet.mk f →
    ZFSet.pair (ZFSet.mk w₂) (ZFSet.mk v₂) ∈ ZFSet.mk f →
    Equiv w₁ w₂ → Equiv v₁ v₂

@[reducible] def is_surj (x y f : PSet.{u}) : Prop :=
  ∀ b : PSet.{u}, b ∈ y →
    ∃ a : PSet.{u}, a ∈ x ∧ ZFSet.pair (ZFSet.mk a) (ZFSet.mk b) ∈ ZFSet.mk f

-- ============================================================
-- Task 6b additions: lines 512-1000 of src/pSet_ordinal.lean
-- ============================================================

/-! ### Injectivity of ordinalMk (src lines 512-618) -/

/-- Helper: structural equation for `Ordinal.toPSet`. The `eq_def` form. -/
lemma ordinalMk_eq_def (o : Ordinal.{u}) :
    ordinalMk o = ⟨o.ToType, fun a : o.ToType => ordinalMk a.toOrd.val⟩ :=
  Ordinal.toPSet.eq_def o

/-- Injectivity: `ordinalMk η₁ ≡ ordinalMk η₂` → `η₁ = η₂`.
    Port of `eq_of_mk_equiv` (src/pSet_ordinal.lean:604). -/
lemma eq_of_mk_equiv {η₁ η₂ : Ordinal} (H_equiv : Equiv (ordinalMk η₁) (ordinalMk η₂)) :
    η₁ = η₂ := by
  refine le_antisymm ?_ ?_
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₂ < η₁ (from not_lt of η₁ ≤ η₂)
    -- H_mem : ordinalMk η₂ ∈ ordinalMk η₁
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Want: ordinalMk η₁ ∈ ordinalMk η₁
    -- Mem.congr_left H_equiv : ordinalMk η₁ ∈ w ↔ ordinalMk η₂ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₂ ∈ ordinalMk η₁) gives ordinalMk η₁ ∈ ordinalMk η₁
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv).mpr H_mem)
  · rw [← not_lt]; intro H_lt
    -- H_lt : η₁ < η₂ (from not_lt of η₂ ≤ η₁)
    have H_mem := mk_mem_mk_of_lt H_lt
    -- Mem.congr_left H_equiv.symm : ordinalMk η₂ ∈ w ↔ ordinalMk η₁ ∈ w
    -- .mpr H_mem (H_mem : ordinalMk η₁ ∈ ordinalMk η₂) gives ordinalMk η₂ ∈ ordinalMk η₂
    exact PSet.mem_irrefl _ ((PSet.Mem.congr_left H_equiv.symm).mpr H_mem)

/-- The func of ordinalMk η at distinct indices gives inequivalent pSets.
    Port of `ordinal.mk_inj` (src/pSet_ordinal.lean:595). -/
lemma ordinalMk_inj (η : Ordinal.{u}) :
    ∀ (i j : (ordinalMk η).Type), i ≠ j →
      ¬ Equiv ((ordinalMk η).Func i) ((ordinalMk η).Func j) := by
  intro i j hij heq
  apply hij
  -- Extract the HEq characterization of `(ordinalMk η).Func`.
  have hfunc : HEq (ordinalMk η).Func
      (fun a : η.ToType => ordinalMk a.toOrd.val) := by
    rw [ordinalMk_eq_def]; rfl
  -- Type equality.
  have htype : (ordinalMk η).Type = η.ToType := ordinalMk_type
  -- Cast i, j to η.ToType.
  let i' : η.ToType := cast htype i
  let j' : η.ToType := cast htype j
  have hi : HEq i i' := (cast_heq htype i).symm
  have hj : HEq j j' := (cast_heq htype j).symm
  -- `congr_heq` produces `Eq` directly when applied to a `Pi` and a `Sigma` of HEq.
  have heqi : (ordinalMk η).Func i = ordinalMk i'.toOrd.val :=
    congr_heq hfunc hi
  have heqj : (ordinalMk η).Func j = ordinalMk j'.toOrd.val :=
    congr_heq hfunc hj
  rw [heqi, heqj] at heq
  -- heq : Equiv (ordinalMk i'.toOrd.val) (ordinalMk j'.toOrd.val)
  have h_ord_eq : i'.toOrd.val = j'.toOrd.val := eq_of_mk_equiv heq
  have h_toOrd : i'.toOrd = j'.toOrd := Subtype.ext h_ord_eq
  have h_inj : i' = j' :=
    Ordinal.ToType.mk.symm.injective h_toOrd
  -- Cast both back.
  have : (cast htype.symm (cast htype i) : (ordinalMk η).Type) =
         cast htype.symm (cast htype j) :=
    congrArg (cast htype.symm) h_inj
  simpa using this

lemma eq_iff_mk_eq {η₁ η₂ : Ordinal} :
    η₁ = η₂ ↔ Equiv (ordinalMk η₁) (ordinalMk η₂) :=
  ⟨fun h => mk_equiv_of_eq h, fun h => eq_of_mk_equiv h⟩

/-! ### Cardinal type size lemmas (src lines 620-666) -/

open Cardinal in
/-- The cardinality of `(ordinalMk (κ.ord)).Type` equals `κ`, for infinite `κ`.
    Port of `mk_type_mk_eq` (src/pSet_ordinal.lean:620). -/
lemma mk_type_mk_eq (κ : Cardinal) (H_inf : ℵ₀ ≤ κ) :
    Cardinal.mk (ordinalMk (Cardinal.ord κ)).Type = κ := by
  simp only [ordinalMk_type]
  exact Cardinal.mk_ord_toType κ

open Cardinal in
@[simp] lemma mk_type_mk_eq' (κ : Cardinal) (H_inf : ℵ₀ < κ) :
    Cardinal.mk (ordinalMk (Cardinal.ord κ)).Type = κ :=
  mk_type_mk_eq _ H_inf.le

open Cardinal in
@[simp] lemma mk_type_mk_eq'' {κ : Cardinal} {H_inf : ℵ₀ ≤ κ} :
    Cardinal.mk (card_ex κ).Type = κ :=
  mk_type_mk_eq κ H_inf

open Cardinal in
@[simp] lemma mk_type_mk_eq''' {κ : Cardinal} {H_inf : ℵ₀ < κ} :
    Cardinal.mk (card_ex κ).Type = κ :=
  mk_type_mk_eq _ H_inf.le

open Cardinal in
@[simp] lemma mk_type_mk_eq'''' {k : Ordinal} :
    Cardinal.mk (ordinalMk (Cardinal.aleph k).ord).Type = Cardinal.aleph k :=
  mk_type_mk_eq _ (Cardinal.aleph0_le_aleph k)

open Cardinal in
@[simp] lemma mk_type_mk_eq''''' {k : Ordinal} :
    Cardinal.mk (card_ex (Cardinal.aleph k)).Type = Cardinal.aleph k := by
  simp [card_ex]

open Cardinal in
/-- The cardinality of `(ordinalMk η).Type` is `η.card`.
    Port of `ordinal.mk_card` (src/pSet_ordinal.lean:645). -/
lemma ordinalMk_card {η : Ordinal} : Cardinal.mk (ordinalMk η).Type = η.card := by
  simp [ordinalMk_type, Cardinal.mk_toType]

open Cardinal in
lemma zero_aleph : ℵ₀ = Cardinal.aleph 0 := by simp

open Cardinal in
@[simp] lemma mk_type_omega_eq :
    Cardinal.mk (ordinalMk (Cardinal.aleph0.ord)).Type = ℵ₀ :=
  mk_type_mk_eq _ le_rfl

open Cardinal in
@[simp] lemma mk_omega_eq_mk_omega :
    Cardinal.mk (PSet.omega).Type = ℵ₀ := by
  simp only [PSet.omega]
  rw [show (⟨ULift ℕ, fun n => PSet.ofNat n.down⟩ : PSet).Type = ULift ℕ from rfl]
  simp [Cardinal.mk_uLift, Cardinal.mk_nat]

/-! ### Ordinal arithmetic helpers (src lines 668-697) -/

open Cardinal in
lemma two_eq_succ_one : (2 : Ordinal) = Order.succ 1 := by
  rw [Order.succ_eq_add_one]
  norm_cast

open Cardinal in
lemma add_one_lt_add_one {a b : Ordinal} : a < b ↔ a + 1 < b + 1 := by
  simp

open Cardinal in
lemma one_lt_two : (1 : Ordinal) < 2 := _root_.one_lt_two

open Cardinal in
lemma aleph_two_eq_succ_aleph_one :
    Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
  -- succ_aleph : Order.succ (aleph o) = aleph (o + 1)
  -- so aleph (1 + 1) = aleph 2 and Order.succ (aleph 1) = aleph (1 + 1)
  have h2 : (2 : Ordinal) = 1 + 1 := two_eq_succ_one ▸ (Order.succ_eq_add_one 1).symm
  rw [h2, ← Cardinal.succ_aleph]

open Cardinal in
lemma aleph_one_eq_succ_aleph_zero :
    Cardinal.aleph 1 = Order.succ ℵ₀ := by
  exact Cardinal.succ_aleph0.symm

open Cardinal in
lemma is_regular_aleph_one : Cardinal.IsRegular (Cardinal.aleph 1) := by
  rw [aleph_one_eq_succ_aleph_zero]
  exact Cardinal.isRegular_succ le_rfl

open Cardinal in
lemma is_regular_aleph_two : Cardinal.IsRegular (Cardinal.aleph 2) := by
  rw [aleph_two_eq_succ_aleph_one]
  exact Cardinal.isRegular_succ (Cardinal.aleph0_le_aleph 1)

open Cardinal in
@[simp] lemma omega_lt_aleph_one : ℵ₀ < Cardinal.aleph 1 :=
  Cardinal.aleph0_lt_aleph_one

open Cardinal in
@[simp] lemma aleph_one_lt_aleph_two : Cardinal.aleph 1 < Cardinal.aleph 2 :=
  Cardinal.aleph_lt_aleph.mpr one_lt_two

open Cardinal in
@[simp] lemma omega_lt_aleph_two : ℵ₀ < Cardinal.aleph 2 :=
  omega_lt_aleph_one.trans aleph_one_lt_aleph_two

/-! ### Subset helpers (src lines 698-704) -/

lemma subset_trans {x y z : PSet} : x ⊆ y → y ⊆ z → x ⊆ z := by
  intro Hxy Hyz
  apply subset_of_all_mem
  intro w hw
  exact all_mem_of_subset Hyz w (all_mem_of_subset Hxy w hw)

@[simp] lemma subset_self {x : PSet} : x ⊆ x :=
  subset_of_all_mem fun _ h => h

/-! ### ofNat lemmas (src lines 706-768) -/
-- In mathlib4, Lean 3's `of_nat` is `PSet.ofNat`.
-- Lean 3 omega.type = ℕ-indexed; mathlib4 uses ULift ℕ.

lemma ofNat_succ {k : ℕ} : PSet.ofNat (k + 1) = succ_ord (PSet.ofNat k) := by
  simp [PSet.ofNat, succ_ord]

lemma subset_of_le {k₁ k₂ : ℕ} (H : k₁ ≤ k₂) : PSet.ofNat k₁ ⊆ PSet.ofNat k₂ := by
  induction H with
  | refl => exact subset_self
  | step _ ih =>
    apply subset_trans ih
    rw [ofNat_succ]
    exact subset_of_all_mem fun z hz => PSet.mem_insert_iff.mpr (Or.inr hz)

lemma false_of_subset_ofNat_ge {k₁ k₂ : ℕ} (H : k₁ < k₂) :
    ¬ (PSet.ofNat k₂ ⊆ PSet.ofNat k₁) := by
  intro H_sub
  suffices h : PSet.ofNat k₁ ∈ PSet.ofNat k₁ from PSet.mem_irrefl _ h
  suffices h2 : PSet.ofNat (k₁ + 1) ⊆ PSet.ofNat k₂ by
    have h3 : PSet.ofNat k₁ ∈ PSet.ofNat (k₁ + 1) := by
      rw [ofNat_succ]; exact PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))
    exact all_mem_of_subset (subset_trans h2 H_sub) _ h3
  exact subset_of_le (Nat.succ_le_of_lt H)

lemma le_of_subset_ofNat {k₁ k₂ : ℕ} (H : PSet.ofNat k₁ ⊆ PSet.ofNat k₂) : k₁ ≤ k₂ := by
  by_contra h
  push_neg at h
  exact false_of_subset_ofNat_ge h H

lemma ofNat_of_mem_ofNat {y : PSet.{u}} {k : ℕ}
    (H_mem : y ∈ (PSet.ofNat k : PSet.{u})) :
    ∃ j, Equiv y (PSet.ofNat j : PSet.{u}) := by
  induction k with
  | zero => exact absurd H_mem (PSet.notMem_empty _)
  | succ k ih =>
    rw [ofNat_succ, succ_ord] at H_mem
    rcases PSet.mem_insert_iff.mp H_mem with heq | hin
    · exact ⟨k, heq⟩
    · exact ih hin

lemma ofNat_is_transitive {k : ℕ} : is_transitive (PSet.ofNat k) := by
  induction k with
  | zero =>
    intro y hy
    exact absurd hy (PSet.notMem_empty _)
  | succ k ih =>
    intro y Hy
    rw [ofNat_succ, succ_ord] at Hy
    rcases PSet.mem_insert_iff.mp Hy with heq | hin
    · -- y ≡ ofNat k; but this means y is ofNat k, so y ⊆ ofNat k ⊆ ofNat (k+1)
      -- We need: y ∈ ofNat k → use ih applied to something in ofNat k
      apply subset_of_all_mem; intro z Hz
      rw [ofNat_succ, succ_ord]
      apply PSet.mem_insert_iff.mpr; right
      -- Hz : z ∈ y, heq : Equiv y (ofNat k)
      -- z ∈ ofNat k by transitivity through equiv
      have Hz' : z ∈ PSet.ofNat k := (PSet.Mem.congr_right heq).mp Hz
      -- ofNat k is transitive... but we don't have y_hin for ih
      -- Actually y ≡ ofNat k means ih applies to ofNat k directly
      exact Hz'
    · -- y ∈ ofNat k, by ih, y ⊆ ofNat k ⊆ ofNat(k+1)
      apply subset_of_all_mem; intro z Hz
      rw [ofNat_succ, succ_ord]
      exact PSet.mem_insert_iff.mpr (Or.inr (all_mem_of_subset (ih y hin) z Hz))

lemma ofNat_mem_of_lt {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) :
    (PSet.ofNat k₁ : PSet.{u}) ∈ (PSet.ofNat k₂ : PSet.{u}) := by
  induction H_lt with
  | refl =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))
  | step _ ih =>
    rw [ofNat_succ, succ_ord]
    exact PSet.mem_insert_iff.mpr (Or.inr ih)

lemma lt_of_ofNat_mem {k₁ k₂ : ℕ} (H_mem : PSet.ofNat k₁ ∈ PSet.ofNat k₂) : k₁ < k₂ := by
  by_contra h
  push_neg at h
  have h_sub := subset_of_le h
  have h_mem := all_mem_of_subset h_sub _ H_mem
  exact PSet.mem_irrefl _ h_mem

/-! ### Transitivity and well-orders for omega (src lines 770-800) -/

lemma is_transitive_omega : is_transitive (PSet.omega : PSet.{u}) := by
  intro z Hz
  rw [PSet.mem_def] at Hz
  obtain ⟨⟨k⟩, Hk⟩ := Hz
  apply subset_of_all_mem; intro y Hy
  rw [PSet.mem_def]
  -- omega.Type = ULift ℕ; Func ⟨k⟩ = ofNat k
  simp only [PSet.omega]
  -- Hy : y ∈ z, Hk : Equiv z (ofNat k)
  -- So y ∈ ofNat k; find j with y ≡ ofNat j
  obtain ⟨j, hj⟩ := ofNat_of_mem_ofNat ((PSet.Mem.congr_right Hk).mp Hy)
  exact ⟨⟨j⟩, hj⟩

lemma is_ewo_omega : epsilon_well_orders (PSet.omega : PSet.{u}) := by
  constructor
  · -- trichotomy
    intro y Hy z Hz
    rw [PSet.mem_def] at Hy Hz
    obtain ⟨⟨k₁⟩, Hk₁⟩ := Hy
    obtain ⟨⟨k₂⟩, Hk₂⟩ := Hz
    rcases lt_trichotomy k₁ k₂ with h | rfl | h
    · right; left
      rw [PSet.Mem.congr_left Hk₁, PSet.Mem.congr_right Hk₂]
      exact ofNat_mem_of_lt h
    · left; exact PSet.Equiv.trans Hk₁ Hk₂.symm
    · right; right
      rw [PSet.Mem.congr_left Hk₂, PSet.Mem.congr_right Hk₁]
      exact ofNat_mem_of_lt h
  · exact is_epsilon_well_founded _

lemma Ord_omega : Ord (PSet.omega : PSet.{u}) := ⟨is_ewo_omega, is_transitive_omega⟩

/-- Injectivity of `ofNat`.
    Port of `of_nat_inj` (src/pSet_ordinal.lean:792). -/
lemma ofNat_inj {n k : ℕ} (H_neq : n ≠ k) :
    ¬ Equiv (PSet.ofNat n : PSet.{u}) (PSet.ofNat k : PSet.{u}) := by
  intro H
  rcases lt_trichotomy n k with h | rfl | h
  · exact PSet.mem_irrefl (PSet.ofNat n)
      ((PSet.Mem.congr_right H).mpr (ofNat_mem_of_lt h))
  · exact H_neq rfl
  · exact PSet.mem_irrefl (PSet.ofNat k)
      ((PSet.Mem.congr_right H.symm).mpr (ofNat_mem_of_lt h))

/-- The indexing function for omega is injective.
    Port of `omega_inj` (src/pSet_ordinal.lean:798). -/
lemma omega_inj {n k : PSet.omega.Type} :
    Equiv (PSet.omega.Func n) (PSet.omega.Func k) → n = k := by
  intro H
  cases n with | up n => cases k with | up k =>
  suffices h : n = k by subst h; rfl
  by_contra H'
  exact ofNat_inj H' H

/-! ### Pair and product for pSets (src lines 945-984) -/

/-- The ordered pair pSet `{{x}, {x, y}}`. -/
def pSet_pair (x y : PSet.{u}) : PSet.{u} := {{x}, {x, y}}

lemma pSet_pair_sound {x y : PSet.{u}} :
    ZFSet.mk (pSet_pair x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) := rfl

lemma equiv_iff_eq_pSet_pair {x y x' y' : PSet.{u}} :
    Equiv x x' ∧ Equiv y y' ↔ Equiv (pSet_pair x y) (pSet_pair x' y') := by
  constructor
  · rintro ⟨H₁, H₂⟩
    apply ZFSet.exact
    simp only [pSet_pair_sound]
    rw [ZFSet.pair_inj]
    exact ⟨ZFSet.sound H₁, ZFSet.sound H₂⟩
  · intro H
    have h : ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) =
             ZFSet.pair (ZFSet.mk x') (ZFSet.mk y') := by
      rw [← pSet_pair_sound, ← pSet_pair_sound]; exact ZFSet.sound H
    exact ⟨ZFSet.exact (ZFSet.pair_inj.mp h).1, ZFSet.exact (ZFSet.pair_inj.mp h).2⟩

/-- The cartesian product pSet. -/
def pSet_prod (x y : PSet.{u}) : PSet.{u} :=
  ⟨x.Type × y.Type, fun pr => pSet_pair (x.Func pr.1) (y.Func pr.2)⟩

lemma pSet_prod_sound {x y : PSet.{u}} :
    ZFSet.mk (pSet_prod x y) = ZFSet.prod (ZFSet.mk x) (ZFSet.mk y) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_prod]
  constructor
  · intro hz
    rw [← ZFSet.mk_out z, ZFSet.mk_mem_iff, PSet.mem_def] at hz
    obtain ⟨⟨i, j⟩, hij⟩ := hz
    exact ⟨ZFSet.mk (x.Func i),
           by rw [ZFSet.mk_mem_iff]; exact PSet.func_mem x i,
           ZFSet.mk (y.Func j),
           by rw [ZFSet.mk_mem_iff]; exact PSet.func_mem y j,
           by rw [← pSet_pair_sound, ← ZFSet.mk_out z]; exact ZFSet.sound hij⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [hab, ← ZFSet.mk_out a, ← ZFSet.mk_out b]
    rw [← ZFSet.mk_out a, ZFSet.mk_mem_iff, PSet.mem_def] at ha
    rw [← ZFSet.mk_out b, ZFSet.mk_mem_iff, PSet.mem_def] at hb
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    have h_pair : (ZFSet.mk a.out).pair (ZFSet.mk b.out) = ZFSet.mk (pSet_pair a.out b.out) :=
      pSet_pair_sound.symm
    rw [h_pair, ZFSet.mk_mem_iff, PSet.mem_def]
    refine ⟨⟨i, j⟩, ?_⟩
    show PSet.Equiv (pSet_pair a.out b.out) (pSet_pair (x.Func i) (y.Func j))
    apply ZFSet.exact
    show ZFSet.mk (pSet_pair a.out b.out) = ZFSet.mk (pSet_pair (x.Func i) (y.Func j))
    rw [pSet_pair_sound, pSet_pair_sound, ZFSet.pair_inj]
    exact ⟨ZFSet.sound hi, ZFSet.sound hj⟩

lemma mem_pSet_prod_iff {x y a b : PSet.{u}} :
    pSet_pair a b ∈ pSet_prod x y ↔ a ∈ x ∧ b ∈ y := by
  rw [mem_iff, pSet_pair_sound, pSet_prod_sound, ZFSet.pair_mem_prod, ← mem_iff, ← mem_iff]

/-! ### Injection predicates (src lines 986-990) -/

@[reducible] def is_inj (f : PSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂ : PSet.{u},
    pSet_pair w₁ v₁ ∈ f ∧ pSet_pair w₂ v₂ ∈ f ∧ Equiv v₁ v₂ → Equiv w₁ w₂

def is_injective_function (x y f : PSet.{u}) : Prop := is_func x y f ∧ is_inj f

def injects_into (x y : PSet.{u}) : Prop := ∃ f, is_injective_function x y f

/-! ### Subset characterization via ZFSet (src/pSet_ordinal.lean:994-1000) -/

lemma subset_sound {x y : PSet.{u}} :
    x ⊆ y ↔ ZFSet.mk x ⊆ ZFSet.mk y := by
  rw [ZFSet.subset_iff]

-- ============================================================
-- Task 6c additions: lines 1000-1391 of src/pSet_ordinal.lean
-- ============================================================

/-! ### is_func characterization (src lines 1002-1045) -/

/-- `is_func x y f` iff `f ⊆ pSet_prod x y` and for every `z ∈ x` there exists a unique `w`
    with `pSet_pair z w ∈ f`.
    Port of `is_func_iff` (src/pSet_ordinal.lean:1002). -/
lemma is_func_iff {x y f : PSet.{u}} :
    is_func x y f ↔ f ⊆ pSet_prod x y ∧ ∀ z, z ∈ x →
      (∃ w, pSet_pair z w ∈ f ∧ ∀ v, pSet_pair z v ∈ f → Equiv v w) := by
  unfold is_func ZFSet.IsFunc
  rw [← pSet_prod_sound, ← subset_sound]
  constructor
  · rintro ⟨H_sub, H_uniq⟩
    refine ⟨H_sub, fun z Hz => ?_⟩
    specialize H_uniq (ZFSet.mk z) (mem_iff.mp Hz)
    obtain ⟨w, Hw₁, Hw₂⟩ := H_uniq
    refine ⟨w.out, ?_, fun v Hv => ?_⟩
    · rw [mem_iff, pSet_pair_sound, ZFSet.mk_out]; exact Hw₁
    · rw [mem_iff, pSet_pair_sound] at Hv
      rw [equiv_iff_eq, ZFSet.mk_out]
      exact Hw₂ (ZFSet.mk v) Hv
  · rintro ⟨H_sub, H_uniq⟩
    refine ⟨H_sub, fun z Hz => ?_⟩
    rw [← ZFSet.mk_out z] at Hz
    rw [ZFSet.mk_mem_iff] at Hz
    obtain ⟨w, Hw₁, Hw₂⟩ := H_uniq z.out Hz
    refine ⟨ZFSet.mk w, ?_, fun v Hv => ?_⟩
    · -- goal: (fun w => z.pair w ∈ ZFSet.mk f) (ZFSet.mk w)
      -- = z.pair (ZFSet.mk w) ∈ ZFSet.mk f
      change z.pair (ZFSet.mk w) ∈ ZFSet.mk f
      rw [← ZFSet.mk_out z]
      rw [show (ZFSet.mk z.out).pair (ZFSet.mk w) = ZFSet.mk (pSet_pair z.out w)
          from pSet_pair_sound.symm]
      exact mem_iff.mp Hw₁
    · -- goal: v = ZFSet.mk w
      -- v : ZFSet, Hv : z.pair v ∈ ZFSet.mk f
      rw [← ZFSet.mk_out z, ← ZFSet.mk_out v] at Hv
      rw [show (ZFSet.mk z.out).pair (ZFSet.mk v.out) = ZFSet.mk (pSet_pair z.out v.out)
          from pSet_pair_sound.symm, ZFSet.mk_mem_iff] at Hv
      have h := Hw₂ v.out Hv
      rw [equiv_iff_eq] at h
      rw [← ZFSet.mk_out v]
      exact h

lemma subset_prod_of_is_func {x y f : PSet.{u}} (H_func : is_func x y f) : f ⊆ pSet_prod x y := by
  rw [is_func_iff] at H_func
  exact H_func.left

def is_total (x y f : PSet.{u}) : Prop := ∀ z ∈ x, ∃ w, w ∈ y ∧ pSet_pair z w ∈ f

lemma is_total_of_is_func {x y f : PSet.{u}} (H_func : is_func x y f) : is_total x y f := by
  intro z Hz
  rw [is_func_iff] at H_func
  obtain ⟨H_sub, H_uniq⟩ := H_func
  obtain ⟨w, Hw₁, _⟩ := H_uniq z Hz
  exact ⟨w, (mem_pSet_prod_iff.mp (all_mem_of_subset H_sub _ Hw₁)).2, Hw₁⟩

/-! ### powerset_sound (src line 1047) -/

lemma powerset_sound {x : PSet.{u}} : ZFSet.mk (PSet.powerset x) = ZFSet.powerset (ZFSet.mk x) :=
  rfl

/-! ### set_of_indicator, functions, mem_functions_iff (src lines 1049-1067) -/

def set_of_indicator {x : PSet.{u}} (χ : x.Type → Prop) : PSet.{u} :=
  ⟨{i // χ i}, fun p => x.Func p.1⟩

/-- The set of all functions from x to y (as a pSet).
    Port of `functions` (src/pSet_ordinal.lean:1052). -/
def functions (x y : PSet.{u}) : PSet.{u} :=
  @set_of_indicator (PSet.powerset (pSet_prod x y))
    (fun i_S => is_func x y ((PSet.powerset (pSet_prod x y)).Func i_S))

lemma mem_functions_iff {x y : PSet.{u}} (z : PSet.{u}) : z ∈ functions x y ↔ is_func x y z := by
  constructor
  · intro H
    rw [mem_unfold] at H
    obtain ⟨⟨j, Hj_prop⟩, Hj_eq⟩ := H
    -- Hj_prop : is_func x y ((powerset (pSet_prod x y)).Func j)
    -- Hj_eq : Equiv z ((powerset (pSet_prod x y)).Func j)
    unfold is_func ZFSet.IsFunc at Hj_prop ⊢
    rw [equiv_iff_eq] at Hj_eq
    rw [Hj_eq]
    exact Hj_prop
  · intro H
    -- H : is_func x y z
    -- z is a subset of pSet_prod x y (from H), so z ∈ powerset(pSet_prod x y)
    have H_sub : z ⊆ pSet_prod x y := subset_prod_of_is_func H
    have H_pow : z ∈ PSet.powerset (pSet_prod x y) := PSet.mem_powerset.mpr H_sub
    rw [mem_unfold] at H_pow
    obtain ⟨j, Hj⟩ := H_pow
    rw [mem_unfold]
    refine ⟨⟨j, ?_⟩, Hj⟩
    -- need: is_func x y ((powerset (pSet_prod x y)).Func j)
    unfold is_func ZFSet.IsFunc at H ⊢
    rw [equiv_iff_eq] at Hj
    rw [← Hj]
    exact H

/-! ### card_ex_aleph_exists_mem (src line 1071) -/

open Cardinal in
@[simp] lemma card_ex_aleph_exists_mem {n : ℕ} : ∃ z, z ∈ card_ex (Cardinal.aleph n) := by
  refine ⟨card_ex 0, mk_mem_mk_of_lt ?_⟩
  -- ord 0 < ord (aleph n): since aleph 0 = ℵ₀ > 0, ord is strictly monotone
  apply Cardinal.ord_lt_ord.mpr
  induction n with
  | zero => exact Cardinal.aleph_pos 0
  | succ n ih => exact ih.trans (Cardinal.aleph_lt_aleph.mpr (by exact_mod_cast Nat.lt_succ_self n))

/-! ### function.mk and related (src lines 1080-1132) -/

namespace function_mk

/-- Build a pSet function graph from a family `ψ : x.Type → PSet`.
    Port of `pSet.function.mk` (src/pSet_ordinal.lean:1080). -/
def mk {x : PSet.{u}} (ψ : x.Type → PSet.{u})
    (H_ext : ∀ i j, Equiv (x.Func i) (x.Func j) → Equiv (ψ i) (ψ j)) : PSet.{u} :=
  ⟨x.Type, fun i => pSet_pair (x.Func i) (ψ i)⟩

lemma mk_mem {x : PSet.{u}} {ψ : x.Type → PSet.{u}}
    {H_ext : ∀ i j, Equiv (x.Func i) (x.Func j) → Equiv (ψ i) (ψ j)}
    {i : x.Type} : pSet_pair (x.Func i) (ψ i) ∈ mk ψ H_ext :=
  PSet.func_mem (mk ψ H_ext) i

lemma mk_is_func {x y : PSet.{u}} (ψ : x.Type → PSet.{u})
    {H_ext : ∀ i j, Equiv (x.Func i) (x.Func j) → Equiv (ψ i) (ψ j)}
    (H_im : ∀ i, ψ i ∈ y) : is_func x y (mk ψ H_ext) := by
  rw [is_func_iff]
  constructor
  · apply subset_of_all_mem
    intro w hw
    rw [mem_unfold] at hw ⊢
    obtain ⟨i, hi⟩ := hw
    obtain ⟨j, hj⟩ := mem_unfold.mp (H_im i)
    refine ⟨⟨i, j⟩, ?_⟩
    apply PSet.Equiv.trans hi
    show PSet.Equiv (pSet_pair (x.Func i) (ψ i)) (pSet_pair (x.Func i) (y.Func j))
    exact equiv_iff_eq_pSet_pair.mp ⟨PSet.Equiv.refl _, hj⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_unfold.mp hz
    refine ⟨ψ i, ?_, ?_⟩
    · rw [mem_unfold]; refine ⟨i, ?_⟩
      show PSet.Equiv (pSet_pair z (ψ i)) (pSet_pair (x.Func i) (ψ i))
      exact equiv_iff_eq_pSet_pair.mp ⟨hi, PSet.Equiv.refl _⟩
    · intro v hv
      rw [mem_unfold] at hv
      obtain ⟨k, hk⟩ := hv
      have ⟨hzk, hvk⟩ := equiv_iff_eq_pSet_pair.mpr hk
      have hki : PSet.Equiv (x.Func k) (x.Func i) := hzk.symm.trans hi
      exact PSet.Equiv.trans hvk (H_ext k i hki)

lemma mk_inj_of_inj {x : PSet.{u}} (ψ : x.Type → PSet.{u})
    (H_ext : ∀ i j, Equiv (x.Func i) (x.Func j) → Equiv (ψ i) (ψ j))
    (H_inj : ∀ i₁ i₂, Equiv (ψ i₁) (ψ i₂) → Equiv (x.Func i₁) (x.Func i₂)) :
    is_inj (mk ψ H_ext) := by
  intro w₁ w₂ v₁ v₂ ⟨Hpr₁, Hpr₂, H_eq⟩
  rw [mem_unfold] at Hpr₁ Hpr₂
  obtain ⟨i, Hi⟩ := Hpr₁
  obtain ⟨j, Hj⟩ := Hpr₂
  have ⟨hw₁xi, hv₁ψi⟩ := equiv_iff_eq_pSet_pair.mpr Hi
  have ⟨hw₂xj, hv₂ψj⟩ := equiv_iff_eq_pSet_pair.mpr Hj
  have hψiψj : PSet.Equiv (ψ i) (ψ j) := hv₁ψi.symm.trans (H_eq.trans hv₂ψj)
  have hxixj : PSet.Equiv (x.Func i) (x.Func j) := H_inj i j hψiψj
  exact hw₁xi.trans (hxixj.trans hw₂xj.symm)

end function_mk

/-! ### P_ext predicate (src lines 1144-1161) -/

def P_ext : (PSet → Prop) → Prop := fun χ => ∀ x y, Equiv x y → χ x → χ y

@[simp] lemma P_ext_mem_left {y : PSet} : P_ext (fun x => x ∈ y) :=
  fun _ _ H_eq H_mem => (PSet.Mem.congr_left H_eq).mp H_mem

@[simp] lemma P_ext_mem_right {x : PSet} : P_ext (fun y => x ∈ y) :=
  fun _ _ H_eq H_mem => (PSet.Mem.congr_right H_eq).mp H_mem

@[simp] lemma P_ext_neg {χ : PSet → Prop} (H : P_ext χ) : P_ext (fun z => ¬ χ z) := by
  intro x y H_eq H'
  intro Hy
  exact H' (H y x H_eq.symm Hy)

@[simp] lemma P_ext_injects_into_left {y : PSet.{u}} : P_ext (fun x => injects_into x y) := by
  intro x₁ x₂ H_eq ⟨f, Hf₁, Hf₂⟩
  refine ⟨f, ?_, Hf₂⟩
  unfold is_func at *
  have h : ZFSet.mk x₁ = ZFSet.mk x₂ := equiv_iff_eq.mp H_eq
  rw [← h]
  exact Hf₁

/-! ### mem_sep_iff (src line 1163) -/

-- PSet.sep for P_ext-respecting predicates
-- Note: must use `PSet.sep p x` explicitly (not `{z ∈ x | p z}` which resolves to Set.sep)
lemma mem_sep_iff {p : PSet → Prop} {x w : PSet} (H_congr : P_ext p) :
    w ∈ PSet.sep p x ↔ w ∈ x ∧ p w :=
  PSet.mem_sep (fun a b hab hpa => H_congr a b hab hpa)

/-! ### sep_subset (src line 1134) -/

@[simp] lemma sep_subset {p : PSet → Prop} {x : PSet} (Hp : P_ext p) : PSet.sep p x ⊆ x := by
  apply subset_of_all_mem
  intro w Hw
  exact ((mem_sep_iff Hp).mp Hw).1

/-! ### sep_equiv_iff (src line 1179) -/

lemma sep_equiv_iff {p₁ p₂ : PSet → Prop} {x : PSet}
    (H_congr₁ : P_ext p₁) (H_congr₂ : P_ext p₂) :
    Equiv (PSet.sep p₁ x) (PSet.sep p₂ x) ↔ ∀ z, z ∈ x ∧ p₁ z ↔ z ∈ x ∧ p₂ z := by
  constructor
  · intro H z
    rw [← mem_sep_iff H_congr₁, ← mem_sep_iff H_congr₂]
    exact PSet.Mem.congr_right H
  · intro H
    apply PSet.Mem.ext; intro z
    rw [mem_sep_iff H_congr₁, mem_sep_iff H_congr₂]
    exact H z

/-! ### mem_two (src line 1186) -/

lemma mem_two {x : PSet.{u}} (H : x ∈ (PSet.ofNat 2 : PSet.{u})) :
    Equiv x (PSet.ofNat 0 : PSet.{u}) ∨ Equiv x (PSet.ofNat 1 : PSet.{u}) := by
  -- ofNat 2 = insert (ofNat 1) (insert (ofNat 0) (insert (ofNat 0) ∅))
  -- membership means x ≡ ofNat 1 or x ∈ ofNat 1
  -- ofNat 1 = insert (ofNat 0) ∅, membership means x ≡ ofNat 0
  rcases PSet.mem_insert_iff.mp H with heq | hin
  · -- x ≡ ofNat 1
    right; exact heq
  · -- x ∈ ofNat 1 = insert (ofNat 0) ∅
    rcases PSet.mem_insert_iff.mp hin with heq | hin'
    · left; exact heq
    · -- x ∈ ofNat 0 = ∅, impossible
      exact absurd hin' (PSet.notMem_empty _)

/-! ### pair_mem.congr_right/left (src lines 1194-1215) -/

lemma pSet_pair_mem_congr_right {p q r s : PSet.{u}} (H : Equiv q r) :
    pSet_pair p q ∈ s ↔ pSet_pair p r ∈ s := by
  rw [mem_iff, mem_iff, pSet_pair_sound, pSet_pair_sound]
  constructor
  · intro h; rwa [show ZFSet.pair (ZFSet.mk p) (ZFSet.mk q) = ZFSet.pair (ZFSet.mk p) (ZFSet.mk r) from
      by rw [ZFSet.pair_inj]; exact ⟨rfl, ZFSet.sound H⟩] at h
  · intro h; rwa [show ZFSet.pair (ZFSet.mk p) (ZFSet.mk r) = ZFSet.pair (ZFSet.mk p) (ZFSet.mk q) from
      by rw [ZFSet.pair_inj]; exact ⟨rfl, ZFSet.sound H.symm⟩] at h

lemma pSet_pair_mem_congr_left {p q r s : PSet.{u}} (H : Equiv q r) :
    pSet_pair q p ∈ s ↔ pSet_pair r p ∈ s := by
  rw [mem_iff, mem_iff, pSet_pair_sound, pSet_pair_sound]
  constructor
  · intro h; rwa [show ZFSet.pair (ZFSet.mk q) (ZFSet.mk p) = ZFSet.pair (ZFSet.mk r) (ZFSet.mk p) from
      by rw [ZFSet.pair_inj]; exact ⟨ZFSet.sound H, rfl⟩] at h
  · intro h; rwa [show ZFSet.pair (ZFSet.mk r) (ZFSet.mk p) = ZFSet.pair (ZFSet.mk q) (ZFSet.mk p) from
      by rw [ZFSet.pair_inj]; exact ⟨ZFSet.sound H.symm, rfl⟩] at h

@[simp] lemma P_ext_pair_mem_right {b c : PSet} : P_ext (fun w => pSet_pair b w ∈ c) :=
  fun _ _ H Hx => (pSet_pair_mem_congr_right H).mp Hx

@[simp] lemma P_ext_pair_mem_left {b c : PSet} : P_ext (fun w => pSet_pair w b ∈ c) :=
  fun _ _ H Hx => (pSet_pair_mem_congr_left H).mp Hx

/-! ### section injects_powerset (src lines 1218-1369) -/

section injects_powerset

variable {x : PSet.{u}}

-- Abbreviation for functions x {0,1}
private abbrev fx2 (x : PSet.{u}) : PSet.{u} := functions x (PSet.ofNat 2 : PSet.{u})

-- Predicate: "z maps to 0 under χ"
private def preimage0 (x : PSet.{u}) (χ : (fx2 x).Type) : PSet → Prop :=
  fun z => pSet_pair z (PSet.ofNat 0 : PSet.{u}) ∈ (fx2 x).Func χ

-- For each function χ in fx2, the "preimage of 0" subset of x
private def f2ip_F (x : PSet.{u}) : (fx2 x).Type → PSet.{u} :=
  fun χ => PSet.sep (preimage0 x χ) x

lemma f2ip_P_ext {x : PSet.{u}} {χ : (fx2 x).Type} {b : PSet} :
    P_ext (fun z => pSet_pair z b ∈ (fx2 x).Func χ) :=
  P_ext_pair_mem_left

lemma mem_f2ip_F_iff {x : PSet.{u}} {χ : (fx2 x).Type} {w : PSet} :
    w ∈ f2ip_F x χ ↔ w ∈ x ∧ pSet_pair w (PSet.ofNat 0 : PSet.{u}) ∈ (fx2 x).Func χ :=
  mem_sep_iff f2ip_P_ext

lemma f2ip_F_ext (x : PSet.{u}) :
    ∀ i j, Equiv ((fx2 x).Func i) ((fx2 x).Func j) → Equiv (f2ip_F x i) (f2ip_F x j) := by
  intro χ₁ χ₂ H_eqv
  -- f2ip_F x χ = PSet.sep (preimage0 x χ) x
  show Equiv (PSet.sep (preimage0 x χ₁) x) (PSet.sep (preimage0 x χ₂) x)
  apply (sep_equiv_iff (f2ip_P_ext (χ := χ₁)) (f2ip_P_ext (χ := χ₂))).mpr
  intro z
  constructor
  · rintro ⟨Hz, Hpr⟩
    refine ⟨Hz, ?_⟩
    rw [mem_iff, pSet_pair_sound] at Hpr ⊢
    rwa [← equiv_iff_eq.mp H_eqv]
  · rintro ⟨Hz, Hpr⟩
    refine ⟨Hz, ?_⟩
    rw [mem_iff, pSet_pair_sound] at Hpr ⊢
    rwa [equiv_iff_eq.mp H_eqv]

def f2ip (x : PSet.{u}) : PSet.{u} := function_mk.mk (f2ip_F x) (f2ip_F_ext x)

lemma mem_f2ip_iff {x a b : PSet.{u}} :
    pSet_pair a b ∈ f2ip x ↔
    a ∈ fx2 x ∧ b ∈ PSet.powerset x ∧
    Equiv b (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0 : PSet.{u}) ∈ a) x) := by
  constructor
  · intro H
    rw [mem_unfold] at H
    obtain ⟨χ, Hχ⟩ := H
    have ⟨ha, hb⟩ := equiv_iff_eq_pSet_pair.mpr Hχ
    refine ⟨?_, ?_, ?_⟩
    · exact (PSet.Mem.congr_left ha).mpr (PSet.func_mem (fx2 x) χ)
    · rw [PSet.mem_powerset]
      exact (PSet.Subset.congr_left hb).mpr (sep_subset f2ip_P_ext)
    · apply PSet.Equiv.trans hb
      apply (sep_equiv_iff f2ip_P_ext P_ext_pair_mem_left).mpr
      intro z
      constructor
      · rintro ⟨Hz, Hpr⟩; exact ⟨Hz, (PSet.Mem.congr_right ha.symm).mp Hpr⟩
      · rintro ⟨Hz, Hpr⟩; exact ⟨Hz, (PSet.Mem.congr_right ha).mp Hpr⟩
  · rintro ⟨H₁, _H₂, H₃⟩
    rw [mem_unfold] at H₁ ⊢
    obtain ⟨χ, Hχ⟩ := H₁
    refine ⟨χ, ?_⟩
    show PSet.Equiv (pSet_pair a b) (pSet_pair ((fx2 x).Func χ) (f2ip_F x χ))
    apply equiv_iff_eq_pSet_pair.mp
    refine ⟨Hχ, PSet.Equiv.trans H₃ ?_⟩
    apply (sep_equiv_iff P_ext_pair_mem_left f2ip_P_ext).mpr
    intro z
    constructor
    · rintro ⟨Hz, Hpr⟩; exact ⟨Hz, (PSet.Mem.congr_right Hχ).mp Hpr⟩
    · rintro ⟨Hz, Hpr⟩; exact ⟨Hz, (PSet.Mem.congr_right Hχ.symm).mp Hpr⟩

lemma rel_eq_iff {x y f g : PSet.{u}} (H₁ : f ⊆ pSet_prod x y) (H₂ : g ⊆ pSet_prod x y) :
    Equiv f g ↔ ∀ a ∈ x, ∀ b ∈ y, pSet_pair a b ∈ f ↔ pSet_pair a b ∈ g := by
  constructor
  · intro H a _Ha b _Hb
    exact PSet.Mem.congr_right H
  · intro H
    apply PSet.Mem.ext; intro p
    constructor
    · intro hpf
      have hprod := all_mem_of_subset H₁ p hpf
      rw [mem_unfold] at hprod
      obtain ⟨⟨i, j⟩, hpr⟩ := hprod
      specialize H (x.Func i) (PSet.func_mem x i) (y.Func j) (PSet.func_mem y j)
      exact (PSet.Mem.congr_left hpr).mpr (H.mp ((PSet.Mem.congr_left hpr).mp hpf))
    · intro hpg
      have hprod := all_mem_of_subset H₂ p hpg
      rw [mem_unfold] at hprod
      obtain ⟨⟨i, j⟩, hpr⟩ := hprod
      specialize H (x.Func i) (PSet.func_mem x i) (y.Func j) (PSet.func_mem y j)
      exact (PSet.Mem.congr_left hpr).mpr (H.mpr ((PSet.Mem.congr_left hpr).mp hpg))

lemma false_of_zero_eq_one (H : Equiv (PSet.ofNat 0 : PSet.{u}) (PSet.ofNat 1 : PSet.{u})) :
    False := ofNat_inj (Nat.zero_ne_one) H

lemma function_to_2_eq_aux₂ {w : PSet} (Hfunc : is_func x (PSet.ofNat 2) w) {a} :
    pSet_pair a (PSet.ofNat 0) ∈ w → pSet_pair a (PSet.ofNat 1) ∈ w → False := by
  intro H₁ H₂
  rw [is_func_iff] at Hfunc
  obtain ⟨_H_sub, H⟩ := Hfunc
  have Ha : a ∈ x := (mem_pSet_prod_iff.mp (all_mem_of_subset _H_sub _ H₁)).1
  obtain ⟨_w', _Hw'₁, Hw'₂⟩ := H a Ha
  have h1 := Hw'₂ (PSet.ofNat 0) H₁
  have h2 := Hw'₂ (PSet.ofNat 1) H₂
  -- h1 : Equiv (ofNat 0) _w', h2 : Equiv (ofNat 1) _w'
  exact false_of_zero_eq_one (h1.trans h2.symm)

-- Auxiliary: sep for predicate "pair z k ∈ w" is P_ext-respecting
private lemma P_ext_pair_in_w {k w : PSet} : P_ext (fun z => pSet_pair z k ∈ w) :=
  P_ext_pair_mem_left

lemma function_to_2_eq_aux {w₁ w₂ : PSet}
    (Hfunc₁ : is_func x (PSet.ofNat 2) w₁)
    (Hfunc₂ : is_func x (PSet.ofNat 2) w₂)
    (H_eq : Equiv (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x)
                  (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x)) :
    Equiv (PSet.sep (fun z => pSet_pair z (PSet.ofNat 1) ∈ w₁) x)
          (PSet.sep (fun z => pSet_pair z (PSet.ofNat 1) ∈ w₂) x) := by
  apply PSet.Mem.ext; intro w
  constructor
  · intro Hmem
    rw [mem_sep_iff P_ext_pair_in_w] at Hmem ⊢
    obtain ⟨Hx, H1⟩ := Hmem
    refine ⟨Hx, ?_⟩
    by_contra Hcontra
    obtain ⟨k, Hk₁, Hk₂⟩ := is_total_of_is_func Hfunc₂ w Hx
    rcases mem_two Hk₁ with H_zero | H_one
    · have H0 : pSet_pair w (PSet.ofNat 0) ∈ w₂ := (pSet_pair_mem_congr_right H_zero).mp Hk₂
      have Hmem2 : w ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Hx, H0⟩
      have Hmem1 : w ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x :=
        (PSet.Mem.congr_right H_eq.symm).mp Hmem2
      exact function_to_2_eq_aux₂ Hfunc₁ ((mem_sep_iff P_ext_pair_in_w).mp Hmem1).2 H1
    · exact Hcontra ((pSet_pair_mem_congr_right H_one).mp Hk₂)
  · intro Hmem
    rw [mem_sep_iff P_ext_pair_in_w] at Hmem ⊢
    obtain ⟨Hx, H1⟩ := Hmem
    refine ⟨Hx, ?_⟩
    by_contra Hcontra
    obtain ⟨k, Hk₁, Hk₂⟩ := is_total_of_is_func Hfunc₁ w Hx
    rcases mem_two Hk₁ with H_zero | H_one
    · have H0 : pSet_pair w (PSet.ofNat 0) ∈ w₁ := (pSet_pair_mem_congr_right H_zero).mp Hk₂
      have Hmem1 : w ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Hx, H0⟩
      have Hmem2 : w ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x :=
        (PSet.Mem.congr_right H_eq).mp Hmem1
      exact function_to_2_eq_aux₂ Hfunc₂ ((mem_sep_iff P_ext_pair_in_w).mp Hmem2).2 H1
    · exact Hcontra ((pSet_pair_mem_congr_right H_one).mp Hk₂)

lemma functions_to_2_eq {w₁ w₂ : PSet}
    (H_eq : Equiv (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x)
                  (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x))
    (H₁₁ : w₁ ∈ functions x (PSet.ofNat 2))
    (H₂₁ : w₂ ∈ functions x (PSet.ofNat 2)) : Equiv w₁ w₂ := by
  have H'₁₁ := H₁₁
  have H'₂₁ := H₂₁
  rw [mem_functions_iff] at H₁₁ H₂₁
  rw [is_func_iff] at H₁₁ H₂₁
  obtain ⟨H₁_sub, H₁⟩ := H₁₁
  obtain ⟨H₂_sub, _H₂⟩ := H₂₁
  rw [rel_eq_iff H₁_sub H₂_sub]
  intro a Ha b Hb
  constructor
  · -- w₁ → w₂ direction: use H_eq to move from sep_w₁ to sep_w₂
    intro H
    rcases mem_two Hb with H_zero | H_one
    · rw [pSet_pair_mem_congr_right H_zero] at H ⊢
      -- H : pair a 0 ∈ w₁; want: pair a 0 ∈ w₂
      have Hmem : a ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Ha, H⟩
      exact ((mem_sep_iff P_ext_pair_in_w).mp ((PSet.Mem.congr_right H_eq).mp Hmem)).2
    · replace H_eq := function_to_2_eq_aux (mem_functions_iff _ |>.mp H'₁₁)
        (mem_functions_iff _ |>.mp H'₂₁) H_eq
      rw [pSet_pair_mem_congr_right H_one] at H ⊢
      have Hmem : a ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 1) ∈ w₁) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Ha, H⟩
      exact ((mem_sep_iff P_ext_pair_in_w).mp ((PSet.Mem.congr_right H_eq).mp Hmem)).2
  · -- w₂ → w₁ direction: use H_eq.symm
    intro H
    rcases mem_two Hb with H_zero | H_one
    · rw [pSet_pair_mem_congr_right H_zero] at H ⊢
      have Hmem : a ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Ha, H⟩
      exact ((mem_sep_iff P_ext_pair_in_w).mp ((PSet.Mem.congr_right H_eq.symm).mp Hmem)).2
    · replace H_eq := function_to_2_eq_aux (mem_functions_iff _ |>.mp H'₁₁)
        (mem_functions_iff _ |>.mp H'₂₁) H_eq
      rw [pSet_pair_mem_congr_right H_one] at H ⊢
      have Hmem : a ∈ PSet.sep (fun z => pSet_pair z (PSet.ofNat 1) ∈ w₂) x :=
        (mem_sep_iff P_ext_pair_in_w).mpr ⟨Ha, H⟩
      exact ((mem_sep_iff P_ext_pair_in_w).mp ((PSet.Mem.congr_right H_eq.symm).mp Hmem)).2

lemma functions_2_injects_into_powerset (x : PSet.{u}) :
    ∃ (f : PSet.{u}), is_injective_function
      (functions x (PSet.ofNat 2) : PSet.{u}) (PSet.powerset x : PSet.{u}) f := by
  refine ⟨f2ip x, ?_, ?_⟩
  · -- is_func (functions x 2) (powerset x) (f2ip x)
    unfold f2ip
    apply function_mk.mk_is_func
    intro χ
    rw [PSet.mem_powerset]
    exact sep_subset f2ip_P_ext
  · -- is_inj (f2ip x): follows from functions_to_2_eq via mem_f2ip_iff
    intro w₁ w₂ v₁ v₂ ⟨H₁, H₂, H_eq⟩
    rw [mem_f2ip_iff] at H₁ H₂
    obtain ⟨H₁₁, _H₁₂, H₁₃⟩ := H₁
    obtain ⟨H₂₁, _H₂₂, H₂₃⟩ := H₂
    have : Equiv (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₁) x)
                 (PSet.sep (fun z => pSet_pair z (PSet.ofNat 0) ∈ w₂) x) := by
      -- H₁₃ : Equiv v₁ (sep ... w₁), H₂₃ : Equiv v₂ (sep ... w₂), H_eq : Equiv v₁ v₂
      exact H₁₃.symm.trans (H_eq.trans H₂₃)
    exact functions_to_2_eq this H₁₁ H₂₁

end injects_powerset

/-! ### eq_of_is_func_of_eq (src line 1372) -/

lemma eq_of_is_func_of_eq {a b c d : PSet.{u}} {x y f : PSet.{u}}
    (H_func : is_func x y f) (H₁ : pSet_pair a c ∈ f) (H₂ : pSet_pair b d ∈ f)
    (H_eq : Equiv a b) : Equiv c d := by
  rw [is_func_iff] at H_func
  obtain ⟨H_sub, H⟩ := H_func
  have Ha : a ∈ x := (mem_pSet_prod_iff.mp (all_mem_of_subset H_sub _ H₁)).1
  obtain ⟨_w, _Hw₁, Hw₂⟩ := H a Ha
  have h1 : Equiv c _w := Hw₂ c H₁
  have h2 : Equiv d _w := by
    apply Hw₂
    exact (pSet_pair_mem_congr_left H_eq).mpr H₂
  exact PSet.Equiv.trans h1 h2.symm

/-! ### exists_mem_of_nonzero, exists_mem_of_regular (src lines 1384-1388) -/

lemma exists_mem_of_nonzero {η : Ordinal} (H_nonzero : 0 < η) :
    ∃ z : PSet, z ∈ ordinalMk η :=
  ⟨ordinalMk 0, mk_mem_mk_of_lt H_nonzero⟩

open Cardinal in
lemma exists_mem_of_regular {κ : Cardinal} (H_reg : Cardinal.IsRegular κ) :
    ∃ z : PSet, z ∈ card_ex κ :=
  exists_mem_of_nonzero H_reg.ord_pos

end PSet

end -- noncomputable section

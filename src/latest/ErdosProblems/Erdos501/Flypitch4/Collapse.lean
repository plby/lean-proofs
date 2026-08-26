/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/collapse.lean — Part 1 (lines 1-450).
   Covers: top-level helpers (cardinal, ordinal, topological_space, propositional lemmas),
   PFun extension lemmas (inter/compatible/subfun/sup/pSup/singleton/extend_via/trivial_extension).
   Part 2 (lines 451-916) covers the collapse_poset structure and collapse_algebra.
   The `end Flypitch` at the bottom closes the namespace; Part 2 will reopen it.
-/

import ErdosProblems.Erdos501.Flypitch4.RegularOpenAlgebra
import ErdosProblems.Erdos501.Flypitch4.PSetOrdinal
import Mathlib.Data.PFun
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family

set_option relaxedAutoImplicit true

open Set TopologicalSpace Cardinal PSet

universe u v

namespace Flypitch

/-! ## Preliminary order lemmas (src lines 9-14) -/

lemma poset_yoneda_iff {β : Type*} [Preorder β] {a b : β} :
    (∀ Γ : β, Γ ≤ a → Γ ≤ b) ↔ a ≤ b :=
  ⟨fun h => h a le_rfl, fun h _ hΓ => hΓ.trans h⟩

lemma poset_coyoneda_iff {β : Type*} [Preorder β] {a b : β} :
    (∀ Γ : β, a ≤ Γ → b ≤ Γ) ↔ b ≤ a :=
  ⟨fun h => h a le_rfl, fun h _ h' => h.trans h'⟩

/-! ## Cardinal helpers (src lines 28-50).
    Helper lemmas used in the collapse algebra section.
    In Lean 4 / Mathlib 4: `cardinal.sum` → `Cardinal.sum`, `cardinal.lift` → `Cardinal.lift`,
    `cardinal.sup` → `iSup`. -/

/-- Analog of cardinal.sum_const_lift. -/
theorem collapse_sum_const_lift (ι : Type u) (a : Cardinal.{max u v}) :
    Cardinal.sum (fun _ : ι => a) = Cardinal.lift.{v} (#ι) * a := by
  rw [Cardinal.sum_const]
  have h1 : @Cardinal.lift.{max u v, u} = @Cardinal.lift.{v, u} := Cardinal.lift_umax
  have h2 : Cardinal.lift.{u} a = a := Cardinal.lift_id' a
  rw [← h1, h2]

/-- Analog of cardinal.sum_le_sup_lift. -/
theorem collapse_sum_le_sup_lift {ι : Type u} (f : ι → Cardinal.{max u v}) :
    Cardinal.sum f ≤ Cardinal.lift.{v} (#ι) * ⨆ i, f i :=
  Cardinal.sum_le_lift_mk_mul_iSup f

/-- Analog of cardinal.mk_Union_le_sum_mk'. -/
theorem collapse_mk_iUnion_le_sum_mk {ι : Type u} {α : Type (max u v)} {f : ι → Set α} :
    #(⋃ i, f i) ≤ Cardinal.sum (fun i => #(f i)) := by
  have h := @Cardinal.mk_iUnion_le_sum_mk_lift α ι f
  rwa [Cardinal.lift_id'] at h

/-- Analog of cardinal.mk_Union_le_lift. TODO (15b): fix universe annotations. -/
lemma collapse_mk_iUnion_le_lift {ι : Type u} {α : Type (max u v)} (f : ι → Set α) :
    #(⋃ i, f i) ≤ Cardinal.lift.{v} (#ι) * ⨆ i, #(f i) := by
  have key := @Cardinal.mk_iUnion_le_lift α ι f
  rw [Cardinal.lift_id', Cardinal.lift_umax,
      iSup_congr (fun i => Cardinal.lift_id' (#(f i)))] at key
  exact key

/-! ## Ordinal helpers (src lines 52-70) -/

/-- Analog of ordinal.sup_lt_ord_lift. -/
theorem collapse_sup_lt_ord_lift {ι : Type u} (f : ι → Ordinal.{max u v}) {c : Ordinal}
    (H1 : Cardinal.lift.{v} (#ι) < c.cof) (H2 : ∀ i, f i < c) : iSup f < c := by
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · rw [← Ordinal.lift_cof]
    rw [show Cardinal.lift.{u, max u v} c.cof = c.cof from Cardinal.lift_id' _]
    rw [show @Cardinal.lift.{max u v, u} = @Cardinal.lift.{v, u} from Cardinal.lift_umax]
    exact H1
  · exact H2

/-- Analog of ordinal.sup_lt_lift. TODO (15b): fix universe annotations. -/
theorem collapse_sup_lt_lift {ι : Type u} (f : ι → Cardinal.{max u v}) {c : Cardinal.{max u v}}
    (H1 : Cardinal.lift.{v} (#ι) < c.ord.cof)
    (H2 : ∀ i, f i < c) : iSup f < c :=
  Ordinal.iSup_lt_lift H1 H2

/-! ## Topological space helpers (src lines 72-84) -/

/-- Analog of topological_space.mem_interior_of_is_topological_basis. -/
lemma collapse_mem_interior_of_isTopologicalBasis {α} [TopologicalSpace α] {B : Set (Set α)}
    (hB : IsTopologicalBasis B) {s : Set α} {x : α} :
    x ∈ interior s ↔ ∃ t ⊆ s, t ∈ B ∧ x ∈ t := by
  rw [mem_interior]
  constructor
  · rintro ⟨t, h1t, h2t, h3t⟩
    rcases hB.exists_subset_of_mem_open h3t h2t with ⟨u, h1u, h2u, h3u⟩
    exact ⟨u, h3u.trans h1t, h1u, h2u⟩
  · rintro ⟨t, h1t, h2t, h3t⟩
    exact ⟨t, h1t, hB.isOpen h2t, h3t⟩

/-! ## Propositional lemmas (src lines 100-131) -/

@[simp] lemma iff_or_self_left {p q : Prop} : (p ↔ p ∨ q) ↔ (q → p) :=
  ⟨fun h hq => h.mpr (Or.inr hq), fun h => ⟨Or.inl, fun h' => h'.elim id h⟩⟩

@[simp] lemma iff_or_self_right {p q : Prop} : (p ↔ q ∨ p) ↔ (q → p) := by
  simp [or_comm]

@[simp] lemma and_iff_self_right {p q : Prop} : (p ∧ q ↔ p) ↔ (p → q) :=
  ⟨fun h hp => (h.mpr hp).2, fun h => ⟨And.left, fun hp => ⟨hp, h hp⟩⟩⟩

@[simp] lemma and_iff_self_left {p q : Prop} : (p ∧ q ↔ q) ↔ (q → p) := by
  rw [and_comm]; exact and_iff_self_right

lemma and_or_and_not {p q r : Prop} : p ∧ (q ∨ (r ∧ ¬p)) ↔ p ∧ q := by
  constructor
  · rintro ⟨hp, hq | ⟨_, hnp⟩⟩
    · exact ⟨hp, hq⟩
    · exact absurd hp hnp
  · rintro ⟨hp, hq⟩; exact ⟨hp, Or.inl hq⟩

lemma or_and_iff_or {p q r : Prop} : (p ∨ (q ∧ r) ↔ p ∨ q) ↔ (q → p ∨ r) :=
  ⟨fun h hq => (h.mpr (Or.inr hq)).imp id And.right,
   fun h => ⟨fun h' => h'.imp id And.left,
             fun h' => h'.elim Or.inl (fun hq => (h hq).imp id (fun hr => ⟨hq, hr⟩))⟩⟩

lemma and_or_iff_and {p q r : Prop} : (p ∧ (q ∨ r) ↔ p ∧ r) ↔ (p → q → r) :=
  ⟨fun h hp hq => (h.mp ⟨hp, Or.inl hq⟩).2,
   fun h => ⟨fun h' => ⟨h'.1, h'.2.elim (h h'.1) id⟩, And.imp id Or.inr⟩⟩

lemma or_not_iff (p q : Prop) [Decidable q] : (p ∨ ¬q) ↔ (q → p) := by
  rw [imp_iff_not_or, or_comm]

lemma eq_iff_eq_of_eq_left {α} {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

lemma eq_iff_eq_of_eq_right {α} {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

/-! ## PFun extensions (src lines 162-543)

    In Lean 4, `pfun` is `PFun` in Mathlib. Key mappings:
    - `pfun.dom` → `PFun.Dom`
    - `pfun.fn` → `PFun.fn`
    - `pfun.ran` → `PFun.ran`

    Many lemmas from the Lean 3 `pfun` namespace are not in Mathlib 4.
    We define them here using the `CPFun` prefix to avoid clashes,
    and avoid defining type class instances on `α →. β` directly. -/

namespace CPFun

attribute [local instance] Classical.propDecidable

variable {ι : Sort*} {α : Type*} {β : Type*}

/-! ### Domain / function basics (src 166-197) -/

lemma mem_Dom_iff (f : α →. β) (x : α) : x ∈ PFun.Dom f ↔ (f x).Dom := by
  simp [PFun.Dom]

lemma mem_Dom_of_mem {f : α →. β} {x : α} {y : β} (h : y ∈ f x) : x ∈ PFun.Dom f :=
  (PFun.mem_dom f x).mpr ⟨y, h⟩

/-- `Part.some (f.fn x h) = f x` -/
lemma some_fn {f : α →. β} {x : α} (h : x ∈ PFun.Dom f) :
    Part.some (PFun.fn f x h) = f x :=
  Part.some_get h

/-- `f.fn x h ∈ f x` -/
lemma fn_mem {f : α →. β} {x : α} (h : x ∈ PFun.Dom f) : PFun.fn f x h ∈ f x :=
  Part.get_mem h

/-- `y ∈ f x ↔ ∃ h : x ∈ Dom f, f.fn x h = y` -/
lemma mem_iff_fn_eq {f : α →. β} {x : α} {y : β} :
    y ∈ f x ↔ ∃ h : x ∈ PFun.Dom f, PFun.fn f x h = y := by
  simp only [PFun.Dom, Set.mem_setOf_eq, PFun.fn_apply]
  exact ⟨fun h => ⟨h.fst, (Part.get_eq_iff_mem h.fst).mpr h⟩,
         fun ⟨hd, heq⟩ => heq ▸ Part.get_mem hd⟩

/-- `f.fn x h = y ↔ y ∈ f x` -/
lemma fn_eq_iff_mem {f : α →. β} {x : α} {y : β} (h : x ∈ PFun.Dom f) :
    PFun.fn f x h = y ↔ y ∈ f x :=
  ⟨fun heq => heq ▸ fn_mem h, fun hy => Part.mem_unique (fn_mem h) hy⟩

/-- `fn_eq_of_mem: if y ∈ f x and h₂ : x ∈ Dom f, then f.fn x h₂ = y` -/
lemma fn_eq_of_mem {f : α →. β} {x : α} {y : β} (h1 : y ∈ f x) (h2 : x ∈ PFun.Dom f) :
    PFun.fn f x h2 = y :=
  (fn_eq_iff_mem h2).mpr h1

/-- `y ∈ (↑f : α →. β) x ↔ f x = y` -/
lemma mem_lift {f : α → β} {x : α} {y : β} : y ∈ (f : α →. β) x ↔ f x = y := by
  simp [eq_comm]

lemma lift_eq_some_iff {f : α → β} {x : α} {y : β} :
    (f : α →. β) x = Part.some y ↔ f x = y := by simp

@[simp] lemma fn_lift (f : α → β) (x : α) :
    (f : α →. β).fn x trivial = f x := by
  simp [PFun.fn_apply, PFun.coe_val]

/-! ### Empty partial function (src 199-203) -/

/-- The empty partial function -/
def empty : α →. β := fun _ => Part.none

@[simp] lemma dom_empty : PFun.Dom (empty : α →. β) = ∅ := by
  simp [PFun.Dom, empty]

@[simp] lemma empty_def (x : α) : (empty : α →. β) x = Part.none := rfl

lemma not_mem_empty (x : α) (y : β) : y ∉ (empty : α →. β) x := Part.notMem_none _

/-! ### Subfun / le order on PFun (src 287-321) -/

/-- f₁ ≤ f₂ (subfun): ∀ x y, y ∈ f₁ x → y ∈ f₂ x -/
def le (f₁ f₂ : α →. β) : Prop := ∀ x y, y ∈ f₁ x → y ∈ f₂ x

@[refl] lemma le_refl (f : α →. β) : le f f := fun _ _ h => h

lemma le_trans {f g h : α →. β} : le f g → le g h → le f h :=
  fun hfg hgh x y hy => hgh x y (hfg x y hy)

lemma le_antisymm {f g : α →. β} (h1 : le f g) (h2 : le g f) : f = g :=
  PFun.ext (fun x y => ⟨h1 x y, h2 x y⟩)

lemma dom_subset_dom_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) :
    PFun.Dom f₁ ⊆ PFun.Dom f₂ :=
  fun x hx => mem_Dom_of_mem (h x (PFun.fn f₁ x hx) (fn_mem hx))

lemma fn_eq_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) {x : α} {y : β}
    (h1 : x ∈ PFun.Dom f₁) (h2 : PFun.fn f₁ x h1 = y) (h3 : x ∈ PFun.Dom f₂) :
    PFun.fn f₂ x h3 = y := by
  apply fn_eq_of_mem; apply h; rw [mem_iff_fn_eq]; exact ⟨h1, h2⟩

lemma le_lift {f : α →. β} {g : α → β} :
    le f (g : α →. β) ↔ ∀ x y, y ∈ f x → g x = y := by
  simp [le, eq_comm]

/-! ### Compatible (src 324-345) -/

/-- Two functions are compatible if they agree on the intersection of their domains. -/
def compatible (f₁ f₂ : α →. β) : Prop :=
  ∀ (x : α), x ∈ PFun.Dom f₁ → x ∈ PFun.Dom f₂ → f₁ x = f₂ x

lemma compatible_def {f₁ f₂ : α →. β} :
    compatible f₁ f₂ ↔ ∀ (x : α), x ∈ PFun.Dom f₁ → x ∈ PFun.Dom f₂ → f₁ x = f₂ x :=
  Iff.rfl

lemma mem_of_compatible {f₁ f₂ : α →. β} (h : compatible f₁ f₂) {x : α} {y : β}
    (h1 : y ∈ f₁ x) (h2 : x ∈ PFun.Dom f₂) : y ∈ f₂ x := by
  have heq := h x (mem_Dom_of_mem h1) h2
  rw [← heq]; exact h1

@[refl] lemma compatible_refl {f : α →. β} : compatible f f := fun _ _ _ => rfl

lemma compatible_comm {f₁ f₂ : α →. β} : compatible f₁ f₂ ↔ compatible f₂ f₁ := by
  simp only [compatible]
  constructor <;> (intro h x h1 h2; exact (h x h2 h1).symm)

lemma compatible_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) : compatible f₁ f₂ := by
  intro x h1x h2x
  apply Part.ext; intro y; constructor
  · intro hy; exact h x y hy
  · intro hy
    have hstep := h x (PFun.fn f₁ x h1x) (fn_mem h1x)
    have hmem : PFun.fn f₁ x h1x ∈ f₂ x := hstep
    have heq : y = PFun.fn f₁ x h1x := Part.mem_unique hy hmem
    rw [heq]; exact fn_mem h1x

/-! ### Intersection on PFun (src 278-284) -/

/-- The intersection of two partial functions: f₁ ∩ f₂.
    Domain: ∃ y, y ∈ f₁ x ∧ y ∈ f₂ x. Value: f₁(x). -/
noncomputable def pfunInter (f₁ f₂ : α →. β) : α →. β :=
  fun x => ⟨∃ y, y ∈ f₁ x ∧ y ∈ f₂ x,
            fun h => PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec h).1)⟩

@[simp] lemma mem_pfunInter {f₁ f₂ : α →. β} {x : α} {y : β} :
    y ∈ pfunInter f₁ f₂ x ↔ y ∈ f₁ x ∧ y ∈ f₂ x := by
  simp only [pfunInter, Part.mem_eq]
  constructor
  · rintro ⟨hex, rfl⟩
    -- hex : ∃ z, z ∈ f₁ x ∧ z ∈ f₂ x
    -- the Part.get value is PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec hex).1)
    have hcs := Classical.choose_spec hex
    have hd' : x ∈ PFun.Dom f₁ := mem_Dom_of_mem hcs.1
    constructor
    · exact fn_mem hd'
    · have hveq : PFun.fn f₁ x hd' = Classical.choose hex :=
        fn_eq_of_mem hcs.1 hd'
      rw [hveq]; exact hcs.2
  · rintro ⟨hy1, hy2⟩
    refine ⟨⟨y, hy1, hy2⟩, ?_⟩
    apply fn_eq_of_mem hy1

lemma pfunInter_le_left {f₁ f₂ : α →. β} : le (pfunInter f₁ f₂) f₁ :=
  fun x y hy => (mem_pfunInter.mp hy).1

lemma pfunInter_le_right {f₁ f₂ : α →. β} : le (pfunInter f₁ f₂) f₂ :=
  fun x y hy => (mem_pfunInter.mp hy).2

lemma le_pfunInter {f g₁ g₂ : α →. β} (h1 : le f g₁) (h2 : le f g₂) :
    le f (pfunInter g₁ g₂) :=
  fun x y hy => mem_pfunInter.mpr ⟨h1 x y hy, h2 x y hy⟩

/-! ### Sup on PFun (src 351-400) -/

/-- The sup of f₁ and f₂: f₁ x if x ∈ Dom f₁, else f₂ x. -/
noncomputable def pfunSup (f₁ f₂ : α →. β) : α →. β :=
  fun a => if h : a ∈ PFun.Dom f₁ then f₁ a else f₂ a

lemma pfunSup_eq_of_mem {f₁ f₂ : α →. β} {x : α} (h : x ∈ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₁ x := by
  simp only [pfunSup, dif_pos h]

lemma pfunSup_eq_of_nmem {f₁ f₂ : α →. β} {x : α} (h : x ∉ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₂ x := by
  simp only [pfunSup, dif_neg h]

@[simp] lemma dom_pfunSup (f₁ f₂ : α →. β) :
    PFun.Dom (pfunSup f₁ f₂) = PFun.Dom f₁ ∪ PFun.Dom f₂ := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_union]
  by_cases hx : x ∈ PFun.Dom f₁
  · simp only [pfunSup_eq_of_mem hx]; exact ⟨fun h => Or.inl hx, fun _ => hx⟩
  · simp only [pfunSup_eq_of_nmem hx]
    exact ⟨fun h => Or.inr (mem_Dom_of_mem (Part.get_mem h)),
           fun h => h.elim (absurd · hx) id⟩

lemma subset_dom_pfunSup_left (f₁ f₂ : α →. β) : PFun.Dom f₁ ⊆ PFun.Dom (pfunSup f₁ f₂) := by
  intro x hx; rw [dom_pfunSup]; exact Set.mem_union_left _ hx

lemma subset_dom_pfunSup_right (f₁ f₂ : α →. β) : PFun.Dom f₂ ⊆ PFun.Dom (pfunSup f₁ f₂) := by
  intro x hx; rw [dom_pfunSup]; exact Set.mem_union_right _ hx

lemma mem_pfunSup {f₁ f₂ : α →. β} {x : α} {y : β} :
    y ∈ pfunSup f₁ f₂ x ↔ y ∈ f₁ x ∨ (y ∈ f₂ x ∧ x ∉ PFun.Dom f₁) := by
  by_cases hx : x ∈ PFun.Dom f₁
  · rw [pfunSup_eq_of_mem hx]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨_, hnx⟩)
      · exact h
      · exact absurd hx hnx
  · rw [pfunSup_eq_of_nmem hx]
    constructor
    · intro h; exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨h2, _⟩)
      · exact absurd (mem_Dom_of_mem h) hx
      · exact h2

lemma mem_pfunSup_of_compatible {f₁ f₂ : α →. β} {x : α} {y : β}
    (h : compatible f₁ f₂) :
    y ∈ pfunSup f₁ f₂ x ↔ y ∈ f₁ x ∨ y ∈ f₂ x := by
  rw [mem_pfunSup]
  constructor
  · rintro (h1 | ⟨h2, _⟩)
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl h1
    · by_cases hx : x ∈ PFun.Dom f₁
      · left
        have heq := h x hx (mem_Dom_of_mem h2)
        -- heq : f₁ x = f₂ x, so y ∈ f₁ x follows from y ∈ f₂ x and heq
        rw [heq]; exact h2
      · exact Or.inr ⟨h2, hx⟩

lemma le_pfunSup_left (f₁ f₂ : α →. β) : le f₁ (pfunSup f₁ f₂) :=
  fun x y hy => by rw [mem_pfunSup]; exact Or.inl hy

lemma le_pfunSup_right {f₁ f₂ : α →. β} (h : compatible f₁ f₂) : le f₂ (pfunSup f₁ f₂) :=
  fun x y hy => by rw [mem_pfunSup_of_compatible h]; exact Or.inr hy

lemma pfunSup_restrict_left {f₁ f₂ : α →. β} :
    (pfunSup f₁ f₂).restrict (subset_dom_pfunSup_left f₁ f₂) = f₁ := by
  apply PFun.ext; intro x y
  simp only [PFun.mem_restrict, mem_pfunSup]
  constructor
  · rintro ⟨hx, h1 | ⟨_, hnx⟩⟩
    · exact h1
    · exact absurd hx hnx
  · intro hy
    exact ⟨mem_Dom_of_mem hy, Or.inl hy⟩

lemma pfunSup_restrict_right {f₁ f₂ : α →. β} (h : compatible f₁ f₂) :
    (pfunSup f₁ f₂).restrict (subset_dom_pfunSup_right f₁ f₂) = f₂ := by
  apply PFun.ext; intro x y
  simp only [PFun.mem_restrict, mem_pfunSup_of_compatible h]
  constructor
  · rintro ⟨hx, h1 | h2⟩
    · rw [← h x (mem_Dom_of_mem h1) hx]; exact h1
    · exact h2
  · intro hy
    exact ⟨mem_Dom_of_mem hy, Or.inr hy⟩

/-! ### Indexed Sup on PFun (src 405-450) -/

/-- The indexed sup of a family of partial functions. Uses Classical.choose. -/
noncomputable def pSup {ι : Type*} (f : ι → α →. β) : α →. β :=
  fun x => if h : ∃ i, x ∈ PFun.Dom (f i)
           then f (Classical.choose h) x
           else Part.none

lemma pSup_helper {ι : Type*} {f : ι → α →. β} {x : α} :
    (∃ i, x ∈ PFun.Dom (f i)) ↔
    (∃ i, x ∈ PFun.Dom (f i) ∧ pSup f x = f i x) :=
  ⟨fun h => ⟨Classical.choose h, Classical.choose_spec h, dif_pos h⟩,
   fun ⟨i, h, _⟩ => ⟨i, h⟩⟩

lemma pSup_helper2 {ι : Type*} {f : ι → α →. β} {x : α} :
    (∃ i, x ∈ PFun.Dom (f i)) ↔
    (∃ i, ∃ h : x ∈ PFun.Dom (f i), pSup f x = Part.some (PFun.fn (f i) x h)) := by
  rw [pSup_helper]
  apply exists_congr; intro i
  rw [← exists_prop]
  apply exists_congr; intro hi
  apply eq_iff_eq_of_eq_right
  exact (some_fn hi).symm

@[simp] lemma dom_pSup {ι : Type*} (f : ι → α →. β) :
    PFun.Dom (pSup f) = ⋃ (i : ι), PFun.Dom (f i) := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    -- (pSup f x).Dom
    by_cases hex : ∃ i, x ∈ PFun.Dom (f i)
    · -- pSup f x = f (Classical.choose hex) x
      have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
      rw [key] at hx
      exact ⟨Classical.choose hex, mem_Dom_of_mem (Part.get_mem hx)⟩
    · exfalso
      have hkey : pSup f x = Part.none := by simp only [pSup, dif_neg hex]
      rw [hkey] at hx; exact hx
  · rintro ⟨i, hi⟩
    have hex : ∃ j, x ∈ PFun.Dom (f j) := ⟨i, hi⟩
    have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
    rw [key]
    exact Classical.choose_spec hex

lemma subset_dom_pSup {ι : Type*} (f : ι → α →. β) (i : ι) :
    PFun.Dom (f i) ⊆ PFun.Dom (pSup f) := by
  intro x hx
  simp only [dom_pSup, Set.mem_iUnion]
  exact ⟨i, hx⟩

lemma pSup_eq_of_mem {ι : Type*} {f : ι → α →. β} {x : α} {i : ι}
    (hf : ∀ i j, compatible (f i) (f j)) (h : x ∈ PFun.Dom (f i)) :
    pSup f x = f i x := by
  have hex : ∃ i, x ∈ PFun.Dom (f i) := ⟨i, h⟩
  obtain ⟨j, hj, h2j⟩ := pSup_helper.mp hex
  rw [h2j]; exact hf j i x hj h

lemma pSup_eq_of_nmem {ι : Type*} {f : ι → α →. β} {x : α}
    (h : ∀ i, x ∉ PFun.Dom (f i)) :
    pSup f x = Part.none := by
  have hne : ¬∃ i, x ∈ PFun.Dom (f i) := fun ⟨i, hi⟩ => h i hi
  simp only [pSup, dif_neg hne]

/-- mem_pSup: port of pfun.mem_Sup (src lines 444-451). -/
lemma mem_pSup {ι : Type*} {f : ι → α →. β} {x : α} {y : β}
    (hf : ∀ i j, compatible (f i) (f j)) :
    y ∈ pSup f x ↔ ∃ i, y ∈ f i x := by
  constructor
  · intro hy
    have := mem_Dom_of_mem hy
    rw [dom_pSup, Set.mem_iUnion] at this
    rcases this with ⟨i, hi⟩
    exact ⟨i, by rwa [pSup_eq_of_mem hf hi] at hy⟩
  · rintro ⟨i, hi⟩
    rwa [pSup_eq_of_mem hf (mem_Dom_of_mem hi)]

/-! ### Additional Sup lemmas (src 453-470) -/

/-- Sup_restrict: port of pfun.Sup_restrict (src line 453). -/
lemma pSup_restrict {ι : Type*} {f : ι → α →. β} (hf : ∀ i j, compatible (f i) (f j)) (i : ι) :
    (pSup f).restrict (subset_dom_pSup f i) = f i := by
  apply PFun.ext; intros x y
  simp only [PFun.mem_restrict, mem_pSup hf]
  constructor
  · rintro ⟨hx, j, hj⟩; exact mem_of_compatible (hf j i) hj hx
  · intro hy; exact ⟨mem_Dom_of_mem hy, i, hy⟩

/-- le_pSup: port of pfun.le_Sup (src line 462). -/
lemma le_pSup {ι : Type*} {f : ι → α →. β} (hf : ∀ i j, compatible (f i) (f j)) (i : ι) :
    le (f i) (pSup f) := by
  intro x y hy; rw [mem_pSup hf]; exact ⟨i, hy⟩

/-- pSup_le: port of pfun.Sup_le (src line 465). -/
lemma pSup_le {ι : Type*} {f : ι → α →. β} (hf : ∀ i j, compatible (f i) (f j))
    {g : α →. β} : le (pSup f) g ↔ ∀ i, le (f i) g := by
  simp only [le, mem_pSup hf]
  constructor
  · intro h i x y hy; exact h x y ⟨i, hy⟩
  · intro h x y ⟨i, hi⟩; exact h i x y hi

/-! ### singleton PFun (src 489-509) -/

/-- A partial function with one element in its domain. Port of pfun.singleton (src line 489). -/
def singleton (x : α) (y : β) : α →. β :=
  fun a => ⟨a = x, fun _ => y⟩

@[simp] lemma fn_singleton {x x' : α} {y : β} (H_a : x' = x) :
    PFun.fn (singleton x y) x' H_a = y := rfl

@[simp] lemma mem_singleton {x x' : α} {y y' : β} :
    y' ∈ singleton x y x' ↔ x = x' ∧ y = y' := by
  simp only [singleton, Part.mem_mk_iff]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h.symm, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

@[simp] lemma singleton_eq_some {x : α} {y : β} : singleton x y x = Part.some y := by
  simp [singleton, Part.eq_some_iff]

@[simp] lemma dom_singleton {x : α} {y : β} : PFun.Dom (singleton x y) = {x} := by
  ext x'; simp [singleton, PFun.Dom]

lemma mk_dom_singleton {x : α} {y : β} : #(PFun.Dom (singleton x y)) = 1 := by simp

/-! ### extend_via and trivial_extension (src 512-541) -/

/-- Extend `f` using `g` for all values where `f` is undefined.
    Port of pfun.extend_via (src line 512). -/
noncomputable def extend_via (f : α →. β) (g : α → β) : α → β :=
  fun x => if hx : x ∈ PFun.Dom f then PFun.fn f x hx else g x

lemma extend_via_pos {f : α →. β} {g : α → β} {x : α} (h : x ∈ PFun.Dom f) :
    extend_via f g x = PFun.fn f x h := by simp [h, extend_via]

lemma extend_via_neg {f : α →. β} {g : α → β} {x : α} (h : x ∉ PFun.Dom f) :
    extend_via f g x = g x := by simp [h, extend_via]

lemma le_extend_via (f : α →. β) (g : α → β) : le f ↑(extend_via f g) := by
  intro x y hy
  have hx : x ∈ PFun.Dom f := hy.fst
  change y ∈ Part.some (extend_via f g x)
  rw [Part.mem_some_iff, extend_via, dif_pos hx]
  exact Part.mem_unique hy (Part.get_mem hx)

/-- Given a partial function f : X →. Y and a point y : Y, define an extension of f to X
    such that g(x) = y whenever x ∉ f.dom. Port of pfun.trivial_extension (src line 529). -/
noncomputable def trivial_extension (f : α →. β) (y : β) : α → β :=
  extend_via f (fun _ => y)

lemma trivial_extension_pos {f : α →. β} {y : β} {x : α} (h : x ∈ PFun.Dom f) :
    trivial_extension f y x = PFun.fn f x h :=
  extend_via_pos h

lemma trivial_extension_neg {f : α →. β} {y : β} {x : α} (h : x ∉ PFun.Dom f) :
    trivial_extension f y x = y :=
  extend_via_neg h

lemma le_trivial_extension (f : α →. β) (y : β) : le f ↑(trivial_extension f y) :=
  le_extend_via f _

/-! ### pfunRan: the range of a partial function (src 472-484) -/

/-- The range of a partial function. Port of pfun.ran (used in src). -/
def pfunRan {α β : Type*} (f : α →. β) : Set β := {y | ∃ x, y ∈ f x}

lemma mem_pfunRan {α β : Type*} {f : α →. β} {y : β} :
    y ∈ pfunRan f ↔ ∃ x, y ∈ f x := Iff.rfl

lemma fn_mem_pfunRan {α β : Type*} {f : α →. β} {x : α} (Hx : x ∈ PFun.Dom f) :
    PFun.fn f x Hx ∈ pfunRan f :=
  ⟨x, fn_mem Hx⟩

lemma mk_pfunRan_le_mk_dom {α β : Type u} (f : α →. β) : #(pfunRan f) ≤ #(PFun.Dom f) := by
  apply Cardinal.mk_le_of_surjective (f := fun ⟨x, hx⟩ => ⟨f.fn x hx, x, Part.get_mem hx⟩)
  intro ⟨y, x, hy⟩
  have hx : x ∈ PFun.Dom f := hy.fst
  exact ⟨⟨x, hx⟩, Subtype.ext (Part.mem_unique (Part.get_mem hx) hy)⟩

end CPFun

end Flypitch

/-! ## Section collapse_poset (src lines 545-766)
    Port of `section collapse_poset`. -/

namespace Flypitch

open CPFun Set TopologicalSpace Cardinal Flypitch.Regular

/-! ### CollapsePoset structure (src lines 547-621) -/

/-- The collapse poset: finite partial functions from X to Y with domain of cardinality < κ.
    Port of `collapse_poset` (src line 547). -/
structure CollapsePoset (X Y : Type u) (κ : Cardinal.{u}) : Type u where
  f    : X →. Y
  Hc   : #(PFun.Dom f) < κ

namespace CollapsePoset

variable {X Y : Type u} {κ : Cardinal.{u}}

/-- The empty collapse poset. Port of collapse_poset.empty (src line 551). -/
def empty {α β : Type u} {κ : Cardinal} (h : 0 < κ) : CollapsePoset α β κ :=
  { f := CPFun.empty, Hc := by simp [h] }

/-- The cardinality of the range is < κ. Port of collapse_poset.mk_ran_lt (src line 559). -/
lemma mk_ran_lt (p : CollapsePoset X Y κ) : #(CPFun.pfunRan p.f) < κ :=
  lt_of_le_of_lt (CPFun.mk_pfunRan_le_mk_dom p.f) p.Hc

/-- Intersection of two collapse posets. Port of collapse_poset.inter (src line 562). -/
noncomputable def inter (p₁ p₂ : CollapsePoset X Y κ) : CollapsePoset X Y κ :=
  { f := CPFun.pfunInter p₁.f p₂.f,
    Hc := by
      apply lt_of_le_of_lt _ p₁.Hc
      apply Cardinal.mk_le_mk_of_subset
      intro x hx
      have hmem := CPFun.mem_pfunInter.mp (Part.get_mem hx)
      exact CPFun.mem_Dom_of_mem hmem.1 }

/-- Union of two collapse posets (requires ℵ₀ ≤ κ).
    Port of collapse_poset.union (src line 566). -/
noncomputable def union (p₁ p₂ : CollapsePoset X Y κ) (h : ℵ₀ ≤ κ) : CollapsePoset X Y κ :=
  { f := CPFun.pfunSup p₁.f p₂.f,
    Hc := by
      rw [CPFun.dom_pfunSup]
      exact lt_of_le_of_lt (Cardinal.mk_union_le _ _)
        (Cardinal.add_lt_of_lt h p₁.Hc p₂.Hc) }

/-- There exists an x ∉ p.f.dom when κ ≤ #X.
    Port of exists_mem_compl_dom_of_unctbl (src line 572). -/
lemma exists_mem_compl_dom (p : CollapsePoset X Y κ) (H_card : κ ≤ #X) :
    ∃ x : X, x ∉ PFun.Dom p.f :=
  exists_mem_compl_of_mk_lt_mk _ (lt_of_lt_of_le p.Hc H_card)

/-- There exists a y ∉ p.f.ran when κ ≤ #Y.
    Port of exists_mem_compl_ran_of_unctbl (src line 576). -/
lemma exists_mem_compl_ran (p : CollapsePoset X Y κ) (H_card : κ ≤ #Y) :
    ∃ y : Y, y ∉ CPFun.pfunRan p.f :=
  exists_mem_compl_of_mk_lt_mk _ (lt_of_lt_of_le (mk_ran_lt p) H_card)

/-- The principal open set associated with a collapse poset.
    Port of collapse_poset.principal_open (src line 580). -/
def principalOpen (p : CollapsePoset X Y κ) : Set (X → Y) :=
  {f | CPFun.le p.f (f : X →. Y)}

@[simp] lemma principalOpen_empty (h : 0 < κ) :
    principalOpen (empty h : CollapsePoset X Y κ) = Set.univ := by
  ext f; simp [principalOpen, empty, CPFun.le, CPFun.empty]

lemma mem_principalOpen_iff {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ principalOpen p ↔ ∀ x y, y ∈ p.f x → f x = y := by
  simp [principalOpen, CPFun.le_lift]

lemma mem_principalOpen_iff' {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ principalOpen p ↔ ∀ (x : X) (H_x : x ∈ PFun.Dom p.f), f x = PFun.fn p.f x H_x := by
  rw [mem_principalOpen_iff]
  apply forall_congr'; intro x
  constructor
  · intro H Hx; apply H; exact CPFun.fn_mem Hx
  · intro H y hy
    rw [H (CPFun.mem_Dom_of_mem hy)]
    exact CPFun.fn_eq_of_mem hy _

lemma mem_compl_principalOpen_iff {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ (principalOpen p)ᶜ ↔ ∃ x, ∃ H_x : x ∈ PFun.Dom p.f, f x ≠ PFun.fn p.f x H_x := by
  rw [Set.mem_compl_iff, mem_principalOpen_iff']
  push Not
  rfl

lemma mem_ran_of_mem_dom {p : CollapsePoset X Y κ} {f : X → Y} {x : X}
    (H : f ∈ principalOpen p) (H_mem : x ∈ PFun.Dom p.f) : f x ∈ CPFun.pfunRan p.f := by
  rw [mem_principalOpen_iff] at H
  exact ⟨x, by
    have heq := H x (PFun.fn p.f x H_mem) (CPFun.fn_mem H_mem)
    -- heq : f x = PFun.fn p.f x H_mem
    -- goal : f x ∈ p.f x
    rw [heq]; exact CPFun.fn_mem H_mem⟩

/-- The sup of a family of collapse posets (same universe, non-lifted).
    Port of collapse_poset.Sup (src line 613). -/
noncomputable def Sup {ι : Type u} (p : ι → CollapsePoset X Y κ)
    (h : #ι < κ.ord.cof) (hκ : ℵ₀ ≤ κ) : CollapsePoset X Y κ :=
  ⟨CPFun.pSup (fun i => (p i).f),
    by
      rw [CPFun.dom_pSup]
      apply lt_of_le_of_lt (Cardinal.mk_iUnion_le _)
      apply Cardinal.mul_lt_of_lt hκ
      · exact lt_of_lt_of_le h (Ordinal.cof_ord_le κ)
      · exact iSup_lt_of_lt_cof_ord h (fun i => (p i).Hc)⟩

/-- The sup of a family of collapse posets (lifted universe).
    Port of collapse_poset.Sup_lift (src line 622). -/
noncomputable def SupLift {ι : Type u} {X' Y' : Type (max u v)} {κ' : Cardinal.{max u v}}
    (p : ι → CollapsePoset X' Y' κ')
    (h : Cardinal.lift.{v} #ι < κ'.ord.cof)
    (hκ : ℵ₀ ≤ κ') : CollapsePoset X' Y' κ' :=
  ⟨CPFun.pSup (fun i => (p i).f),
    by
      rw [CPFun.dom_pSup]
      have bound : #(⋃ i : ι, PFun.Dom (p i).f) ≤
          Cardinal.lift.{v} #ι * ⨆ i, #(PFun.Dom (p i).f) := by
        have key := @Cardinal.mk_iUnion_le_lift X' ι (fun i => PFun.Dom (p i).f)
        rw [Cardinal.lift_id', Cardinal.lift_umax,
            iSup_congr (fun i => Cardinal.lift_id' _)] at key
        exact key
      apply lt_of_le_of_lt bound
      apply Cardinal.mul_lt_of_lt hκ
      · exact lt_of_lt_of_le h (Ordinal.cof_ord_le κ')
      · exact Ordinal.iSup_lt_lift h (fun i => (p i).Hc)⟩

end CollapsePoset

/-! ### collapse_space: the topology on X → Y (src lines 633-766) -/

/-- The collapse space topology: generated by principal opens.
    Port of collapse_space (src line 633). -/
def collapseSpace (X Y : Type u) : TopologicalSpace (X → Y) :=
  TopologicalSpace.generateFrom
    (Set.image (CollapsePoset.principalOpen (κ := Order.succ ℵ₀)) Set.univ)

section CollapseSpaceLemmas

variable {X Y : Type u}

local instance collapseSpaceInst : TopologicalSpace (X → Y) := collapseSpace X Y

@[simp] lemma principalOpen_isOpen {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsOpen (CollapsePoset.principalOpen p) :=
  TopologicalSpace.GenerateOpen.basic _ (Set.mem_image_of_mem _ trivial)

lemma aleph0_lt_aleph0_succ : ℵ₀ < Order.succ (ℵ₀ : Cardinal) :=
  Order.lt_succ ℵ₀

lemma aleph0_le_aleph0_succ : ℵ₀ ≤ Order.succ (ℵ₀ : Cardinal) :=
  le_of_lt aleph0_lt_aleph0_succ

lemma one_lt_aleph0_succ : 1 < Order.succ (ℵ₀ : Cardinal) :=
  lt_trans Cardinal.one_lt_aleph0 aleph0_lt_aleph0_succ

lemma zero_lt_aleph0_succ : 0 < Order.succ (ℵ₀ : Cardinal) :=
  lt_trans one_pos one_lt_aleph0_succ

/-- singleton collapse poset. Port of singleton_collapse_poset (src line 651). -/
noncomputable def singletonCollapsePoset (x : X) (y : Y) (hκ : 1 < κ) :
    CollapsePoset X Y κ :=
  { f := CPFun.singleton x y,
    Hc := by simp [CPFun.mk_dom_singleton]; exact hκ }

lemma singletonCollapsePoset_principalOpen' {x : X} {y : Y} {hκ : 1 < κ} :
    CollapsePoset.principalOpen (singletonCollapsePoset x y hκ) = {g : X → Y | g x = y} := by
  ext g
  simp only [Set.mem_setOf_eq, CollapsePoset.mem_principalOpen_iff, CPFun.mem_singleton,
             singletonCollapsePoset]
  constructor
  · intro H; exact H x y ⟨rfl, rfl⟩
  · rintro H x' y' ⟨rfl, rfl⟩; exact H

@[simp] lemma singletonCollapsePoset_principalOpen {x : X} {y : Y}
    {hκ : 1 < Order.succ (ℵ₀ : Cardinal)} :
    CollapsePoset.principalOpen (singletonCollapsePoset x y hκ) = {g : X → Y | g x = y} :=
  singletonCollapsePoset_principalOpen'

lemma compl_principalOpen_isUnion (hκ : 1 < κ) (p : CollapsePoset X Y κ) :
    ∃ (ι : Type u) (s : ι → CollapsePoset X Y κ),
      ⋃ i : ι, CollapsePoset.principalOpen (s i) = (CollapsePoset.principalOpen p)ᶜ := by
  use {pr : X × Y // ∃ H_mem : pr.1 ∈ PFun.Dom p.f, pr.2 ≠ PFun.fn p.f pr.1 H_mem}
  use fun s => singletonCollapsePoset s.val.1 s.val.2 hκ
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨x, z⟩, H_mem, H_neq⟩, H_in⟩
    rw [singletonCollapsePoset_principalOpen'] at H_in
    simp only [Set.mem_setOf_eq] at H_in
    rw [CollapsePoset.mem_compl_principalOpen_iff]
    exact ⟨x, H_mem, by rw [H_in]; exact H_neq⟩
  · intro H
    rw [CollapsePoset.mem_compl_principalOpen_iff] at H
    rcases H with ⟨x, H_mem, H_neq⟩
    exact ⟨⟨⟨x, g x⟩, H_mem, H_neq⟩, by
      rw [singletonCollapsePoset_principalOpen']; simp⟩

@[simp] lemma principalOpen_isClosed {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsClosed (CollapsePoset.principalOpen p) := by
  rcases compl_principalOpen_isUnion one_lt_aleph0_succ p with ⟨_, s, Hu⟩
  rw [← isOpen_compl_iff, ← Hu]
  exact isOpen_iUnion (fun i => principalOpen_isOpen)

@[simp] lemma principalOpen_isRegular {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsRegularOpen (CollapsePoset.principalOpen p) :=
  isRegularOpen_of_isClopen ⟨principalOpen_isClosed, principalOpen_isOpen⟩

lemma inter_principalOpen (hκ : ℵ₀ ≤ κ) {p₁ p₂ : CollapsePoset X Y κ}
    (H : CPFun.compatible p₁.f p₂.f) :
    CollapsePoset.principalOpen p₁ ∩ CollapsePoset.principalOpen p₂ =
    CollapsePoset.principalOpen (p₁.union p₂ hκ) := by
  ext f
  simp only [Set.mem_inter_iff, CollapsePoset.mem_principalOpen_iff,
             CollapsePoset.union, CPFun.mem_pfunSup_of_compatible H]
  constructor
  · intro ⟨h1, h2⟩ x y hy
    rcases hy with h | h
    · exact h1 x y h
    · exact h2 x y h
  · intro h
    constructor
    · intro x y hy; exact h x y (Or.inl hy)
    · intro x y hy; exact h x y (Or.inr hy)

/-- The basis for the collapse space. Port of collapse_space_basis (src line 704). -/
def collapseSpaceBasis (X Y : Type u) : Set (Set (X → Y)) :=
  insert (∅ : Set (X → Y))
    (Set.image CollapsePoset.principalOpen
      (Set.univ : Set (CollapsePoset X Y (Order.succ ℵ₀))))

/-- The basis is indeed a topological basis. Port of collapse_space_basis_spec (src line 709). -/
lemma collapseSpaceBasis_spec : IsTopologicalBasis (collapseSpaceBasis X Y) := by
  apply IsTopologicalBasis.mk
  · -- Condition 1: For every pair P, P' in the basis and f ∈ P ∩ P', find P'' ∈ basis with f ∈ P'' ⊆ P ∩ P'
    intro P HP P' HP' f H_mem_inter
    rw [collapseSpaceBasis] at HP HP'
    rcases HP with rfl | ⟨p, _, rfl⟩ <;> rcases HP' with rfl | ⟨p', _, rfl⟩
    · exact absurd H_mem_inter.1 (Set.notMem_empty _)
    · exact absurd H_mem_inter.1 (Set.notMem_empty _)
    · exact absurd H_mem_inter.2 (Set.notMem_empty _)
    · -- Both are principal opens
      have hle : ℵ₀ ≤ Order.succ (ℵ₀ : Cardinal) := aleph0_le_aleph0_succ
      by_cases H_compat : CPFun.compatible p.f p'.f
      · -- Use the union poset
        refine ⟨CollapsePoset.principalOpen (p.union p' hle),
               Set.mem_insert_of_mem _ ⟨p.union p' hle, trivial, rfl⟩,
               ?_, ?_⟩
        · rw [inter_principalOpen hle H_compat] at H_mem_inter; exact H_mem_inter
        · rw [← inter_principalOpen hle H_compat]
      · -- Incompatible: intersection is empty, contradiction
        exfalso
        rcases H_mem_inter with ⟨H₁, H₂⟩
        rw [CollapsePoset.mem_principalOpen_iff] at H₁ H₂
        rw [CPFun.compatible] at H_compat
        push Not at H_compat
        rcases H_compat with ⟨x, hx₁, hx₂, hneq⟩
        apply hneq
        have e1 := H₁ x (PFun.fn p.f x hx₁) (CPFun.fn_mem hx₁)
        have e2 := H₂ x (PFun.fn p'.f x hx₂) (CPFun.fn_mem hx₂)
        -- e1 : f x = PFun.fn p.f x hx₁
        -- e2 : f x = PFun.fn p'.f x hx₂
        -- need : p.f x = p'.f x
        rw [← CPFun.some_fn hx₁, ← CPFun.some_fn hx₂, ← e1, e2]
  · -- Condition 2: sUnion of basis = univ
    simp only [Set.sUnion_eq_univ_iff, collapseSpaceBasis]
    intro f
    exact ⟨CollapsePoset.principalOpen (CollapsePoset.empty zero_lt_aleph0_succ),
           Set.mem_insert_of_mem _ ⟨_, trivial, rfl⟩,
           by simp [CollapsePoset.principalOpen_empty]⟩
  · -- Condition 3: generateFrom (collapseSpaceBasis) = collapseSpaceInst
    simp only [collapseSpaceBasis, collapseSpace]
    apply _root_.le_antisymm
    · rw [le_generateFrom_iff_subset_isOpen]
      intro T HT
      simp only [Set.mem_insert_iff] at HT
      rcases HT with rfl | HT
      · exact @isOpen_empty _ (generateFrom _)
      · exact isOpen_generateFrom_of_mem HT
    · exact generateFrom_anti (Set.subset_insert _ _)

@[simp] lemma isRegular_singletonPrincipalOpen {x : X} {y : Y} :
    IsRegularOpen (CollapsePoset.principalOpen
      (singletonCollapsePoset x y one_lt_aleph0_succ)) :=
  principalOpen_isRegular

@[simp] lemma isRegular_setOf {x : X} {y : Y} :
    IsRegularOpen {g : X → Y | g x = y} := by
  rw [← singletonCollapsePoset_principalOpen (hκ := one_lt_aleph0_succ)]
  exact isRegular_singletonPrincipalOpen

lemma trivialExtension_mem_principalOpen {p : CollapsePoset X Y κ} {y : Y} :
    CPFun.trivial_extension p.f y ∈ CollapsePoset.principalOpen p := by
  rw [CollapsePoset.mem_principalOpen_iff]
  intro x z hz
  rw [CPFun.trivial_extension_pos (CPFun.mem_Dom_of_mem hz)]
  exact CPFun.fn_eq_of_mem hz _

end CollapseSpaceLemmas

/-! ## Section omega_closed_dense_subset (src lines 768-797) -/

section OmegaClosedDense

variable {α : Type*} [NontrivialCompleteBooleanAlgebra α]

/-- Any ω-indexed downward chain in D has an intersection in D.
    Port of omega_closed (src line 773). -/
def OmegaClosed (D : Set α) : Prop :=
  ∀ (s : ℕ → α), (∀ n, s n ∈ D) → (∀ n, ⊥ < s n) → (∀ n, s (n + 1) ≤ s n) → (⨅ n, s n) ∈ D

/-- Dense subset: ⊥ ∉ D and every nonzero element has something in D below it.
    Port of dense_subset (src line 776). -/
def DenseSubset (D : Set α) : Prop :=
  ⊥ ∉ D ∧ ∀ x, ⊥ < x → ∃ y ∈ D, y ≤ x

/-- Port of dense_omega_closed_subset (src line 779). -/
def DenseOmegaClosed (D : Set α) : Prop :=
  DenseSubset D ∧ OmegaClosed D

lemma nonzero_of_mem_DenseOmegaClosed {x : α} {D : Set α}
    (H : DenseOmegaClosed D) (H_mem : x ∈ D) : ⊥ < x := by
  rcases H.1 with ⟨hbot, _⟩
  rcases lt_or_eq_of_le (bot_le (a := x)) with h | h
  · exact h
  · exact absurd (h ▸ H_mem) hbot

lemma nonzero_iInf_of_mem_DenseOmegaClosed {s : ℕ → α} {D : Set α}
    (H : DenseOmegaClosed D) (H_chain : ∀ n, s (n + 1) ≤ s n)
    (H_mem : ∀ n, s n ∈ D) : ⊥ < ⨅ n, s n := by
  apply nonzero_of_mem_DenseOmegaClosed H
  exact H.2 s H_mem (fun n => nonzero_of_mem_DenseOmegaClosed H (H_mem n)) H_chain

end OmegaClosedDense

/-! ## Section collapse_algebra (src lines 800-812) -/

/-- The collapse algebra: regular opens of X → Y with the collapse topology.
    Port of collapse_algebra (src line 805). -/
noncomputable def CollapseAlgebra (X Y : Type u) : Type u :=
  @RegularOpens (X → Y) (collapseSpace X Y)

variable {X Y : Type u}

/-- CollapseAlgebra is a NontrivialCompleteBooleanAlgebra when X → Y is nonempty.
    Port of collapse_algebra_boolean_algebra (src line 809). -/
noncomputable instance collapseAlgebra_ncba [Nonempty (X → Y)] :
    NontrivialCompleteBooleanAlgebra (CollapseAlgebra X Y) :=
  @RegularOpens.instNontrivialCBA (X → Y) (collapseSpace X Y) ‹_›

/-! ## Section collapse_poset_dense (src lines 814-906) -/

section CollapsePosetDense

local instance collapseSpaceInst' : TopologicalSpace (X → Y) := collapseSpace X Y

/-- Inclusion of a collapse poset into the collapse algebra.
    Port of collapse_poset.inclusion (src line 817). -/
noncomputable def collapseInclusion (p : CollapsePoset X Y (Order.succ ℵ₀)) :
    CollapseAlgebra X Y :=
  ⟨CollapsePoset.principalOpen p, principalOpen_isRegular⟩

local notation "ι" => collapseInclusion

lemma collapsePoset_dense_basis :
    ∀ T ∈ collapseSpaceBasis X Y, ∀ _h_nonempty : T ≠ ∅,
      ∃ p : CollapsePoset X Y (Order.succ ℵ₀), (ι p).val ⊆ T := by
  intro T H_mem_basis h_ne
  rcases H_mem_basis with rfl | ⟨p, _, rfl⟩
  · exact absurd rfl h_ne
  · exact ⟨p, le_refl _⟩

lemma collapsePoset_dense [Nonempty (X → Y)] {b : CollapseAlgebra X Y}
    (H : ⊥ < b) : ∃ p : CollapsePoset X Y (Order.succ ℵ₀), ι p ≤ b := by
  have hne : b.val.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply ne_of_gt H
    apply RegularOpens.ext
    rw [h, ← RegularOpens.bot_val]; rfl
  rcases hne with ⟨f, hf⟩
  have hopen : IsOpen b.val := isOpen_of_isRegularOpen b.property
  rcases collapseSpaceBasis_spec.exists_subset_of_mem_open hf hopen with ⟨v, hv₁, hv₂, hv₃⟩
  have hv_ne : v ≠ ∅ := fun h => absurd (h ▸ hv₂) (Set.notMem_empty _)
  rcases collapsePoset_dense_basis v hv₁ hv_ne with ⟨p, hp⟩
  exact ⟨p, hp.trans hv₃⟩

/-- Port of compatible_of_inclusion_le_inclusion (src line 845). -/
lemma compatible_of_inclusion_le [Nonempty (X → Y)]
    {p q : CollapsePoset X Y (Order.succ ℵ₀)} (h : ι p ≤ ι q) : CPFun.compatible p.f q.f := by
  simp only [collapseInclusion, RegularOpens.le_iff_subset] at h
  intro x px qx
  have key : CPFun.trivial_extension p.f (PFun.fn p.f x px) ∈ CollapsePoset.principalOpen q :=
    h trivialExtension_mem_principalOpen
  rw [CollapsePoset.mem_principalOpen_iff] at key
  have hfx := key x (PFun.fn q.f x qx) (CPFun.fn_mem qx)
  rw [CPFun.trivial_extension_pos px] at hfx
  -- hfx : PFun.fn p.f x px = PFun.fn q.f x qx
  -- goal: p.f x = q.f x
  rw [← CPFun.some_fn px, ← CPFun.some_fn qx]
  congr 1

lemma principal_open_eq_iInf_of_eq_inter [Nonempty (X → Y)] {I : Type*}
    {s : I → CollapseAlgebra X Y} {s_infty : CollapseAlgebra X Y}
    (H_eq_inter : s_infty.val = ⋂ n, (s n).val) : s_infty = ⨅ n, s n := by
  apply @RegularOpens.ext _ (collapseSpace X Y)
  rw [show (⨅ n, s n : CollapseAlgebra X Y).val = (⋂ i, (s i).val)ᵖᵖ from
      @RegularOpens.fst_iInf _ (collapseSpace X Y) I s]
  rw [← H_eq_inter]
  exact (@Flypitch.Regular.isRegularOpen_eq_p_p _ (collapseSpace X Y) _ s_infty.property).symm

/-- Principal opens form a dense ω-closed subset of the collapse algebra.
    Port of principal_opens_dense_omega_closed (src line 867). -/
lemma principalOpens_denseOmegaClosed [Nonempty (X → Y)] :
    DenseOmegaClosed (Set.range ι : Set (CollapseAlgebra X Y)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- ⊥ ∉ range ι: principalOpen p ≠ ∅ because trivial_extension witnesses it
    rintro ⟨p, hp⟩
    have hval : (collapseInclusion p).val = (⊥ : CollapseAlgebra X Y).val := congr_arg _ hp
    simp only [collapseInclusion, Subtype.coe_mk] at hval
    have hbot : (⊥ : CollapseAlgebra X Y).val = ∅ := RegularOpens.bot_val
    rw [hbot] at hval
    obtain ⟨g⟩ := ‹Nonempty (X → Y)›
    have hmem : CPFun.extend_via p.f g ∈ CollapsePoset.principalOpen p := by
      rw [CollapsePoset.mem_principalOpen_iff]
      intro x y hy
      have hx : x ∈ PFun.Dom p.f := hy.fst
      rw [CPFun.extend_via_pos hx]
      exact Part.mem_unique (Part.get_mem hx) hy
    rw [hval] at hmem
    exact Set.notMem_empty _ hmem
  · -- Dense: every nonzero element has something in range ι below it
    intro o ho
    have h2o : o.val ≠ ∅ := by
      intro h; apply ne_of_gt ho
      apply RegularOpens.ext
      rw [h, ← RegularOpens.bot_val]; rfl
    have hopen : IsOpen o.val := isOpen_of_isRegularOpen o.property
    have hone : o.val.Nonempty := Set.nonempty_iff_ne_empty.mpr h2o
    rcases hone with ⟨f, hf⟩
    rcases collapseSpaceBasis_spec.exists_subset_of_mem_open hf hopen with ⟨u, hu, h2u, h3u⟩
    have hu_ne : u ≠ ∅ := fun h => absurd (h ▸ h2u) (Set.notMem_empty _)
    rcases collapsePoset_dense_basis u hu hu_ne with ⟨p, hp⟩
    exact ⟨ι p, Set.mem_range_self p, hp.trans h3u⟩
  · -- OmegaClosed: ω-indexed downward chain (src/collapse.lean:882-905)
    -- We build P := CollapsePoset.Sup of the chain (using ULift.{u} ℕ since the
    -- index type must live in `Type u`), then show principalOpen P equals the
    -- intersection ⋂ n, principalOpen (g n), so ι P is the infimum.
    intro f hf hpos h3f
    choose g hg using hf
    simp only [(hg _).symm] at h3f ⊢
    clear hg hpos f
    -- Descending chain on the inclusions
    have hdesc : ∀ ⦃i j : ℕ⦄, i ≤ j → ι (g j) ≤ ι (g i) := by
      intro i j hij
      induction hij with
      | refl => exact le_refl _
      | step _ ih => exact (h3f _).trans ih
    -- Pairwise compatibility of the underlying CPFuns
    have hcompat : ∀ (i j : ℕ), CPFun.compatible (g i).f (g j).f := by
      intro i j
      rcases le_total i j with h | h
      · rw [CPFun.compatible_comm]
        exact compatible_of_inclusion_le (hdesc h)
      · exact compatible_of_inclusion_le (hdesc h)
    -- Lift the index to Type u, then form Sup
    let g' : ULift.{u} ℕ → CollapsePoset X Y (Order.succ ℵ₀) := fun n => g n.down
    have hreg : Cardinal.IsRegular (Order.succ (ℵ₀ : Cardinal.{u})) :=
      Cardinal.isRegular_succ le_rfl
    have h_cof : #(ULift.{u} ℕ) < (Order.succ (ℵ₀ : Cardinal.{u})).ord.cof := by
      rw [hreg.cof_ord, Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
      exact aleph0_lt_aleph0_succ
    let P : CollapsePoset X Y (Order.succ ℵ₀) :=
      CollapsePoset.Sup g' h_cof aleph0_le_aleph0_succ
    have hcompat' : ∀ (i j : ULift.{u} ℕ), CPFun.compatible (g' i).f (g' j).f :=
      fun i j => hcompat i.down j.down
    refine ⟨P, ?_⟩
    -- Show ι P = ⨅ n, ι (g n) by establishing the inter equality on .val
    apply principal_open_eq_iInf_of_eq_inter
    -- Goal: (ι P).val = ⋂ n, (ι (g n)).val
    show CollapsePoset.principalOpen P = ⋂ n, CollapsePoset.principalOpen (g n)
    ext h
    simp only [Set.mem_iInter, CollapsePoset.mem_principalOpen_iff]
    constructor
    · -- h ∈ principalOpen P → ∀ k, h ∈ principalOpen (g k)
      intro H k x y Hy
      apply H x y
      -- y ∈ P.f x ↔ ∃ i, y ∈ (g' i).f x; supply i = ⟨k⟩
      change y ∈ CPFun.pSup (fun i : ULift.{u} ℕ => (g' i).f) x
      rw [CPFun.mem_pSup hcompat']
      exact ⟨ULift.up k, Hy⟩
    · -- (∀ k, h ∈ principalOpen (g k)) → h ∈ principalOpen P
      intro H x y Hy
      change y ∈ CPFun.pSup (fun i : ULift.{u} ℕ => (g' i).f) x at Hy
      rw [CPFun.mem_pSup hcompat'] at Hy
      obtain ⟨i, hi⟩ := Hy
      exact H i.down x y hi

end CollapsePosetDense

/-! ## Final: collapse_boolean_algebra (src lines 910-916) -/

/-- Port of has_dense_omega_closed_subset (src line 783). -/
def HasDenseOmegaClosed (α : Type*) [NontrivialCompleteBooleanAlgebra α] : Prop :=
  ∃ D : Set α, DenseOmegaClosed D

end Flypitch

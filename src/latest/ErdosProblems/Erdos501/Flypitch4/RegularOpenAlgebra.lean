/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/regular_open_algebra.lean (complete, lines 1-722).

Namespace: everything lives in `Flypitch` namespace to avoid clashing with mathlib's `IsRegular`.
The `ᵖ` postfix for `perp` is declared globally after the namespace.
-/

import ErdosProblems.Erdos501.Flypitch4.SetTheoryExt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens

set_option relaxedAutoImplicit true

open Set TopologicalSpace

universe u

namespace Flypitch

/-! ## topology_lemmas section -/

section topology_lemmas

variable {α : Type u} [TopologicalSpace α]

/-- A set S is dense: it meets every nonempty open set. -/
def Dense' (S : Set α) : Prop :=
  ∀ U : Set α, IsOpen U → U.Nonempty → (U ∩ S).Nonempty

/-- S is relatively dense in S₀: every open set meeting S₀ also meets S₀ ∩ S. -/
def RelDense (S₀ S : Set α) : Prop :=
  ∀ U : Set α, IsOpen U → (U ∩ S₀).Nonempty → (U ∩ S₀ ∩ S).Nonempty

/-- Dense' S corresponds to mathlib's Dense. -/
lemma dense'_iff_mathlib {S : Set α} : Dense' S ↔ Dense S :=
  dense_iff_inter_open.symm

lemma closure_univ_of_dense {S : Set α} (H_dense : Dense' S) : closure S = Set.univ :=
  (dense'_iff_mathlib.mp H_dense).closure_eq

lemma closure_rel_dense_of_open {S₀ S : Set α} (H_open : IsOpen S₀)
    (H_rel_dense : RelDense S₀ S) : closure S ∩ S₀ = S₀ := by
  ext x; constructor
  · exact fun ⟨_, H₂⟩ => H₂
  · intro H_mem
    refine ⟨?_, H_mem⟩
    rw [mem_closure_iff]
    intro o Ho hxo
    have h_ne : (o ∩ S₀).Nonempty := ⟨x, hxo, H_mem⟩
    rcases H_rel_dense o Ho h_ne with ⟨y, ⟨⟨hy_o, _⟩, hy_S⟩⟩
    exact ⟨y, hy_o, hy_S⟩

/-- S is dense in basis 𝓑 if S meets every nonempty B ∈ 𝓑. -/
def DenseInBasis (S : Set α) {𝓑 : Set (Set α)} (_H_basis : IsTopologicalBasis 𝓑) : Prop :=
  ∀ B ∈ 𝓑, B.Nonempty → (B ∩ S).Nonempty

lemma dense_of_dense_in_basis (S : Set α) {𝓑 : Set (Set α)}
    (H_basis : IsTopologicalBasis 𝓑) (H : DenseInBasis S H_basis) : Dense' S := by
  intro U HU ⟨a, Ha⟩
  rcases H_basis.exists_subset_of_mem_open Ha HU with ⟨B, HB₁, HB₂, HB₃⟩
  rcases H B HB₁ ⟨a, HB₂⟩ with ⟨x, hxB, hxS⟩
  exact ⟨x, HB₃ hxB, hxS⟩

/-- S is relatively dense in S₀ with respect to basis 𝓑. -/
def RelDenseInBasis (S₀ : Set α) (S : Set α) {𝓑 : Set (Set α)}
    (_H_basis : IsTopologicalBasis 𝓑) : Prop :=
  ∀ B ∈ 𝓑, (B ∩ S₀).Nonempty → (B ∩ S₀ ∩ S).Nonempty

lemma rel_dense_of_dense_in_basis (S₀ : Set α) (S : Set α) {𝓑 : Set (Set α)}
    (H_basis : IsTopologicalBasis 𝓑) (H : RelDenseInBasis S₀ S H_basis) : RelDense S₀ S := by
  intro U HU ⟨a, ha_U, ha_S₀⟩
  rcases H_basis.exists_subset_of_mem_open ha_U HU with ⟨B, HB₁, HB₂, HB₃⟩
  rcases H B HB₁ ⟨a, HB₂, ha_S₀⟩ with ⟨x, ⟨hxB, hxS₀⟩, hxS⟩
  exact ⟨x, ⟨HB₃ hxB, hxS₀⟩, hxS⟩

/-- S is nowhere dense if interior(closure S) = ∅. -/
def NowhereDense (S : Set α) : Prop := interior (closure S) = ∅

lemma frontier_closed_of_open {S : Set α} (_H : IsOpen S) : IsClosed (frontier S) :=
  isClosed_frontier

/-- The frontier of an open set is nowhere dense. -/
lemma frontier_nowhere_dense_of_open {S : Set α} (H : IsOpen S) : NowhereDense (frontier S) := by
  unfold NowhereDense
  rw [isClosed_frontier.closure_eq, Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx_frontier : x ∈ frontier S := interior_subset hx
  have hx_cl : x ∈ closure S := hx_frontier.1
  rw [mem_interior] at hx
  rcases hx with ⟨t, ht_sub, ht_open, hxt⟩
  have ht_S : t ∩ S = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨hyt, hyS⟩; exact (H.frontier_eq ▸ ht_sub hyt).2 hyS
  have hxt_cl : (closure S ∩ t).Nonempty := ⟨x, hx_cl, hxt⟩
  rw [closure_inter_open_nonempty_iff ht_open] at hxt_cl
  rcases hxt_cl with ⟨y, hyS, hyt⟩
  exact absurd (show y ∈ t ∩ S from ⟨hyt, hyS⟩) (by simp [ht_S])

lemma isClopen_interior' {S : Set α} (H : IsClopen S) : interior S = S := H.2.interior_eq
lemma isClopen_closure' {S : Set α} (H : IsClopen S) : closure S = S := H.1.closure_eq

end topology_lemmas

/-! ## regular section -/

section regular

variable {α : Type u} [TopologicalSpace α]

/-- A set S is regular open if S = interior(closure S). -/
def IsRegularOpen (S : Set α) : Prop := S = interior (closure S)

/-- The perp of S: the complement of the closure. -/
def perp (S : Set α) : Set α := (closure S)ᶜ

end regular

end Flypitch

-- Declare ᵖ postfix globally (outside namespace)
postfix:80 "ᵖ" => Flypitch.perp

/-! ## Lemmas about perp and IsRegularOpen in namespace Flypitch.Regular -/

namespace Flypitch.Regular

open Flypitch

variable {α : Type u} [TopologicalSpace α]

@[simp] lemma perp_unfold (S : Set α) : Sᵖ = (closure S)ᶜ := rfl

lemma perp_eq_int_neg {S : Set α} : Sᵖ = interior Sᶜ := by
  simp [Flypitch.perp, interior_compl]

lemma mem_perp_iff {S : Set α} {x : α} :
    x ∈ Sᵖ ↔ ∃ T, T ∩ S = ∅ ∧ IsOpen T ∧ x ∈ T := by
  rw [perp_eq_int_neg, mem_interior]
  constructor
  · rintro ⟨t, ht_sub, ht_open, hx⟩
    refine ⟨t, ?_, ht_open, hx⟩
    ext y; simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    intro ⟨hyt, hyS⟩; exact absurd hyS (ht_sub hyt)
  · rintro ⟨t, ht_inter, ht_open, hx⟩
    refine ⟨t, fun y hy => ?_, ht_open, hx⟩
    simp only [mem_compl_iff]
    intro hyS
    exact absurd (show y ∈ t ∩ S from ⟨hy, hyS⟩) (by rw [ht_inter]; exact notMem_empty y)

@[simp] lemma isOpen_perp {S : Set α} : IsOpen (Sᵖ) := isClosed_closure.isOpen_compl
@[simp] lemma perp_univ : (Set.univ : Set α)ᵖ = ∅ := by simp [Flypitch.perp]
@[simp] lemma perp_empty : (∅ : Set α)ᵖ = Set.univ := by simp [Flypitch.perp]

@[simp] lemma isOpen_of_isRegularOpen {S : Set α} (H : IsRegularOpen S) : IsOpen S := by
  rw [H]; exact isOpen_interior

@[simp] lemma isRegularOpen_of_isClopen {S : Set α} (H : IsClopen S) : IsRegularOpen S := by
  unfold IsRegularOpen; rw [H.1.closure_eq, H.2.interior_eq]

lemma p_p_eq_int_cl {S : Set α} : Sᵖᵖ = interior (closure S) := by
  simp only [perp_unfold, closure_compl, compl_compl]

lemma int_cl_eq_p_p {S : Set α} : interior (closure S) = Sᵖᵖ := p_p_eq_int_cl.symm

lemma regular_iff_p_p {S : Set α} : IsRegularOpen S ↔ Sᵖᵖ = S := by
  rw [IsRegularOpen, ← p_p_eq_int_cl]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma mem_int_cl_iff_mem_eq_p_p {S : Set α} {a : α} :
    a ∈ interior (closure S) ↔ a ∈ Sᵖᵖ := by rw [int_cl_eq_p_p]

lemma isOpen_of_p_p {S : Set α} (H : Sᵖᵖ = S) : IsOpen S := by
  rw [p_p_eq_int_cl] at H; exact H ▸ isOpen_interior

@[simp] lemma isRegularOpen_empty : IsRegularOpen (∅ : Set α) := by simp [IsRegularOpen]
@[simp] lemma isRegularOpen_univ : IsRegularOpen (Set.univ : Set α) := by simp [IsRegularOpen]

lemma p_anti {P Q : Set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ :=
  compl_subset_compl.mpr (closure_mono H)

lemma p_p_mono {P Q : Set α} (H : P ⊆ Q) : Pᵖᵖ ⊆ Qᵖᵖ := p_anti (p_anti H)

lemma in_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := by
  rw [p_p_eq_int_cl]; exact H.subset_interior_iff.mpr subset_closure

@[simp] lemma isRegularOpen_eq_p_p {S : Set α} (H : IsRegularOpen S) : Sᵖᵖ = S := by
  rw [regular_iff_p_p] at H; exact H

lemma isRegularOpen_stable_subset {S₁ S₂ : Set α} (H : IsRegularOpen S₂) (H₂ : S₁ ⊆ S₂) :
    S₁ᵖᵖ ⊆ S₂ := by
  have h := p_p_mono H₂; rwa [isRegularOpen_eq_p_p H] at h

lemma subset_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := in_p_p_of_open H

lemma subset_int_cl_of_open {S : Set α} (H : IsOpen S) : S ⊆ interior (closure S) := by
  rw [← p_p_eq_int_cl]; exact subset_p_p_of_open H

lemma p_eq_p_p_p {S : Set α} (H : IsOpen S) : Sᵖ = Sᵖᵖᵖ :=
  le_antisymm (in_p_p_of_open isOpen_perp) (p_anti (in_p_p_of_open H))

@[simp] lemma p_p_p_p_eq_p_p {S : Set α} : Sᵖᵖᵖᵖ = Sᵖᵖ :=
  (p_eq_p_p_p (isOpen_perp (S := S))).symm

@[simp] lemma isOpen_of_p_p' {S : Set α} : IsOpen (Sᵖᵖ) := by
  rw [p_p_eq_int_cl]; exact isOpen_interior

@[simp] lemma isRegularOpen_p_p {S : Set α} : IsRegularOpen (Sᵖᵖ) := by
  rw [regular_iff_p_p]; exact p_p_p_p_eq_p_p

lemma isRegularOpen_sup {S₁ S₂ : Set α} : IsRegularOpen ((S₁ ∪ S₂)ᵖᵖ) := isRegularOpen_p_p

/-- For open S₁: S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂). -/
lemma inter_eq_inter_aux (S₁ S₂ : Set α) (H : IsOpen S₁) :
    S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂) := by
  intro x ⟨hx1, hx2⟩
  have := H.closure_inter (s := S₂) ⟨hx2, hx1⟩
  rwa [Set.inter_comm S₂ S₁] at this

@[simp] lemma cl_compl_of_isOpen (S : Set α) (H : IsOpen S) : closure Sᶜ = Sᶜ :=
  H.isClosed_compl.closure_eq

lemma inter_eq_inter_aux₂ (S₁ S₂ : Set α) (H₁ : IsOpen S₁) (_H₂ : IsOpen S₂) :
    S₁ ∩ S₂ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
  rw [p_p_eq_int_cl, p_p_eq_int_cl]
  intro x ⟨hx1, hx2⟩
  rw [mem_interior] at hx2 ⊢
  rcases hx2 with ⟨t, ht_sub, ht_open, hxt⟩
  exact ⟨S₁ ∩ t, (Set.inter_subset_inter_right S₁ ht_sub).trans (inter_eq_inter_aux S₁ S₂ H₁),
    H₁.inter ht_open, hx1, hxt⟩

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : Set α} (H₁ : IsOpen S₁) (H₂ : IsOpen S₂) :
    (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ := by
  apply le_antisymm
  · exact fun x hx => ⟨p_p_mono Set.inter_subset_left hx,
                        p_p_mono Set.inter_subset_right hx⟩
  · intro x ⟨hx1, hx2⟩
    have sub1 : S₁ᵖᵖ ∩ S₂ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      intro y ⟨hy1, hy2⟩
      have h := inter_eq_inter_aux₂ S₂ S₁ H₂ H₁ ⟨hy2, hy1⟩
      rwa [Set.inter_comm] at h
    have sub2 : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      have := p_p_mono sub1; rwa [p_p_p_p_eq_p_p] at this
    have step := inter_eq_inter_aux₂ (S₁ᵖᵖ) S₂ (isOpen_of_p_p' (S := S₁)) H₂
    exact sub2 (step ⟨hx1, hx2⟩)

@[simp] lemma isRegularOpen_inter {S₁ S₂ : Set α} (H₁ : IsRegularOpen S₁)
    (H₂ : IsRegularOpen S₂) : IsRegularOpen (S₁ ∩ S₂) := by
  rw [regular_iff_p_p] at *
  rw [p_p_inter_eq_inter_p_p (isOpen_of_p_p H₁) (isOpen_of_p_p H₂), H₁, H₂]

lemma Union_perp_subset (C : Set (Set α)) : ⋃₀ (Flypitch.perp '' C) ⊆ (⋂₀ C)ᵖ := by
  intro x hx
  simp only [mem_sUnion, mem_image] at hx
  rcases hx with ⟨_, ⟨s, hs, rfl⟩, hxs⟩
  simp only [perp_unfold, mem_compl_iff] at hxs ⊢
  exact fun hx_sInter => hxs (closure_mono (sInter_subset_of_mem hs) hx_sInter)

lemma perp_sUnion_perp {C : Set (Set α)} (h : ∀ s ∈ C, IsRegularOpen s) :
    (⋃₀ (Flypitch.perp '' C))ᵖ = (⋂₀ C)ᵖᵖ := by
  refine subset_antisymm ?_ (p_anti (Union_perp_subset C))
  intro x hx
  rw [perp_eq_int_neg] at hx
  rw [p_p_eq_int_cl]
  rw [mem_interior] at hx ⊢
  rcases hx with ⟨t, ht_sub, ht_open, hxt⟩
  have ht_sInter : t ⊆ ⋂₀ C := by
    intro y hy; rw [mem_sInter]; intro s hs
    have hy_not_union : y ∉ ⋃₀ (Flypitch.perp '' C) := ht_sub hy
    have hy_not_perp : y ∉ Flypitch.perp s := fun hp =>
      hy_not_union ⟨Flypitch.perp s, ⟨s, hs, rfl⟩, hp⟩
    simp only [perp_unfold, mem_compl_iff, not_not] at hy_not_perp
    have ht_cl_s : t ⊆ closure s := by
      intro z hz
      have hz_not_union : z ∉ ⋃₀ (Flypitch.perp '' C) := ht_sub hz
      have hz_not_perp : z ∉ Flypitch.perp s := fun hp =>
        hz_not_union ⟨_, ⟨s, hs, rfl⟩, hp⟩
      simpa [perp_unfold, mem_compl_iff] using hz_not_perp
    have ht_int_cl_s : t ⊆ interior (closure s) := ht_open.subset_interior_iff.mpr ht_cl_s
    rw [← isRegularOpen_eq_p_p (h s hs), p_p_eq_int_cl]
    exact ht_int_cl_s hy
  exact ⟨t, ht_sInter.trans subset_closure, ht_open, hxt⟩

end Flypitch.Regular

/-! ## regular_algebra section

Port of: `section regular_algebra` (src/regular_open_algebra.lean lines 349-722).
Builds the complete Boolean algebra structure on regular open sets.
-/

namespace Flypitch

open Flypitch.Regular

/-! ### The type of regular open sets -/

/-- The type of regular open sets of a topological space.
Port of: `def regular_opens` (src/regular_open_algebra.lean:364). -/
def RegularOpens (α : Type u) [TopologicalSpace α] : Type u :=
  {S : Set α // IsRegularOpen S}

namespace RegularOpens

variable {α : Type u} [TopologicalSpace α]

instance instCoe : CoeTC (RegularOpens α) (Set α) := ⟨Subtype.val⟩

@[ext] theorem ext {x y : RegularOpens α} (h : (x : Set α) = y) : x = y := Subtype.ext h

-- Helper: extract val image of a set of regular opens
-- (using Set.image (·.val) avoids the ↑𝒮 coercion issue in where blocks)
private def roVals (𝒮 : Set (RegularOpens α)) : Set (Set α) := Set.image (·.val) 𝒮

@[simp] lemma mem_roVals {𝒮 : Set (RegularOpens α)} {S : Set α} :
    S ∈ roVals 𝒮 ↔ ∃ r ∈ 𝒮, r.val = S := Iff.rfl

lemma roVals_eq_image (𝒮 : Set (RegularOpens α)) :
    roVals 𝒮 = Subtype.val '' 𝒮 := rfl

/-! ### Key set lemmas -/

private lemma compl_isRO' (x : RegularOpens α) : IsRegularOpen (Flypitch.perp x.val) := by
  rw [regular_iff_p_p]
  exact (p_eq_p_p_p (isOpen_of_isRegularOpen x.property)).symm

private lemma val_inter_perp_empty' (x : RegularOpens α) : x.val ∩ x.valᵖ = ∅ := by
  ext y; simp only [Flypitch.perp, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hy; exact fun h => h (subset_closure hy)

private lemma union_perp_pp_eq_univ' (x : RegularOpens α) :
    (x.val ∪ x.valᵖ)ᵖᵖ = Set.univ := by
  rw [p_p_eq_int_cl]
  suffices h : closure (x.val ∪ x.valᵖ) = Set.univ by rw [h]; exact interior_univ
  rw [Set.eq_univ_iff_forall]; intro y
  by_cases hy : y ∈ closure x.val
  · rw [mem_closure_iff]; intro V hV hyV
    by_cases hVne : (V ∩ x.valᵖ).Nonempty
    · rcases hVne with ⟨z, hzV, hzp⟩
      exact ⟨z, hzV, Set.mem_union_right _ hzp⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hVne
      have hVcl : V ⊆ closure x.val := by
        intro z hz
        by_contra hzncl
        have hmem : z ∈ V ∩ x.valᵖ := ⟨hz, by simp [Flypitch.perp, hzncl]⟩
        rw [hVne] at hmem; simp at hmem
      have hVx : V ⊆ x.val := by
        have h1 : V ⊆ interior (closure x.val) := hV.subset_interior_iff.mpr hVcl
        rwa [← x.property] at h1
      exact ⟨y, hyV, Set.mem_union_left _ (hVx hyV)⟩
  · exact subset_closure (Set.mem_union_right _ (by simp [Flypitch.perp, hy]))

/-! ### Order on RegularOpens (needed before instance) -/

instance instLE : LE (RegularOpens α) := ⟨fun a b => a.val ⊆ b.val⟩

/-! ### Auxiliary lemmas for the CBA instance -/

private lemma le_sup_left' (a b : RegularOpens α) : a.val ⊆ (a.val ∪ b.val)ᵖᵖ :=
  Set.Subset.trans Set.subset_union_left
    (subset_p_p_of_open ((isOpen_of_isRegularOpen a.property).union
      (isOpen_of_isRegularOpen b.property)))

private lemma le_sup_right' (a b : RegularOpens α) : b.val ⊆ (a.val ∪ b.val)ᵖᵖ :=
  Set.Subset.trans Set.subset_union_right
    (subset_p_p_of_open ((isOpen_of_isRegularOpen a.property).union
      (isOpen_of_isRegularOpen b.property)))

private lemma sup_le' (a b c : RegularOpens α) (h1 : a.val ⊆ c.val) (h2 : b.val ⊆ c.val) :
    (a.val ∪ b.val)ᵖᵖ ⊆ c.val := by
  apply isRegularOpen_stable_subset c.property
  intro x hx
  rcases hx with hxa | hxb
  · exact h1 hxa
  · exact h2 hxb

private lemma le_sup_inf' (x y z : RegularOpens α) :
    (x.val ∪ y.val)ᵖᵖ ∩ (x.val ∪ z.val)ᵖᵖ ⊆ (x.val ∪ y.val ∩ z.val)ᵖᵖ := by
  have hxy : IsOpen (x.val ∪ y.val) :=
    (isOpen_of_isRegularOpen x.property).union (isOpen_of_isRegularOpen y.property)
  have hxz : IsOpen (x.val ∪ z.val) :=
    (isOpen_of_isRegularOpen x.property).union (isOpen_of_isRegularOpen z.property)
  rw [← p_p_inter_eq_inter_p_p hxy hxz]
  apply p_p_mono
  intro a ⟨haux, hazx⟩
  rcases haux with hax | hay <;> rcases hazx with hax' | haz
  · exact Or.inl hax
  · exact Or.inl hax
  · exact Or.inl hax'
  · exact Or.inr ⟨hay, haz⟩

-- Auxiliary: sSup upper bound for a ∈ s
private lemma sSup_ub' (s : Set (RegularOpens α)) (a : RegularOpens α) (ha : a ∈ s) :
    a.val ⊆ (⋃₀ Set.image (·.val) s)ᵖᵖ :=
  (subset_p_p_of_open (isOpen_of_isRegularOpen a.property)).trans
    (p_p_mono (fun x hx => ⟨a.val, ⟨a, ha, rfl⟩, hx⟩))

-- Auxiliary: sSup is least upper bound
private lemma sSup_lub' (s : Set (RegularOpens α)) (a : RegularOpens α)
    (ha : ∀ b ∈ s, b.val ⊆ a.val) :
    (⋃₀ Set.image (·.val) s)ᵖᵖ ⊆ a.val := by
  apply isRegularOpen_stable_subset a.property
  intro x hx
  rcases hx with ⟨S, ⟨b, hb, rfl⟩, hxS⟩
  exact ha b hb hxS

-- Auxiliary: sInf lower bound for a ∈ s
private lemma sInf_lb' (s : Set (RegularOpens α)) (a : RegularOpens α) (ha : a ∈ s) :
    (⋂₀ Set.image (·.val) s)ᵖᵖ ⊆ a.val := by
  apply isRegularOpen_stable_subset a.property
  intro x hx
  rw [Set.mem_sInter] at hx
  exact hx a.val ⟨a, ha, rfl⟩

-- Auxiliary: a ≤ sInf s when a ≤ all b ∈ s
private lemma le_sInf' (s : Set (RegularOpens α)) (a : RegularOpens α)
    (ha : ∀ b ∈ s, a.val ⊆ b.val) :
    a.val ⊆ (⋂₀ Set.image (·.val) s)ᵖᵖ := by
  have hSub : a.val ⊆ ⋂₀ Set.image (·.val) s := by
    intro x hx
    rw [Set.mem_sInter]
    intro S hS
    rcases hS with ⟨b, hb, rfl⟩
    exact ha b hb hx
  rw [← isRegularOpen_eq_p_p a.property]
  exact p_p_mono hSub

/-! ### Complete Boolean Algebra instance

Build everything in one `where` block to avoid coherence issues.
-/

set_option maxHeartbeats 800000 in
/-- Regular opens form a complete Boolean algebra.
Port of: `regular_open_algebra` (src/regular_open_algebra.lean:507-647). -/
noncomputable instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra (RegularOpens α) where
  -- Binary operations
  sup a b := ⟨(a.val ∪ b.val)ᵖᵖ, isRegularOpen_p_p⟩
  inf a b := ⟨a.val ∩ b.val, isRegularOpen_inter a.property b.property⟩
  compl a := ⟨Flypitch.perp a.val, compl_isRO' a⟩
  top := ⟨Set.univ, isRegularOpen_univ⟩
  bot := ⟨∅, isRegularOpen_empty⟩
  -- Order
  le a b := a.val ⊆ b.val
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := Set.Subset.trans h1 h2
  le_antisymm _ _ h1 h2 := Subtype.ext (Set.Subset.antisymm h1 h2)
  -- Sup lattice axioms
  le_sup_left a b := le_sup_left' a b
  le_sup_right a b := le_sup_right' a b
  sup_le a b c h1 h2 := sup_le' a b c h1 h2
  -- Inf lattice axioms
  inf_le_left a b := Set.inter_subset_left
  inf_le_right a b := Set.inter_subset_right
  le_inf a b c h1 h2 := Set.subset_inter h1 h2
  -- Distributivity
  le_sup_inf x y z := le_sup_inf' x y z
  -- Boolean algebra axioms
  inf_compl_le_bot a := by
    -- a ⊓ aᶜ ≤ ⊥ means a.val ∩ (Flypitch.perp a.val) ⊆ ∅
    show a.val ∩ Flypitch.perp a.val ⊆ ∅
    exact val_inter_perp_empty' a ▸ le_refl _
  top_le_sup_compl a := by
    -- ⊤ ≤ a ⊔ aᶜ means Set.univ ⊆ (a.val ∪ (Flypitch.perp a.val))ᵖᵖ
    show Set.univ ⊆ (a.val ∪ Flypitch.perp a.val)ᵖᵖ
    exact union_perp_pp_eq_univ' a ▸ le_refl _
  le_top _ := Set.subset_univ _
  bot_le _ := Set.empty_subset _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl
  -- Complete lattice operations
  sSup 𝒮 := ⟨(⋃₀ Set.image (·.val) 𝒮)ᵖᵖ, isRegularOpen_p_p⟩
  sInf 𝒮 := ⟨(⋂₀ Set.image (·.val) 𝒮)ᵖᵖ, isRegularOpen_p_p⟩
  isLUB_sSup s := by
    refine ⟨fun a ha => sSup_ub' s a ha, fun a ha => ?_⟩
    exact sSup_lub' s a (fun b hb => ha hb)
  isGLB_sInf s := by
    refine ⟨fun a ha => sInf_lb' s a ha, fun a ha => ?_⟩
    exact le_sInf' s a (fun b hb => ha hb)

/-! ### Convenience simp lemmas (work once the instance is defined) -/

@[simp] lemma sup_val (x₁ x₂ : RegularOpens α) :
    (x₁ ⊔ x₂ : RegularOpens α).val = ((x₁ : Set α) ∪ x₂)ᵖᵖ := rfl

@[simp] lemma inf_val (x₁ x₂ : RegularOpens α) :
    (x₁ ⊓ x₂ : RegularOpens α).val = (x₁ : Set α) ∩ x₂ := rfl

@[simp] lemma top_val : (⊤ : RegularOpens α).val = Set.univ := rfl
@[simp] lemma bot_val : (⊥ : RegularOpens α).val = ∅ := rfl
@[simp] lemma coe_bot : ((⊥ : RegularOpens α) : Set α) = ∅ := rfl

@[simp] lemma compl_val (x : RegularOpens α) : (xᶜ : RegularOpens α).val = x.valᵖ := rfl

@[simp] lemma sSup_val (𝒜 : Set (RegularOpens α)) :
    (sSup 𝒜 : RegularOpens α).val = (⋃₀ Set.image (·.val) 𝒜)ᵖᵖ := rfl

@[simp] lemma sInf_val (s : Set (RegularOpens α)) :
    (sInf s : RegularOpens α).val = (⋂₀ Set.image (·.val) s)ᵖᵖ := rfl

lemma le_iff_subset {S₁ S₂ : RegularOpens α} : S₁ ≤ S₂ ↔ (S₁ : Set α) ⊆ S₂ := Iff.rfl

/-! ### NontrivialCompleteBooleanAlgebra -/

/-- Regular opens form a nontrivial CBA when α is nonempty.
Port of: `def regular_open_algebra` (src/regular_open_algebra.lean:635). -/
noncomputable instance instNontrivialCBA [Nonempty α] :
    NontrivialCompleteBooleanAlgebra (RegularOpens α) where
  bot_lt_top := by
    refine lt_of_le_of_ne bot_le (fun h => ?_)
    have : (⊥ : RegularOpens α).val = (⊤ : RegularOpens α).val := congr_arg (·.val) h
    rw [bot_val, top_val] at this
    exact absurd (this ▸ Set.mem_univ (‹Nonempty α›.some)) (by simp)

/-! ### Density lemmas -/

open Flypitch.Regular in
/-- If S is dense, Sᵖᵖ = univ. Port of src:649. -/
lemma p_p_eq_univ_of_dense {S : Set α} (H_dense : Dense' S) : Sᵖᵖ = Set.univ := by
  simp only [perp_unfold, closure_univ_of_dense H_dense,
    Set.compl_univ, closure_empty, Set.compl_empty]

open Flypitch.Regular in
/-- If S is rel-dense in open S₀, then S₀ ∩ Sᵖᵖ = S₀. Port of src:653. -/
lemma p_p_eq_univ_of_rel_dense_of_open {S₀ S : Set α} (H_open : IsOpen S₀)
    (H_rel_dense : RelDense S₀ S) : S₀ ∩ Sᵖᵖ = S₀ := by
  rw [p_p_eq_int_cl]
  have hcl : closure S ∩ S₀ = S₀ := closure_rel_dense_of_open H_open H_rel_dense
  -- hcl: closure S ∩ S₀ = S₀, so S₀ ⊆ closure S
  have hS₀_sub_cl : S₀ ⊆ closure S := by
    intro x hx
    have : x ∈ closure S ∩ S₀ := by rw [hcl]; exact hx
    exact this.1
  exact Set.inter_eq_left.mpr (H_open.subset_interior_iff.mpr hS₀_sub_cl)

/-- If the union of rO is dense, then ⨆ rO = ⊤. Port of src:659. -/
lemma sSup_eq_top_of_dense_Union {ι : Type u} {rO : ι → RegularOpens α}
    (H_dense : Dense' (⋃₀ (Set.image (·.val) (Set.range rO)))) :
    (⨆ i, rO i : RegularOpens α) = ⊤ := by
  apply ext; rw [top_val]
  show (sSup (Set.range rO)).val = Set.univ
  rw [sSup_val, p_p_eq_univ_of_dense H_dense]

/-- If the union is rel-dense in S, then (⨆ rO) ⊓ S = S. Port of src:664. -/
lemma sSup_eq_top_of_dense_Union_rel {ι : Type u} {rO : ι → RegularOpens α}
    (S : RegularOpens α)
    (H_dense : RelDense S.val (⋃₀ (Set.image (·.val) (Set.range rO)))) :
    (⨆ i, rO i : RegularOpens α) ⊓ S = S := by
  apply ext; rw [inf_val]
  show ((sSup (Set.range rO)).val ∩ S.val) = S.val
  rw [sSup_val, Set.inter_comm]
  exact p_p_eq_univ_of_rel_dense_of_open (isOpen_of_isRegularOpen S.property) H_dense

/-! ### CCC for regular opens -/

/-- If α satisfies the CCC, so do its regular opens. Port of src:674. -/
lemma CCC_regular_opens (h : countable_chain_condition α) : CCC (RegularOpens α) := by
  intro ι O hO h2O
  -- Step 1: O is injective on ι
  have O_inj : Function.Injective O := by
    intro x y hxy
    by_contra hne
    have hle := h2O x y hne
    rw [hxy, inf_idem] at hle
    exact (Std.not_le_of_gt (hO y)) hle
  -- Step 2: The composition Subtype.val ∘ O is also injective
  have hValInj : Function.Injective (Subtype.val ∘ O) :=
    Subtype.val_injective.comp O_inj
  -- Step 3: The range consists of open sets
  have hopen : ∀ ⦃o : Set α⦄, o ∈ Set.range (Subtype.val ∘ O) → IsOpen o := by
    rintro _ ⟨x, rfl⟩
    exact isOpen_of_isRegularOpen (O x).property
  -- Step 4: The range is pairwise disjoint
  have hpwd : (Set.range (Subtype.val ∘ O)).PairwiseDisjoint id := by
    intro a ha b hb hab
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    have hne : x ≠ y := fun heq => hab (congr_arg (Subtype.val ∘ O) heq)
    have hle := h2O x y hne
    simp only [Function.onFun, id, Set.disjoint_left]
    intro z hz1 hz2
    have : z ∈ (O x ⊓ O y).val := by rw [inf_val]; exact ⟨hz1, hz2⟩
    have hbot : (O x ⊓ O y).val ⊆ (⊥ : RegularOpens α).val := hle
    exact absurd (hbot this) (by simp [bot_val])
  -- Step 5: Apply CCC for α and convert cardinal bound
  have hcnt := h _ hopen hpwd
  calc Cardinal.mk ι = Cardinal.mk (Set.range (Subtype.val ∘ O)) := (Cardinal.mk_range_eq _ hValInj).symm
    _ ≤ Cardinal.aleph0 := hcnt.le_aleph0

/-! ### bot_lt and fst lemmas -/

/-- ⊥ < o iff o is nonempty. Port of src:691. -/
lemma bot_lt_iff [Nonempty α] {o : RegularOpens α} : ⊥ < o ↔ ∃ x, x ∈ (o : Set α) := by
  constructor
  · intro h
    have hne : (o : Set α) ≠ ∅ := by
      intro heq
      have : (⊥ : RegularOpens α) = o := by apply ext; rw [bot_val, heq]
      exact absurd this (ne_of_lt h)
    exact Set.nonempty_iff_ne_empty.mpr hne
  · rintro ⟨x, hx⟩
    exact lt_of_le_of_ne bot_le (fun h => by simp [← h, bot_val] at hx)

/-- ↑(sSup f) = (⋃₀ (val '' f))ᵖᵖ. Port of src:696. -/
@[simp] lemma fst_sSup {f : Set (RegularOpens α)} :
    (sSup f : RegularOpens α).val = (⋃₀ Set.image (·.val) f)ᵖᵖ := rfl

/-- ↑(⨆ i, f i) = (⋃ i, (f i).val)ᵖᵖ. Port of src:699. -/
lemma fst_iSup {ι : Type*} {f : ι → RegularOpens α} :
    (⨆ i, f i : RegularOpens α).val = (⋃ i, (f i).val)ᵖᵖ := by
  show (sSup (Set.range f)).val = _
  rw [fst_sSup]
  congr 1
  ext x
  simp [Set.mem_iUnion, Set.mem_sUnion, Set.mem_image, Set.mem_range]

/-- ↑(sInf f) = (⋂₀ (val '' f))ᵖᵖ. Port of src:702. -/
@[simp] lemma fst_sInf {f : Set (RegularOpens α)} :
    (sInf f : RegularOpens α).val = (⋂₀ Set.image (·.val) f)ᵖᵖ := rfl

/-- ↑(⨅ i, f i) = (⋂ i, (f i).val)ᵖᵖ. Port of src:713. -/
lemma fst_iInf {ι : Type*} {f : ι → RegularOpens α} :
    (⨅ i, f i : RegularOpens α).val = (⋂ i, (f i).val)ᵖᵖ := by
  show (sInf (Set.range f)).val = _
  rw [fst_sInf]
  congr 1
  ext x
  simp [Set.mem_iInter, Set.mem_sInter, Set.mem_image, Set.mem_range]

end RegularOpens

end Flypitch

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/bvm_extras2.lean

import ErdosProblems.Erdos501.Flypitch4.BvmExtras

set_option relaxedAutoImplicit true

open scoped Flypitch
open Lattice

universe u

namespace bSet

-- ============================================================
-- src/bvm_extras2.lean:17-35: section lemmas
-- ============================================================

section lemmas
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:20
lemma prod_subset {x₁ x₂ y₁ y₂ : bSet 𝔹} (H_sub₁ : Γ ≤ x₁ ⊆ᴮ x₂) (H_sub₂ : Γ ≤ y₁ ⊆ᴮ y₂) :
    Γ ≤ prod x₁ y₁ ⊆ᴮ prod x₂ y₂ := by
  rw [subset_unfold']
  apply le_iInf; intro pr; rw [← deduction]
  -- Goal: Γ ⊓ pr ∈ prod x₁ y₁ ≤ pr ∈ prod x₂ y₂
  set ctx := Γ ⊓ pr ∈ᴮ prod x₁ y₁
  have hmem : ctx ≤ pr ∈ᴮ prod x₁ y₁ := inf_le_right
  obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hmem
  apply mem_prod_iff₂.mpr
  exact ⟨v, mem_of_mem_subset (inf_le_left.trans H_sub₁) Hv,
         w, mem_of_mem_subset (inf_le_left.trans H_sub₂) Hw, H_eq⟩

-- src/bvm_extras2.lean:29
lemma prod_subset_left {x₁ x₂ y : bSet 𝔹} (H_sub : Γ ≤ x₁ ⊆ᴮ x₂) :
    Γ ≤ prod x₁ y ⊆ᴮ prod x₂ y :=
  prod_subset H_sub subset_self

-- src/bvm_extras2.lean:32
lemma prod_subset_right {x y₁ y₂ : bSet 𝔹} (H_sub : Γ ≤ y₁ ⊆ᴮ y₂) :
    Γ ≤ prod x y₁ ⊆ᴮ prod x y₂ :=
  prod_subset subset_self H_sub

end lemmas

-- ============================================================
-- src/bvm_extras2.lean:37-62: section inj_inverse_surj
-- ============================================================

section inj_inverse_surj
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {x y f : bSet 𝔹} {Γ : 𝔹}
  (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

-- src/bvm_extras2.lean:41
lemma inj_inverse.is_total_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_total y x (inj_inverse H_func H_inj) := by
  have heq := bv_symm (image_eq_codomain_of_surj H_surj)
  -- is_total z x g = ⨅ w, w ∈ z ⟹ ⨆ w', w' ∈ x ⊓ pair w w' ∈ g
  -- B_ext (fun z => is_total z x g): z appears only in w ∈ z
  apply bv_rw' heq (ϕ := fun z => is_total z x (inj_inverse H_func H_inj))
  · exact B_ext_iInf (h := fun w => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))
  · exact inj_inverse_is_total H_func H_inj

-- src/bvm_extras2.lean:48
lemma inj_inverse.is_function_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_function y x (inj_inverse H_func H_inj) := by
  have heq := bv_symm (image_eq_codomain_of_surj H_surj)
  apply bv_rw' heq (ϕ := fun z => is_function z x (inj_inverse H_func H_inj))
  · exact B_ext_is_function_left
  · exact inj_inverse_is_function H_func H_inj

-- src/bvm_extras2.lean:55
lemma inj_inverse.is_surj_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj y x (inj_inverse H_func H_inj) := by
  -- is_surj y x g = ⨅ v, v ∈ x ⟹ ⨆ w, w ∈ y ⊓ pair w v ∈ g
  -- inj_inverse_is_surj gives: is_surj (image x y f) x (inj_inverse)
  -- image x y f =ᴮ y via image_eq_codomain_of_surj
  apply bv_rw' (bv_symm (image_eq_codomain_of_surj H_surj))
          (ϕ := fun z => is_surj z x (inj_inverse H_func H_inj))
  · -- B_ext (fun z => is_surj z x g): z appears in w ∈ z, i.e., w ∈ᴮ z inside ⨆ w
    -- is_surj z x g = ⨅ v, v ∈ x ⟹ ⨆ w, w ∈ z ⊓ pair w v ∈ g
    exact B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun w => B_ext_inf B_ext_mem_right B_ext_const)))
  · exact inj_inverse_is_surj H_func H_inj

end inj_inverse_surj

-- ============================================================
-- src/bvm_extras2.lean:64-345: section Ord
-- ============================================================

section Ord
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:67
lemma subset_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y :=
  subset_of_mem_transitive (H_Ord.trans inf_le_right) H_mem

-- src/bvm_extras2.lean:70
lemma mem_of_mem_Ord {x y z : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_mem' : Γ ≤ y ∈ᴮ z)
    (H_ord₂ : Γ ≤ Ord z) : Γ ≤ x ∈ᴮ z :=
  mem_of_mem_subset (subset_of_mem_Ord H_mem' H_ord₂) H_mem

-- src/bvm_extras2.lean:78
lemma transitive_union {u : bSet 𝔹} {Γ : 𝔹} (Hu : Γ ≤ ⨅ z, z ∈ᴮ u ⟹ is_transitive z) :
    Γ ≤ is_transitive (bv_union u) := by
  unfold is_transitive
  apply le_iInf; intro x; rw [← deduction]
  set ctx := Γ ⊓ x ∈ᴮ bv_union u
  have hmem : ctx ≤ x ∈ᴮ bv_union u := inf_le_right
  rw [mem_bv_union_iff] at hmem
  obtain ⟨y, Hy⟩ := exists_convert hmem (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hy_u : ctx ≤ y ∈ᴮ u := Hy.trans inf_le_left
  have Hx_y : ctx ≤ x ∈ᴮ y := Hy.trans inf_le_right
  have Hy_trans : ctx ≤ is_transitive y :=
    le_trans (le_inf (inf_le_left.trans (Hu.trans (iInf_le _ y))) Hy_u) bv_imp_elim
  have Hx_sub_y : ctx ≤ x ⊆ᴮ y :=
    le_trans (le_inf (Hy_trans.trans (iInf_le _ x)) Hx_y) bv_imp_elim
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  rw [mem_bv_union_iff]
  apply le_iSup_of_le y
  apply le_inf
  · exact inf_le_left.trans Hy_u
  · rw [subset_unfold'] at Hx_sub_y
    exact le_trans (le_inf (inf_le_left.trans (Hx_sub_y.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim

-- src/bvm_extras2.lean:88
lemma transitive_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ is_transitive (x ∩ᴮ y) := by
  unfold is_transitive
  apply le_iInf; intro z; rw [← deduction]
  set ctx := Γ ⊓ z ∈ᴮ x ∩ᴮ y
  have hmem : ctx ≤ z ∈ᴮ x ∩ᴮ y := inf_le_right
  have Hz_x : ctx ≤ z ∈ᴮ x := (mem_binary_inter_iff.mp hmem).1
  have Hz_y : ctx ≤ z ∈ᴮ y := (mem_binary_inter_iff.mp hmem).2
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  apply mem_binary_inter_iff.mpr
  constructor
  · have Hx_trans : ctx ≤ is_transitive x := inf_le_left.trans (H₁.trans inf_le_right)
    have hsub : ctx ≤ z ⊆ᴮ x :=
      le_trans (le_inf (Hx_trans.trans (iInf_le _ z)) Hz_x) bv_imp_elim
    rw [subset_unfold'] at hsub
    exact le_trans (le_inf (inf_le_left.trans (hsub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim
  · have Hy_trans : ctx ≤ is_transitive y := inf_le_left.trans (H₂.trans inf_le_right)
    have hsub : ctx ≤ z ⊆ᴮ y :=
      le_trans (le_inf (Hy_trans.trans (iInf_le _ z)) Hz_y) bv_imp_elim
    rw [subset_unfold'] at hsub
    exact le_trans (le_inf (inf_le_left.trans (hsub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim

-- src/bvm_extras2.lean:96
lemma epsilon_trichotomy_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_trichotomy (x ∩ᴮ y) := by
  unfold epsilon_trichotomy
  apply le_iInf; intro w; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  set ctx := Γ ⊓ w ∈ᴮ x ∩ᴮ y ⊓ z ∈ᴮ x ∩ᴮ y
  have hw_inter : ctx ≤ w ∈ᴮ x ∩ᴮ y := inf_le_left.trans inf_le_right
  have hz_inter : ctx ≤ z ∈ᴮ x ∩ᴮ y := inf_le_right
  have Hw_x : ctx ≤ w ∈ᴮ x := (mem_binary_inter_iff.mp hw_inter).1
  have Hz_x : ctx ≤ z ∈ᴮ x := (mem_binary_inter_iff.mp hz_inter).1
  exact epsilon_trichotomy_of_Ord Hw_x Hz_x (inf_le_left.trans (inf_le_left.trans H₁))

-- src/bvm_extras2.lean:104
lemma epsilon_well_founded_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_well_founded (x ∩ᴮ y) := by
  rw [epsilon_well_founded]
  apply le_iInf; intro w; rw [← deduction, ← deduction]
  -- ctx = Γ ⊓ w ⊆ᴮ (x ∩ᴮ y) ⊓ (w =ᴮ ∅)ᶜ
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ v, ...)
  -- Apply at w with w ⊆ x (via w ⊆ x ∩ y ⊆ x) and w ≠ ∅
  set ctx := Γ ⊓ w ⊆ᴮ x ∩ᴮ y ⊓ (w =ᴮ ∅)ᶜ
  have Hw_sub_x : ctx ≤ w ⊆ᴮ x :=
    subset_trans' (inf_le_left.trans inf_le_right) binary_inter_subset_left
  have Hw_ne : ctx ≤ (w =ᴮ ∅)ᶜ := inf_le_right
  -- epsilon_well_founded x at w
  have Hewf : ctx ≤ epsilon_well_founded x :=
    inf_le_left.trans (inf_le_left.trans
      (le_trans H₁ (inf_le_left.trans inf_le_right)))
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ y, ...)
  have Hewf_w : ctx ≤ w ⊆ᴮ x ⟹ ((w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ)) :=
    le_trans Hewf (iInf_le _ w)
  have h1 : ctx ≤ (w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ) :=
    le_trans (le_inf Hewf_w Hw_sub_x) bv_imp_elim
  exact le_trans (le_inf h1 Hw_ne) bv_imp_elim

-- src/bvm_extras2.lean:112
lemma Ord_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ Ord (binary_inter x y) := by
  unfold Ord epsilon_well_orders
  apply le_inf
  · apply le_inf
    · exact epsilon_trichotomy_binary_inter H₁
    · exact epsilon_well_founded_binary_inter H₁
  · exact transitive_binary_inter H₁ H₂

-- ============================================================
-- src/bvm_extras2.lean:122-158: section compl
-- ============================================================

section compl

def compl (x y : bSet 𝔹) : bSet 𝔹 := comprehend (fun z => (z ∈ᴮ y)ᶜ) x

-- src/bvm_extras2.lean:126
lemma compl_subset {x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ compl x y ⊆ᴮ x :=
  subset.mk_subset

-- src/bvm_extras2.lean:129
lemma mem_compl_iff {x y : bSet 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ compl x y ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ (z ∈ᴮ y)ᶜ) := by
  unfold compl
  have H_congr : ∀ a b : bSet 𝔹, a =ᴮ b ⊓ (a ∈ᴮ y)ᶜ ≤ (b ∈ᴮ y)ᶜ := by
    intro a b
    simp only [← imp_bot]; rw [← deduction]
    have h_ba : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ b =ᴮ a := by
      rw [bv_eq_symm]; exact inf_le_left.trans inf_le_left
    have h_by : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ b ∈ᴮ y := inf_le_right
    have h_ay : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ a ∈ᴮ y :=
      bv_rw'' h_ba h_by B_ext_mem_left
    have h_nay : a =ᴮ b ⊓ (a ∈ᴮ y ⟹ ⊥) ⊓ b ∈ᴮ y ≤ a ∈ᴮ y ⟹ ⊥ :=
      inf_le_left.trans inf_le_right
    exact le_trans (le_inf h_nay h_ay) bv_imp_elim
  rw [mem_comprehend_iff₂ _ _ H_congr]
  constructor
  · intro H
    obtain ⟨w, Hw⟩ := exists_convert H (B_ext_inf B_ext_mem_left
      (B_ext_inf B_ext_bv_eq_right (B_ext_neg (h := B_ext_mem_left))))
    have Hw_mem : Γ ≤ w ∈ᴮ x := Hw.trans inf_le_left
    have Hw_eq : Γ ≤ z =ᴮ w := Hw.trans (inf_le_right.trans inf_le_left)
    have Hw_nmem : Γ ≤ (w ∈ᴮ y)ᶜ := Hw.trans (inf_le_right.trans inf_le_right)
    constructor
    · exact bv_rw'' (bv_symm Hw_eq) Hw_mem B_ext_mem_left
    · simp only [← imp_bot] at Hw_nmem ⊢; rw [← deduction] at Hw_nmem ⊢
      have : Γ ⊓ z ∈ᴮ y ≤ w ∈ᴮ y :=
        bv_rw'' (inf_le_left.trans Hw_eq) inf_le_right B_ext_mem_left
      exact le_trans (le_inf inf_le_left this) Hw_nmem
  · intro ⟨H_mem, H_nmem⟩
    apply le_iSup_of_le z
    exact le_inf H_mem (le_inf bv_refl H_nmem)

end compl

-- src/bvm_extras2.lean:141
lemma compl_empty_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H_sub : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ compl x y =ᴮ ∅ := by
  apply mem_ext
  · apply le_iInf; intro w; rw [← deduction]
    have hmem : Γ ⊓ w ∈ᴮ compl x y ≤ w ∈ᴮ compl x y := inf_le_right
    have ⟨Hw_x, Hw_ny⟩ := mem_compl_iff.mp hmem
    have Hw_y : Γ ⊓ w ∈ᴮ compl x y ≤ w ∈ᴮ y :=
      mem_of_mem_subset (inf_le_left.trans H_sub) Hw_x
    exact bv_exfalso (bv_absurd (w ∈ᴮ y) Hw_y Hw_ny)
  · apply le_iInf; intro w; rw [← deduction]
    exact bv_exfalso (bot_of_mem_empty inf_le_right)

-- src/bvm_extras2.lean:149
lemma nonempty_compl_of_ne {x y : bSet 𝔹} {Γ : 𝔹} (H_ne : Γ ≤ (x =ᴮ y)ᶜ) :
    Γ ≤ ((compl x y =ᴮ ∅)ᶜ) ⊔ ((compl y x =ᴮ ∅)ᶜ) := by
  -- x ≠ y means (x ⊆ y ⊓ y ⊆ x)ᶜ = (x ⊆ y)ᶜ ⊔ (y ⊆ x)ᶜ
  rw [eq_iff_subset_subset, compl_inf] at H_ne
  -- Helper: compl a b = ∅ and z ∈ a and z ∉ b → ⊥ (contradiction)
  -- Actually: show each disjunct using bv_or_elim_left
  -- For (x ⊆ y)ᶜ case: derive (compl x y = ∅)ᶜ
  -- For (y ⊆ x)ᶜ case: derive (compl y x = ∅)ᶜ
  -- Use: if (compl x y = ∅) then x ⊆ y [the contrapositive of compl_empty_of_subset]
  -- Prove: compl_full_empty : Γ ≤ compl x y =ᴮ ∅ → Γ ≤ x ⊆ y
  -- Proof: for z ∈ x, if z ∉ y then z ∈ compl x y = ∅, contradiction
  -- So the two branches are:
  -- Branch 1: (x ⊆ y)ᶜ ⊓ Γ: if compl x y = ∅ → x ⊆ y, but (x ⊆ y)ᶜ = contradiction
  -- Branch 2: symmetric
  have compl_empty_imp_sub : ∀ (a b : bSet 𝔹) (Γ' : 𝔹),
      Γ' ≤ compl a b =ᴮ ∅ → Γ' ≤ a ⊆ᴮ b := by
    intro a b Γ' H
    rw [subset_unfold']
    apply le_iInf; intro z; rw [← deduction]
    -- z ∈ a → z ∈ b; prove: ctx' ⊓ (z ∈ b)ᶜ = ⊥
    set ctx' := Γ' ⊓ z ∈ᴮ a
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    have h1 : ctx' ⊓ (z ∈ᴮ b)ᶜ ≤ z ∈ᴮ compl a b :=
      mem_compl_iff.mpr ⟨inf_le_left.trans inf_le_right, inf_le_right⟩
    have h2 : ctx' ⊓ (z ∈ᴮ b)ᶜ ≤ compl a b =ᴮ ∅ := inf_le_left.trans (inf_le_left.trans H)
    exact bv_exfalso (bot_of_mem_empty (bv_rw'' h2 h1 B_ext_mem_right))
  -- Now case split on H_ne : (x ⊆ y)ᶜ ⊔ (y ⊆ x)ᶜ
  have h_left : (x ⊆ᴮ y)ᶜ ⊓ Γ ≤ (compl x y =ᴮ ∅)ᶜ ⊔ (compl y x =ᴮ ∅)ᶜ := by
    apply bv_or_left
    -- need: (x ⊆ y)ᶜ ⊓ Γ ≤ (compl x y = ∅)ᶜ
    conv_rhs => rw [← imp_bot]
    rw [← deduction]
    -- goal: (x ⊆ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ ⊥
    have hce : (x ⊆ᴮ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ compl x y =ᴮ ∅ := inf_le_right
    have hsub := compl_empty_imp_sub x y _ hce
    have hn : (x ⊆ᴮ y)ᶜ ⊓ Γ ⊓ compl x y =ᴮ ∅ ≤ (x ⊆ᴮ y)ᶜ := inf_le_left.trans inf_le_left
    exact bv_absurd (x ⊆ᴮ y) hsub hn
  have h_right : (y ⊆ᴮ x)ᶜ ⊓ Γ ≤ (compl x y =ᴮ ∅)ᶜ ⊔ (compl y x =ᴮ ∅)ᶜ := by
    apply bv_or_right
    conv_rhs => rw [← imp_bot]
    rw [← deduction]
    have hce : (y ⊆ᴮ x)ᶜ ⊓ Γ ⊓ compl y x =ᴮ ∅ ≤ compl y x =ᴮ ∅ := inf_le_right
    have hsub := compl_empty_imp_sub y x _ hce
    have hn : (y ⊆ᴮ x)ᶜ ⊓ Γ ⊓ compl y x =ᴮ ∅ ≤ (y ⊆ᴮ x)ᶜ := inf_le_left.trans inf_le_left
    exact bv_absurd (y ⊆ᴮ x) hsub hn
  exact le_trans (le_inf H_ne le_rfl) (bv_or_elim_left h_left h_right)
-- src/bvm_extras2.lean:173
lemma Ord.lt_of_ne_and_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H_ne : Γ ≤ (x =ᴮ y)ᶜ) (H_le : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ∈ᴮ y := by
  -- Step 1: compl y x ≠ ∅ (since x ≠ y, one of compl x y or compl y x is nonempty;
  --   compl x y = ∅ since x ⊆ y; so compl y x ≠ ∅)
  have H_cxy := compl_empty_of_subset H_le
  have H_compl_ne : Γ ≤ (compl y x =ᴮ ∅)ᶜ := by
    have H_both := nonempty_compl_of_ne H_ne
    have h1 : (compl x y =ᴮ ∅)ᶜ ⊓ Γ ≤ (compl y x =ᴮ ∅)ᶜ :=
      bv_exfalso (bv_absurd _ (inf_le_right.trans H_cxy) inf_le_left)
    have h2 : (compl y x =ᴮ ∅)ᶜ ⊓ Γ ≤ (compl y x =ᴮ ∅)ᶜ := inf_le_left
    exact le_trans (le_inf H_both le_rfl) (bv_or_elim_left h1 h2)
  -- Step 2: get minimal element u of compl y x by regularity
  have H_reg := bSet_axiom_of_regularity (compl y x) H_compl_ne
  -- B_ext for ϕ u = u ∈ compl y x ⊓ ⨅ z', z' ∈ compl y x ⟹ (z' ∈ u)ᶜ
  have H_Bext : B_ext (fun u : bSet 𝔹 =>
      u ∈ᴮ compl y x ⊓ (⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ)) := by
    apply B_ext_inf B_ext_mem_left
    apply B_ext_iInf; intro z'
    simp only [← imp_bot]
    exact B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))
  obtain ⟨u, Hu⟩ := exists_convert H_reg H_Bext
  -- Hu : Γ ≤ u ∈ compl y x ⊓ ⨅ z', z' ∈ compl y x ⟹ (z' ∈ u)ᶜ
  have Hu_mem : Γ ≤ u ∈ᴮ compl y x := Hu.trans inf_le_left
  have Hu_min : Γ ≤ ⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ := Hu.trans inf_le_right
  -- From u ∈ compl y x: u ∈ y and u ∉ x
  have ⟨Hu_y, Hu_nx⟩ := mem_compl_iff.mp Hu_mem
  -- Step 3: show x = u (hence x ∈ y via bv_rw)
  -- Prove x ⊆ u
  have Hx_sub_u : Γ ≤ x ⊆ᴮ u := by
    rw [subset_unfold']
    apply le_iInf; intro a; rw [← deduction]
    set ctx := Γ ⊓ a ∈ᴮ x
    have Ha_x : ctx ≤ a ∈ᴮ x := inf_le_right
    have Ha_y : ctx ≤ a ∈ᴮ y := mem_of_mem_subset (inf_le_left.trans H_le) Ha_x
    -- trichotomy on a,u ∈ y under Ord y
    have H_tri := epsilon_trichotomy_of_Ord Ha_y (inf_le_left.trans Hu_y)
                    (inf_le_left.trans H₂)
    -- H_tri : ctx ≤ a = u ⊔ a ∈ u ⊔ u ∈ a
    -- Case a = u: u ∈ x, contradiction with Hu_nx
    have hcase1 : (a =ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := by
      have heq : (a =ᴮ u) ⊓ ctx ≤ a =ᴮ u := inf_le_left
      have ha_x : (a =ᴮ u) ⊓ ctx ≤ a ∈ᴮ x := inf_le_right.trans Ha_x
      -- a = u and a ∈ x → u ∈ x, contradicts Hu_nx
      have hu_x : (a =ᴮ u) ⊓ ctx ≤ u ∈ᴮ x :=
        bv_rw'' heq ha_x B_ext_mem_left
      exact bv_exfalso (bv_absurd (u ∈ᴮ x) hu_x (inf_le_right.trans (inf_le_left.trans Hu_nx)))
    -- Case a ∈ u: done
    have hcase2 : (a ∈ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := inf_le_left
    -- Case u ∈ a: u ∈ a ∈ x → u ∈ x (by Ord x transitivity), contradiction
    have hcase3 : (u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ u := by
      have Hua : (u ∈ᴮ a) ⊓ ctx ≤ u ∈ᴮ a := inf_le_left
      have ha_x2 : (u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ x := inf_le_right.trans Ha_x
      -- u ∈ a ∈ x → u ∈ x by Ord x transitivity
      have hu_x : (u ∈ᴮ a) ⊓ ctx ≤ u ∈ᴮ x :=
        mem_of_mem_Ord Hua ha_x2 (inf_le_right.trans (inf_le_left.trans H₁))
      exact bv_exfalso (bv_absurd (u ∈ᴮ x) hu_x (inf_le_right.trans (inf_le_left.trans Hu_nx)))
    -- Combine trichotomy: (a=u ⊔ a∈u ⊔ u∈a) ⊓ ctx ≤ a∈u
    have h12 : (a =ᴮ u ⊔ a ∈ᴮ u) ⊓ ctx ≤ a ∈ᴮ u := bv_or_elim_left hcase1 hcase2
    have hfinal := bv_or_elim_left h12 hcase3
    -- hfinal : ((a =ᴮ u ⊔ a ∈ᴮ u) ⊔ u ∈ᴮ a) ⊓ ctx ≤ a ∈ᴮ u
    exact le_trans (le_inf H_tri le_rfl) hfinal
  -- Prove u ⊆ x
  have Hu_sub_x : Γ ≤ u ⊆ᴮ x := by
    rw [subset_unfold']
    apply le_iInf; intro a; rw [← deduction]
    set ctx := Γ ⊓ a ∈ᴮ u
    have Ha_u : ctx ≤ a ∈ᴮ u := inf_le_right
    -- By contradiction: assume a ∉ x
    -- Convert ctx ≤ a ∈ x to: ctx ⊓ (a ∈ x)ᶜ ≤ ⊥
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    -- goal: ctx ⊓ (a ∈ x)ᶜ ≤ ⊥
    -- From a ∈ u ∈ y → a ∈ y; and a ∉ x → a ∈ compl y x
    -- Minimality of u: z' ∈ compl y x → z' ∉ u; contradiction with a ∈ u
    have Ha_y : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ y := by
      have hu_y : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ u ∈ᴮ y := inf_le_left.trans (inf_le_left.trans Hu_y)
      have ha_u : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ u := inf_le_left.trans Ha_u
      exact mem_of_mem_Ord ha_u hu_y (inf_le_left.trans (inf_le_left.trans H₂))
    have Ha_compl : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ compl y x :=
      mem_compl_iff.mpr ⟨Ha_y, inf_le_right⟩
    -- Minimality gives a ∉ u
    have Ha_nu : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ (a ∈ᴮ u)ᶜ := by
      -- ctx ⊓ (a ∈ x)ᶜ ≤ ctx ≤ Γ ≤ Hu_min
      have h1 : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ ctx := inf_le_left
      have h2 : ctx ≤ ⨅ z', z' ∈ᴮ compl y x ⟹ (z' ∈ᴮ u)ᶜ :=
        inf_le_left.trans Hu_min
      have h3 : ctx ⊓ (a ∈ᴮ x)ᶜ ≤ a ∈ᴮ compl y x ⟹ (a ∈ᴮ u)ᶜ :=
        (h1.trans h2).trans (iInf_le _ a)
      exact le_trans (le_inf h3 Ha_compl) bv_imp_elim
    exact bv_absurd (a ∈ᴮ u) (inf_le_left.trans Ha_u) Ha_nu
  -- Step 4: x = u, so x ∈ y (since u ∈ y)
  have H_eq : Γ ≤ x =ᴮ u := by
    rw [eq_iff_subset_subset]
    exact le_inf Hx_sub_u Hu_sub_x
  exact bv_rw'' (bv_symm H_eq) Hu_y B_ext_mem_left

-- src/bvm_extras2.lean:201
lemma Ord.le_or_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
  -- Let w = x ∩ y. If w ≠ x and w ≠ y, then w ∈ x and w ∈ y → w ∈ w (foundation).
  -- So w = x or w = y, giving x ⊆ y or y ⊆ x.
  set w := x ∩ᴮ y
  have w_Ord : Γ ≤ Ord w := Ord_binary_inter H₁ H₂
  -- Show: w = x ⊔ w = y
  have hdiag : Γ ≤ w =ᴮ x ⊔ w =ᴮ y := by
    -- by contradiction: ¬(w = x ⊔ w = y) leads to w ∈ w
    rw [← disjoint_compl_right_iff, disjoint_iff]
    apply le_antisymm _ bot_le
    -- goal: Γ ⊓ (w =ᴮ x ⊔ w =ᴮ y)ᶜ ≤ ⊥
    set ctx := Γ ⊓ (w =ᴮ x ⊔ w =ᴮ y)ᶜ
    -- ¬(w=x): w=x ≤ w=x ⊔ w=y, so (w=x ⊔ w=y)ᶜ ≤ (w=x)ᶜ
    have hne_x : ctx ≤ (w =ᴮ x)ᶜ := inf_le_right.trans (compl_le_compl le_sup_left)
    -- ¬(w=y): w=y ≤ w=x ⊔ w=y, so (w=x ⊔ w=y)ᶜ ≤ (w=y)ᶜ
    have hne_y : ctx ≤ (w =ᴮ y)ᶜ := inf_le_right.trans (compl_le_compl le_sup_right)
    -- From ¬(w = x) and w ⊆ x: w ∈ x
    have hw_x : ctx ≤ w ∈ᴮ x :=
      Ord.lt_of_ne_and_le (inf_le_left.trans w_Ord) (inf_le_left.trans H₁)
        hne_x (inf_le_left.trans binary_inter_subset_left)
    -- From ¬(w = y) and w ⊆ y: w ∈ y
    have hw_y : ctx ≤ w ∈ᴮ y :=
      Ord.lt_of_ne_and_le (inf_le_left.trans w_Ord) (inf_le_left.trans H₂)
        hne_y (inf_le_left.trans binary_inter_subset_right)
    -- w ∈ x ∩ y = w → w ∈ w, contradiction
    exact bot_of_mem_self' (mem_binary_inter_iff.mpr ⟨hw_x, hw_y⟩)
  -- Case split on hdiag
  have h1 : w =ᴮ x ⊓ Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
    apply bv_or_left
    -- w = x, so w ⊆ y gives x ⊆ y
    have hw_sub : w =ᴮ x ⊓ Γ ≤ w ⊆ᴮ y := inf_le_right.trans binary_inter_subset_right
    exact bv_rw'' (ϕ := fun v => v ⊆ᴮ y) inf_le_left hw_sub B_ext_subset_left
  have h2 : w =ᴮ y ⊓ Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
    apply bv_or_right
    -- w = y, so w ⊆ x gives y ⊆ x
    have hw_sub : w =ᴮ y ⊓ Γ ≤ w ⊆ᴮ x := inf_le_right.trans binary_inter_subset_left
    exact bv_rw'' (ϕ := fun v => v ⊆ᴮ x) inf_le_left hw_sub B_ext_subset_left
  exact le_trans (le_inf hdiag le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:220
lemma Ord.trichotomy {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
  have h_lor := Ord.le_or_le H₁ H₂
  -- helper: case split on (x=y)
  have hL : (x ⊆ᴮ y) ⊓ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
    set ctx := x ⊆ᴮ y ⊓ Γ
    have h_eq : (x =ᴮ y) ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_left inf_le_left)
    have h_ne : (x =ᴮ y)ᶜ ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_right
        (Ord.lt_of_ne_and_le (inf_le_right.trans (inf_le_right.trans H₁))
          (inf_le_right.trans (inf_le_right.trans H₂))
          inf_le_left (inf_le_right.trans inf_le_left)))
    calc ctx = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ ctx := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ ctx ⊔ (x =ᴮ y)ᶜ ⊓ ctx := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  have hR : (y ⊆ᴮ x) ⊓ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
    set ctx := y ⊆ᴮ x ⊓ Γ
    have h_eq : (x =ᴮ y) ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x :=
      le_sup_of_le_left (le_sup_of_le_left inf_le_left)
    have h_ne : (x =ᴮ y)ᶜ ⊓ ctx ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
      -- ¬(x=y) ↔ ¬(y=x) (bv_eq_symm), and y ⊆ x with ¬(y=x) gives y ∈ x
      apply le_sup_of_le_right
      have hne_yx : (x =ᴮ y)ᶜ ⊓ ctx ≤ (y =ᴮ x)ᶜ := by
        -- if y = x then x = y (bv_symm), contradicting (x=y)ᶜ
        conv_rhs => rw [← imp_bot]
        rw [← deduction]
        exact bv_absurd (x =ᴮ y) (bv_symm inf_le_right) (inf_le_left.trans inf_le_left)
      exact Ord.lt_of_ne_and_le (inf_le_right.trans (inf_le_right.trans H₂))
        (inf_le_right.trans (inf_le_right.trans H₁))
        hne_yx (inf_le_right.trans inf_le_left)
    calc ctx = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ ctx := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ ctx ⊔ (x =ᴮ y)ᶜ ⊓ ctx := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  exact le_trans (le_inf h_lor le_rfl) (bv_or_elim_left hL hR)

-- src/bvm_extras2.lean:232
lemma Ord.eq_iff_not_mem {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ↔ (Γ ≤ (x ∈ᴮ y)ᶜ ∧ Γ ≤ (y ∈ᴮ x)ᶜ) := by
  constructor
  · -- x = y → ¬(x ∈ y) ∧ ¬(y ∈ x)
    intro H
    constructor
    · -- x = y → ¬(x ∈ y): if x ∈ y and x = y then y ∈ y, contradiction
      conv_rhs => rw [← imp_bot]
      rw [← deduction]
      -- goal: Γ ⊓ x∈y ≤ ⊥; H: Γ ≤ x=y
      exact bot_of_mem_self' (bv_rw'' (ϕ := fun v => v ∈ᴮ y)
        (inf_le_left.trans H) inf_le_right B_ext_mem_left)
    · conv_rhs => rw [← imp_bot]
      rw [← deduction]
      -- goal: Γ ⊓ y∈x ≤ ⊥; H: Γ ≤ x=y, so bv_symm: ≤ y=x
      exact bot_of_mem_self' (bv_rw'' (ϕ := fun v => v ∈ᴮ x)
        (inf_le_left.trans (bv_symm H)) inf_le_right B_ext_mem_left)
  · -- ¬(x ∈ y) ∧ ¬(y ∈ x) → x = y: by trichotomy, x=y or x∈y or y∈x
    intro ⟨H₁', H₂'⟩
    have H_tri := Ord.trichotomy H₁ H₂
    -- H_tri: x=y ⊔ x∈y ⊔ y∈x
    -- from ¬(x∈y) and ¬(y∈x): must have x=y
    have h1 : (x =ᴮ y) ⊓ Γ ≤ x =ᴮ y := inf_le_left
    have h2 : (x ∈ᴮ y) ⊓ Γ ≤ x =ᴮ y :=
      bv_exfalso (bv_absurd (x ∈ᴮ y) inf_le_left (inf_le_right.trans H₁'))
    have h3 : (y ∈ᴮ x) ⊓ Γ ≤ x =ᴮ y :=
      bv_exfalso (bv_absurd (y ∈ᴮ x) inf_le_left (inf_le_right.trans H₂'))
    exact le_trans (le_inf H_tri le_rfl) (bv_or_elim_left (bv_or_elim_left h1 h2) h3)

-- src/bvm_extras2.lean:245
lemma Ord.eq_of_not_mem {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H_nmem₁ : Γ ≤ (x ∈ᴮ y)ᶜ) (H_nmem₂ : Γ ≤ (y ∈ᴮ x)ᶜ) : Γ ≤ x =ᴮ y := by
  rw [Ord.eq_iff_not_mem H₁ H₂]; exact ⟨H_nmem₁, H_nmem₂⟩

-- src/bvm_extras2.lean:160
lemma eq_iff_not_mem_of_Ord {x y z : bSet 𝔹} {Γ : 𝔹} (H_mem₁ : Γ ≤ x ∈ᴮ z) (H_mem₂ : Γ ≤ y ∈ᴮ z)
    (H_ord : Γ ≤ Ord z) : Γ ≤ x =ᴮ y ↔ (Γ ≤ (x ∈ᴮ y)ᶜ ∧ Γ ≤ (y ∈ᴮ x)ᶜ) :=
  Ord.eq_iff_not_mem (Ord_of_mem_Ord H_mem₁ H_ord) (Ord_of_mem_Ord H_mem₂ H_ord)

-- src/bvm_extras2.lean:248
lemma Ord.le_iff_lt_or_eq {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ↔ (Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y) := by
  constructor
  · -- x ⊆ y → x ∈ y ∨ x = y: case split on x = y
    intro H
    have h_eq : (x =ᴮ y) ⊓ Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y := le_sup_of_le_right inf_le_left
    have h_ne : (x =ᴮ y)ᶜ ⊓ Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y :=
      le_sup_of_le_left (Ord.lt_of_ne_and_le (inf_le_right.trans H₁) (inf_le_right.trans H₂)
        inf_le_left (inf_le_right.trans H))
    calc Γ = (x =ᴮ y ⊔ (x =ᴮ y)ᶜ) ⊓ Γ := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (x =ᴮ y) ⊓ Γ ⊔ (x =ᴮ y)ᶜ ⊓ Γ := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_eq h_ne
  · -- x ∈ y ∨ x = y → x ⊆ y
    intro H
    have h1 : (x ∈ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y := subset_of_mem_Ord inf_le_left (inf_le_right.trans H₂)
    have h2 : (x =ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y :=
      -- x = y → x ⊆ x → x ⊆ y (rewrite y to x in x ⊆ x)
      bv_rw'' (ϕ := fun v => x ⊆ᴮ v) inf_le_left (inf_le_right.trans subset_self)
        B_ext_subset_right
    exact le_trans (le_inf H le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:259
lemma Ord.lt_of_not_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ (x ⊆ᴮ y)ᶜ → Γ ≤ y ∈ᴮ x := by
  intro H_not_le
  -- From ¬(x ⊆ y), and trichotomy gives x=y ∨ x∈y ∨ y∈x,
  -- x=y → x⊆y (contradiction), x∈y → x⊆y (contradiction), so y∈x
  have H_tri := Ord.trichotomy H₁ H₂
  -- Case x=y: then x⊆y, contradiction
  have h1 : (x =ᴮ y) ⊓ Γ ≤ y ∈ᴮ x := by
    have hsub : (x =ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y :=
      bv_rw'' (ϕ := fun v => x ⊆ᴮ v) inf_le_left (inf_le_right.trans subset_self)
        B_ext_subset_right
    exact bv_exfalso (bv_absurd _ hsub (inf_le_right.trans H_not_le))
  -- Case x∈y: then x⊆y, contradiction
  have h2 : (x ∈ᴮ y) ⊓ Γ ≤ y ∈ᴮ x := by
    have hsub : (x ∈ᴮ y) ⊓ Γ ≤ x ⊆ᴮ y :=
      subset_of_mem_Ord inf_le_left (inf_le_right.trans H₂)
    exact bv_exfalso (bv_absurd _ hsub (inf_le_right.trans H_not_le))
  -- Case y∈x: done
  have h3 : (y ∈ᴮ x) ⊓ Γ ≤ y ∈ᴮ x := inf_le_left
  exact le_trans (le_inf H_tri le_rfl) (bv_or_elim_left (bv_or_elim_left h1 h2) h3)

-- src/bvm_extras2.lean:271
lemma Ord.resolve_lt {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ (x ∈ᴮ y)ᶜ → Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x := by
  intro H_not_mem
  -- By trichotomy: x=y ∨ x∈y ∨ y∈x
  -- x∈y is ruled out; x=y → y=x; y∈x is direct
  have H_tri := Ord.trichotomy H₁ H₂
  have h1 : (x =ᴮ y) ⊓ Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x :=
    le_sup_of_le_right (bv_symm inf_le_left)
  have h2 : (x ∈ᴮ y) ⊓ Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x :=
    bv_exfalso (bv_absurd (x ∈ᴮ y) inf_le_left (inf_le_right.trans H_not_mem))
  have h3 : (y ∈ᴮ x) ⊓ Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x := le_sup_of_le_left inf_le_left
  exact le_trans (le_inf H_tri le_rfl) (bv_or_elim_left (bv_or_elim_left h1 h2) h3)

-- src/bvm_extras2.lean:280
lemma epsilon_trichotomy_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹)
    (H_ord : Γ ≤ ⨅ x, x ∈ᴮ u ⟹ Ord x) :
    Γ ≤ (⨅ y, y ∈ᴮ u ⟹ (⨅ z, z ∈ᴮ u ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf; intro y; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  -- ctx = Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u
  -- H_ord : Γ ≤ ⨅ x, x ∈ u ⟹ Ord x
  have H₁ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord y :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ y))))
      (inf_le_left.trans inf_le_right)) bv_imp_elim
  have H₂ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord z :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ z))))
      inf_le_right) bv_imp_elim
  exact Ord.trichotomy H₁ H₂

-- src/bvm_extras2.lean:289
lemma epsilon_wf_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹) :
    Γ ≤ (⨅ x, x ⊆ᴮ u ⟹ ((x =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ))) := by
  apply le_iInf; intro x; rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity x inf_le_right

-- src/bvm_extras2.lean:295
def exists_two (η : bSet 𝔹) : 𝔹 :=
  (⨅ x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x))

-- src/bvm_extras2.lean:297
@[simp] lemma B_ext_exists_two : B_ext (exists_two : bSet 𝔹 → 𝔹) := by
  unfold B_ext exists_two
  exact B_ext_iInf (h := fun x =>
    B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
      B_ext_iSup (h := fun z => B_ext_inf B_ext_mem_right B_ext_const)))

-- src/bvm_extras2.lean:302
lemma one_mem_of_not_zero_and_not_one {η : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord η)
    (H_not_zero : Γ ≤ (η =ᴮ 0)ᶜ) (H_not_one : Γ ≤ (η =ᴮ 1)ᶜ) : Γ ≤ 1 ∈ᴮ η := by
  have H_tri := Ord.trichotomy H_ord Ord_one
  have h_ne1 : Γ ≤ (η =ᴮ 1)ᶜ := H_not_one
  have h_nmem1 : Γ ≤ (η ∈ᴮ (1 : bSet 𝔹))ᶜ := by
    simp only [← imp_bot]; rw [← deduction]
    have heq0 := eq_zero_of_mem_one (Γ := Γ ⊓ η ∈ᴮ 1) inf_le_right
    exact bv_absurd _ heq0 (inf_le_left.trans H_not_zero)
  -- Use bv_or_elim_left: (A ⊔ B) ⊓ Γ ≤ C
  -- Case A = η=1: η=1 ⊓ Γ ≤ ⊥ (from h_ne1), so ≤ 1∈η
  have h1 : η =ᴮ 1 ⊓ Γ ≤ 1 ∈ᴮ η :=
    bv_exfalso (bv_absurd _ inf_le_left (inf_le_right.trans h_ne1))
  -- Case B = η∈1: similarly
  have h2 : η ∈ᴮ 1 ⊓ Γ ≤ 1 ∈ᴮ η :=
    bv_exfalso (bv_absurd _ inf_le_left (inf_le_right.trans h_nmem1))
  -- H_tri : Γ ≤ (η=1 ⊔ η∈1) ⊔ 1∈η = η=1 ⊔ η∈1 ⊔ 1∈η
  -- bv_or_elim_left: (η=1 ⊔ η∈1) ⊓ Γ ≤ 1∈η
  have h12 : (η =ᴮ 1 ⊔ η ∈ᴮ 1) ⊓ Γ ≤ 1 ∈ᴮ η := bv_or_elim_left h1 h2
  -- 1∈η ⊓ Γ ≤ 1∈η trivially
  have h3 : 1 ∈ᴮ η ⊓ Γ ≤ 1 ∈ᴮ η := inf_le_left
  -- H_tri: Γ ≤ (η=1 ⊔ η∈1) ⊔ 1∈η
  -- bv_or_elim_left h12 h3 : ((η=1 ⊔ η∈1) ⊔ 1∈η) ⊓ Γ ≤ 1∈η
  exact le_trans (le_inf H_tri le_rfl) (bv_or_elim_left h12 h3)

-- src/bvm_extras2.lean:312
lemma exists_two_iff {η : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord η) :
    Γ ≤ exists_two η ↔ Γ ≤ (η =ᴮ 1)ᶜ := by
  constructor
  · -- Forward: exists_two η → η ≠ 1
    intro H
    simp only [← imp_bot]; rw [← deduction]
    -- Goal: Γ ⊓ η =ᴮ 1 ≤ ⊥
    -- If η = 1, then 0 ∈ η; exists_two gives w ∈ η with (0∈w or w∈0); but w=0, contradiction
    have h01 : Γ ⊓ η =ᴮ 1 ≤ (0 : bSet 𝔹) ∈ᴮ η :=
      bv_rw'' (ϕ := fun v => (0 : bSet 𝔹) ∈ᴮ v) (bv_symm inf_le_right) zero_mem_one B_ext_mem_right
    unfold exists_two at H
    have h_spec : Γ ⊓ η =ᴮ 1 ≤ ⨆ z, z ∈ᴮ η ⊓ ((0 : bSet 𝔹) ∈ᴮ z ⊔ z ∈ᴮ 0) :=
      le_trans (le_inf (inf_le_left.trans (H.trans (iInf_le _ 0))) h01) bv_imp_elim
    obtain ⟨w, Hw⟩ := exists_convert h_spec
      (B_ext_inf B_ext_mem_left (B_ext_sup (h₁ := B_ext_mem_right) (h₂ := B_ext_mem_left)))
    have Hw_η : Γ ⊓ η =ᴮ 1 ≤ w ∈ᴮ η := Hw.trans inf_le_left
    have Hw_or : Γ ⊓ η =ᴮ 1 ≤ (0 : bSet 𝔹) ∈ᴮ w ⊔ w ∈ᴮ 0 := Hw.trans inf_le_right
    -- w ∈ η = 1 → w = 0
    have Hw_eq0 : Γ ⊓ η =ᴮ 1 ≤ w =ᴮ 0 :=
      eq_zero_of_mem_one (bv_rw'' (ϕ := fun v => w ∈ᴮ v) inf_le_right Hw_η B_ext_mem_right)
    -- Case 0 ∈ w: w = 0, so 0 ∈ 0, contradiction
    have hc1 : (0 : bSet 𝔹) ∈ᴮ w ⊓ (Γ ⊓ η =ᴮ 1) ≤ ⊥ :=
      bot_of_mem_self' (bv_rw'' (ϕ := fun v => (0 : bSet 𝔹) ∈ᴮ v)
        (inf_le_right.trans Hw_eq0) inf_le_left B_ext_mem_right)
    -- Case w ∈ 0: 0 = ∅, contradiction
    have hc2 : w ∈ᴮ (0 : bSet 𝔹) ⊓ (Γ ⊓ η =ᴮ 1) ≤ ⊥ :=
      bv_exfalso (bot_of_mem_empty (bv_rw'' (ϕ := fun v => w ∈ᴮ v)
        zero_eq_empty inf_le_left B_ext_mem_right))
    exact le_trans (le_inf Hw_or le_rfl) (bv_or_elim_left hc1 hc2)
  · -- Backward: η ≠ 1 → exists_two η
    intro H_ne1
    unfold exists_two
    -- Case: η = 0 or η ≠ 0
    have h_zero : (η =ᴮ 0) ⊓ Γ ≤ ⨅ x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x) := by
      -- Rewrite η to 0 to ∅; then forall_empty applies
      apply bv_rw' (H := inf_le_left) (h_congr := B_ext_exists_two)
      apply bv_rw' (H := zero_eq_empty) (h_congr := B_ext_exists_two)
      exact forall_empty
    have h_nonzero : (η =ᴮ 0)ᶜ ⊓ Γ ≤ ⨅ x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x) := by
      have H_ord' : (η =ᴮ 0)ᶜ ⊓ Γ ≤ Ord η := inf_le_right.trans H_ord
      have H_ne0 : (η =ᴮ 0)ᶜ ⊓ Γ ≤ (η =ᴮ 0)ᶜ := inf_le_left
      have H_ne1' : (η =ᴮ 0)ᶜ ⊓ Γ ≤ (η =ᴮ 1)ᶜ := inf_le_right.trans H_ne1
      have h1_mem : (η =ᴮ 0)ᶜ ⊓ Γ ≤ (1 : bSet 𝔹) ∈ᴮ η :=
        one_mem_of_not_zero_and_not_one H_ord' H_ne0 H_ne1'
      apply le_iInf; intro z; rw [← deduction]
      -- For z ∈ η, find w ∈ η with z ∈ w or w ∈ z, using 1 ∈ η
      set ctx := (η =ᴮ 0)ᶜ ⊓ Γ ⊓ z ∈ᴮ η
      have Hz_η : ctx ≤ z ∈ᴮ η := inf_le_right
      have h1_η : ctx ≤ (1 : bSet 𝔹) ∈ᴮ η := inf_le_left.trans h1_mem
      have Hz_ord : ctx ≤ Ord z := Ord_of_mem_Ord Hz_η (inf_le_left.trans H_ord')
      -- Trichotomy z vs 1
      have H_tri := Ord.trichotomy Hz_ord (inf_le_left.trans (inf_le_right.trans Ord_one))
      -- Case z = 1: pick w = 0 ∈ η (0∈1=z∈η); w=0 ∈ z
      have hcase1 : (z =ᴮ 1) ⊓ ctx ≤ ⨆ w, w ∈ᴮ η ⊓ (z ∈ᴮ w ⊔ w ∈ᴮ z) := by
        apply le_iSup_of_le 0
        apply le_inf
        · -- 0 ∈ η: 0 ∈ 1 = z, and z ∈ η
          exact mem_of_mem_Ord
            (bv_rw'' (ϕ := fun v => (0 : bSet 𝔹) ∈ᴮ v) (bv_symm inf_le_left)
              zero_mem_one B_ext_mem_right)
            (inf_le_right.trans Hz_η)
            (inf_le_right.trans (inf_le_left.trans H_ord'))
        · -- 0 ∈ z (since 0 ∈ 1 = z)
          exact bv_or_right (bv_rw'' (ϕ := fun v => (0 : bSet 𝔹) ∈ᴮ v)
            (bv_symm inf_le_left) zero_mem_one B_ext_mem_right)
      -- Case z ∈ 1: z = 0; pick w = 1 ∈ η; z ∈ 1 = w
      have hcase2 : (z ∈ᴮ 1) ⊓ ctx ≤ ⨆ w, w ∈ᴮ η ⊓ (z ∈ᴮ w ⊔ w ∈ᴮ z) := by
        apply le_iSup_of_le 1
        exact le_inf (inf_le_right.trans h1_η) (bv_or_left inf_le_left)
      -- Case 1 ∈ z: pick w = 1 ∈ η; 1 ∈ z, so w ∈ z
      have hcase3 : ((1 : bSet 𝔹) ∈ᴮ z) ⊓ ctx ≤ ⨆ w, w ∈ᴮ η ⊓ (z ∈ᴮ w ⊔ w ∈ᴮ z) := by
        apply le_iSup_of_le 1
        exact le_inf (inf_le_right.trans h1_η) (bv_or_right inf_le_left)
      exact le_trans (le_inf H_tri le_rfl)
        (bv_or_elim_left (bv_or_elim_left hcase1 hcase2) hcase3)
    -- Combine: split on η=0 or η≠0
    calc Γ = (η =ᴮ 0 ⊔ (η =ᴮ 0)ᶜ) ⊓ Γ := by rw [sup_compl_eq_top, top_inf_eq]
         _ = (η =ᴮ 0) ⊓ Γ ⊔ (η =ᴮ 0)ᶜ ⊓ Γ := by rw [inf_sup_right]
         _ ≤ _ := sup_le h_zero h_nonzero

end Ord

-- ============================================================
-- src/bvm_extras2.lean:347-537: section eps_iso
-- ============================================================

section eps_iso
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:350
@[reducible] def strong_eps_hom (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ z₁, z₁ ∈ᴮ x ⟹ ⨅ z₂, z₂ ∈ᴮ x ⟹ ⨅ w₁, w₁ ∈ᴮ y ⟹ ⨅ w₂, w₂ ∈ᴮ y ⟹
    (pair z₁ w₁ ∈ᴮ f ⟹ (pair z₂ w₂ ∈ᴮ f ⟹ (z₁ ∈ᴮ z₂ ⇔ w₁ ∈ᴮ w₂)))

-- src/bvm_extras2.lean:352
lemma strong_eps_hom_iff {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ strong_eps_hom x y f ↔
    ∀ {Γ'} (_H_le : Γ' ≤ Γ), ∀ z₁ (_Hz₁_mem : Γ' ≤ z₁ ∈ᴮ x) (z₂) (_Hz₂_mem : Γ' ≤ z₂ ∈ᴮ x)
      (w₁) (_Hw₁_mem : Γ' ≤ w₁ ∈ᴮ y) (w₂) (_Hw₂_mem : Γ' ≤ w₂ ∈ᴮ y)
      (_Hpr₁_mem : Γ' ≤ pair z₁ w₁ ∈ᴮ f) (_Hpr₂_mem : Γ' ≤ pair z₂ w₂ ∈ᴮ f),
      Γ' ≤ z₁ ∈ᴮ z₂ ↔ Γ' ≤ w₁ ∈ᴮ w₂ := by
  constructor
  · -- Forward: unfold the iInf structure and use bv_biimp_iff
    intro H Γ' H_le z₁ Hz₁ z₂ Hz₂ w₁ Hw₁ w₂ Hw₂ Hpr₁ Hpr₂
    -- Unfold strong_eps_hom manually (we can't use strong_eps_hom_unfold since it's defined after)
    have H' := le_trans H_le H
    have h1 := le_trans H' (iInf_le _ z₁)
    have h2 := le_trans (le_inf h1 Hz₁) bv_imp_elim
    have h3 := le_trans h2 (iInf_le _ z₂)
    have h4 := le_trans (le_inf h3 Hz₂) bv_imp_elim
    have h5 := le_trans h4 (iInf_le _ w₁)
    have h6 := le_trans (le_inf h5 Hw₁) bv_imp_elim
    have h7 := le_trans h6 (iInf_le _ w₂)
    have h8 := le_trans (le_inf h7 Hw₂) bv_imp_elim
    have h9 := le_trans (le_inf h8 Hpr₁) bv_imp_elim
    have h10 := le_trans (le_inf h9 Hpr₂) bv_imp_elim
    rw [bv_biimp_iff] at h10
    exact h10 le_rfl
  · -- Backward: build the iInf structure
    intro H
    unfold strong_eps_hom
    apply le_iInf; intro z₁; rw [← deduction]
    apply le_iInf; intro z₂; rw [← deduction]
    apply le_iInf; intro w₁; rw [← deduction]
    apply le_iInf; intro w₂; rw [← deduction, ← deduction, ← deduction]
    -- ctx6 = Γ ⊓ z₁∈x ⊓ z₂∈x ⊓ w₁∈y ⊓ w₂∈y ⊓ pair z₁ w₁ ∈ f ⊓ pair z₂ w₂ ∈ f ≤ z₁∈z₂ ⇔ w₁∈w₂
    -- Note: the context is left-associated: ((((((Γ ⊓ z₁∈x) ⊓ z₂∈x) ⊓ w₁∈y) ⊓ w₂∈y) ⊓ pr₁∈f) ⊓ pr₂∈f)
    rw [bv_biimp_iff]
    intro Γ'' H_Γ''
    apply H
    · -- Γ'' ≤ Γ
      exact H_Γ''.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left)))))
    · -- Γ'' ≤ z₁ ∈ᴮ x
      exact H_Γ''.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right)))))
    · -- Γ'' ≤ z₂ ∈ᴮ x
      exact H_Γ''.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))))
    · -- Γ'' ≤ w₁ ∈ᴮ y
      exact H_Γ''.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    · -- Γ'' ≤ w₂ ∈ᴮ y
      exact H_Γ''.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
    · -- Γ'' ≤ pair z₁ w₁ ∈ᴮ f
      exact H_Γ''.trans (inf_le_left.trans inf_le_right)
    · -- Γ'' ≤ pair z₂ w₂ ∈ᴮ f
      exact H_Γ''.trans inf_le_right

-- src/bvm_extras2.lean:365
lemma strong_eps_hom_unfold {x y f : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ strong_eps_hom x y f) :
    ∀ z₁ (Hz₁_mem : Γ ≤ z₁ ∈ᴮ x) (z₂) (Hz₂_mem : Γ ≤ z₂ ∈ᴮ x)
      (w₁) (Hw₁_mem : Γ ≤ w₁ ∈ᴮ y) (w₂) (Hw₂_mem : Γ ≤ w₂ ∈ᴮ y)
      (Hpr₁_mem : Γ ≤ pair z₁ w₁ ∈ᴮ f) (Hpr₂_mem : Γ ≤ pair z₂ w₂ ∈ᴮ f),
      Γ ≤ z₁ ∈ᴮ z₂ ↔ Γ ≤ w₁ ∈ᴮ w₂ :=
    fun z₁ Hz₁ z₂ Hz₂ w₁ Hw₁ w₂ Hw₂ Hpr₁ Hpr₂ => by
  -- strong_eps_hom x y f = ⨅ z₁, z₁∈x ⟹ ⨅ z₂, z₂∈x ⟹ ⨅ w₁, w₁∈y ⟹ ⨅ w₂, w₂∈y ⟹
  --   pair z₁ w₁ ∈ f ⟹ (pair z₂ w₂ ∈ f ⟹ (z₁∈z₂ ⇔ w₁∈w₂))
  have h1 := le_trans H (iInf_le _ z₁)
  have h2 := le_trans (le_inf h1 Hz₁) bv_imp_elim
  have h3 := le_trans h2 (iInf_le _ z₂)
  have h4 := le_trans (le_inf h3 Hz₂) bv_imp_elim
  have h5 := le_trans h4 (iInf_le _ w₁)
  have h6 := le_trans (le_inf h5 Hw₁) bv_imp_elim
  have h7 := le_trans h6 (iInf_le _ w₂)
  have h8 := le_trans (le_inf h7 Hw₂) bv_imp_elim
  have h9 := le_trans (le_inf h8 Hpr₁) bv_imp_elim
  have h10 := le_trans (le_inf h9 Hpr₂) bv_imp_elim
  rw [bv_biimp_iff] at h10
  exact h10 le_rfl

-- src/bvm_extras2.lean:371
def eps_iso (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ (strong_eps_hom x y f) ⊓ is_surj x y f

-- src/bvm_extras2.lean:373
lemma is_surj_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_surj x y f :=
  le_trans H_eps_iso inf_le_right

-- src/bvm_extras2.lean:376
lemma is_function_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_function x y f :=
  le_trans H_eps_iso (inf_le_left.trans inf_le_left)

-- src/bvm_extras2.lean:379
lemma strong_eps_hom_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ strong_eps_hom x y f :=
  le_trans H_eps_iso (inf_le_left.trans inf_le_right)

-- src/bvm_extras2.lean:382
lemma eps_iso_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ z₁ ∈ᴮ z₂)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ w₁ ∈ᴮ w₂ :=
  (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso H₂)
    z₁ H_mem z₂ H_mem' w₁ H_mem''' w₂ H_mem'''' H_mem_pr₁ H_mem_pr₂).mp H_mem''

-- src/bvm_extras2.lean:385
lemma eps_iso_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (H_mem'' : Γ ≤ w₁ ∈ᴮ w₂) : Γ ≤ z₁ ∈ᴮ z₂ :=
  (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso H₂)
    z₁ H_mem z₂ H_mem' w₁ H_mem''' w₂ H_mem'''' H_mem_pr₁ H_mem_pr₂).mpr H_mem''

-- src/bvm_extras2.lean:388
lemma eps_iso_not_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ := by
  simp only [← imp_bot]; rw [← deduction]
  set ctx' := Γ ⊓ w₁ ∈ᴮ w₂
  have h_z12 : ctx' ≤ z₁ ∈ᴮ z₂ :=
    eps_iso_mem' (inf_le_left.trans H₂) (inf_le_left.trans H_mem) (inf_le_left.trans H_mem')
      (inf_le_left.trans H_mem''') (inf_le_left.trans H_mem_pr₁)
      (inf_le_left.trans H_mem'''') (inf_le_left.trans H_mem_pr₂) inf_le_right
  exact bv_absurd _ h_z12 (inf_le_left.trans H_mem'')

-- src/bvm_extras2.lean:394
lemma eps_iso_not_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (H_mem'' : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ) : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ := by
  simp only [← imp_bot]; rw [← deduction]
  set ctx' := Γ ⊓ z₁ ∈ᴮ z₂
  have h_w12 : ctx' ≤ w₁ ∈ᴮ w₂ :=
    eps_iso_mem (inf_le_left.trans H₂) (inf_le_left.trans H_mem) (inf_le_left.trans H_mem')
      inf_le_right (inf_le_left.trans H_mem''') (inf_le_left.trans H_mem_pr₁)
      (inf_le_left.trans H_mem'''') (inf_le_left.trans H_mem_pr₂)
  exact bv_absurd _ h_w12 (inf_le_left.trans H_mem'')

-- src/bvm_extras2.lean:400
lemma eps_iso_inj_of_Ord {x y f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H₃ : Γ ≤ eps_iso x y f) : Γ ≤ is_inj f := by
  -- is_inj f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⊓ v₁=v₂ ⟹ w₁=w₂
  unfold is_inj
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  -- ctx = Γ ⊓ (pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⊓ v₁ =ᴮ v₂)
  set ctx := Γ ⊓ (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂)
  have H_func : ctx ≤ is_function x y f := inf_le_left.trans (is_function_of_eps_iso H₃)
  have H_pr₁ : ctx ≤ pair w₁ v₁ ∈ᴮ f := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have H_pr₂ : ctx ≤ pair w₂ v₂ ∈ᴮ f := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have H_veq : ctx ≤ v₁ =ᴮ v₂ := inf_le_right.trans inf_le_right
  have Hw₁_mem : ctx ≤ w₁ ∈ᴮ x := mem_domain_of_is_function H_pr₁ H_func
  have Hw₂_mem : ctx ≤ w₂ ∈ᴮ x := mem_domain_of_is_function H_pr₂ H_func
  have Hv₁_mem : ctx ≤ v₁ ∈ᴮ y := mem_codomain_of_is_function H_pr₁ H_func
  have Hv₂_mem : ctx ≤ v₂ ∈ᴮ y := mem_codomain_of_is_function H_pr₂ H_func
  have Hw₁_ord : ctx ≤ Ord w₁ := Ord_of_mem_Ord Hw₁_mem (inf_le_left.trans H₁)
  have Hw₂_ord : ctx ≤ Ord w₂ := Ord_of_mem_Ord Hw₂_mem (inf_le_left.trans H₁)
  -- v₁ = v₂, so ¬(v₁ ∈ v₂) and ¬(v₂ ∈ v₁)
  -- derive ¬(w₁ ∈ w₂) and ¬(w₂ ∈ w₁) from these via eps_iso_not_mem'
  have H_v₁_nmem_v₂ : ctx ≤ (v₁ ∈ᴮ v₂)ᶜ :=
    ((Ord.eq_iff_not_mem (Ord_of_mem_Ord Hv₁_mem (inf_le_left.trans H₂))
                         (Ord_of_mem_Ord Hv₂_mem (inf_le_left.trans H₂))).mp H_veq).1
  have H_v₂_nmem_v₁ : ctx ≤ (v₂ ∈ᴮ v₁)ᶜ :=
    ((Ord.eq_iff_not_mem (Ord_of_mem_Ord Hv₁_mem (inf_le_left.trans H₂))
                         (Ord_of_mem_Ord Hv₂_mem (inf_le_left.trans H₂))).mp H_veq).2
  have H_w₁_nmem_w₂ : ctx ≤ (w₁ ∈ᴮ w₂)ᶜ :=
    eps_iso_not_mem' (inf_le_left.trans H₃) Hw₁_mem Hw₂_mem Hv₁_mem H_pr₁ Hv₂_mem H_pr₂ H_v₁_nmem_v₂
  have H_w₂_nmem_w₁ : ctx ≤ (w₂ ∈ᴮ w₁)ᶜ :=
    eps_iso_not_mem' (inf_le_left.trans H₃) Hw₂_mem Hw₁_mem Hv₂_mem H_pr₂ Hv₁_mem H_pr₁ H_v₂_nmem_v₁
  exact Ord.eq_of_not_mem Hw₁_ord Hw₂_ord H_w₁_nmem_w₂ H_w₂_nmem_w₁

-- src/bvm_extras2.lean:423
def eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H₃ : Γ ≤ eps_iso x y f) : bSet 𝔹 :=
  inj_inverse (is_func'_of_is_function (is_function_of_eps_iso H₃))
    (eps_iso_inj_of_Ord H₁ H₂ H₃)

-- src/bvm_extras2.lean:425
lemma eps_iso_inv_surj {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_surj y x (eps_iso_inv H₁ H₂ H₃) :=
  inj_inverse.is_surj_surj
    (H_func := is_func'_of_is_function (is_function_of_eps_iso H₃))
    (H_inj := eps_iso_inj_of_Ord H₁ H₂ H₃)
    (is_surj_of_eps_iso H₃)

-- src/bvm_extras2.lean:428
lemma eps_iso_inv_is_function {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_function y x (eps_iso_inv H₁ H₂ H₃) :=
  inj_inverse.is_function_surj
    (H_func := is_func'_of_is_function (is_function_of_eps_iso H₃))
    (H_inj := eps_iso_inj_of_Ord H₁ H₂ H₃)
    (is_surj_of_eps_iso H₃)

-- src/bvm_extras2.lean:433
lemma eps_iso_inv_strong_eps_hom {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ strong_eps_hom y x (eps_iso_inv H₁ H₂ H₃) := by
  have H_seh := strong_eps_hom_of_eps_iso H₃
  -- eps_iso_inv = inj_inverse (is_func' x y f) (is_inj f)
  -- pair z₁ w₁ ∈ eps_iso_inv ↔ w₁ ∈ x ∧ z₁ ∈ y ∧ pair w₁ z₁ ∈ f
  set H_func := is_func'_of_is_function (is_function_of_eps_iso H₃)
  set H_inj := eps_iso_inj_of_Ord H₁ H₂ H₃
  -- Use strong_eps_hom_iff to prove strong_eps_hom y x (eps_iso_inv)
  rw [strong_eps_hom_iff]
  intro Γ' H_le z₁ Hz₁_y z₂ Hz₂_y w₁ Hw₁_x w₂ Hw₂_x Hpr₁ Hpr₂
  -- z₁, z₂ ∈ y (the domain of the inverse), w₁, w₂ ∈ x (the codomain of the inverse)
  -- pair z₁ w₁ ∈ eps_iso_inv means w₁ ∈ x ∧ z₁ ∈ y ∧ pair w₁ z₁ ∈ f
  have hpr₁ := (mem_inj_inverse_iff H_func H_inj).mp Hpr₁
  have hpr₂ := (mem_inj_inverse_iff H_func H_inj).mp Hpr₂
  -- hpr₁ : w₁ ∈ x ∧ z₁ ∈ y ∧ pair w₁ z₁ ∈ f
  -- hpr₂ : w₂ ∈ x ∧ z₂ ∈ y ∧ pair w₂ z₂ ∈ f
  -- Apply strong_eps_hom x y f to get: w₁∈w₂ ↔ z₁∈z₂
  -- We need z₁∈z₂ ↔ w₁∈w₂ (i.e., the symmetric version)
  have h_iff := (strong_eps_hom_iff.mp H_seh) H_le
    w₁ hpr₁.1 w₂ hpr₂.1 z₁ hpr₁.2.1 z₂ hpr₂.2.1 hpr₁.2.2 hpr₂.2.2
  -- h_iff : Γ' ≤ w₁ ∈ w₂ ↔ Γ' ≤ z₁ ∈ z₂
  exact h_iff.symm

-- src/bvm_extras2.lean:449
lemma eps_iso_eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ eps_iso y x (eps_iso_inv H₁ H₂ H₃) :=
  le_inf (le_inf eps_iso_inv_is_function eps_iso_inv_strong_eps_hom) eps_iso_inv_surj

-- src/bvm_extras2.lean:453
lemma eps_iso_symm {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    (Γ ≤ ⨆ f, eps_iso x y f) ↔ (Γ ≤ ⨆ f, eps_iso y x f) := by
  -- B_ext for eps_iso in f variable
  have B_eps_iso_f : ∀ (a b : bSet 𝔹), B_ext (fun f : bSet 𝔹 => eps_iso a b f) := fun a b => by
    unfold eps_iso is_surj strong_eps_hom
    -- eps_iso a b f = (is_function a b f ⊓ strong_eps_hom a b f) ⊓ is_surj a b f
    refine B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_is_function_right) (h₂ := ?_)) (h₂ := ?_)
    · -- strong_eps_hom in f
      refine B_ext_iInf (h := fun z₁ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iInf (h := fun z₂ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
          B_ext_iInf (h := fun w₁ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
            B_ext_iInf (h := fun w₂ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
              B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
                B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))))))))
    · -- is_surj in f
      refine B_ext_iInf (h := fun v => B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun w => B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_mem_right))))
  constructor
  · intro H
    obtain ⟨f, Hf⟩ := exists_convert H (B_eps_iso_f x y)
    exact le_iSup_of_le _ (@eps_iso_eps_iso_inv _ _ x y f _ H₁ H₂ Hf)
  · intro H
    obtain ⟨f, Hf⟩ := exists_convert H (B_eps_iso_f y x)
    exact le_iSup_of_le _ (@eps_iso_eps_iso_inv _ _ y x f _ H₂ H₁ Hf)

-- src/bvm_extras2.lean:460
lemma eps_iso_mono {x y z f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord y) (H₂ : Γ ≤ z ⊆ᴮ y)
    (H₃ : Γ ≤ eps_iso y z f) (H₄ : Γ ≤ x ∈ᴮ y) (w' : bSet 𝔹)
    (Hw' : Γ ≤ pair x w' ∈ᴮ f) : Γ ≤ x ⊆ᴮ w' := by
  -- Let A = { v ∈ y | ∀ w, pair v w ∈ f → w ∈ v } (elements of y whose f-image is below them)
  -- We claim A = ∅. By regularity, if A ≠ ∅ get minimal a ∈ A; derive wa ∈ A ∩ a, contradiction.
  have H_func := is_function_of_eps_iso H₃
  have H_total := is_total_of_is_function H_func
  -- Define the B_ext for the comprehend predicate: fun v => ⨅ w, pair v w ∈ f ⟹ w ∈ v
  have H_Bext_A : B_ext (fun v : bSet 𝔹 => ⨅ w, pair v w ∈ᴮ f ⟹ w ∈ᴮ v) :=
    B_ext_iInf (h := fun w => B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_mem_right))
  set A := comprehend (fun v : bSet 𝔹 => ⨅ w, pair v w ∈ᴮ f ⟹ w ∈ᴮ v) y
  -- The iff for A-membership:
  -- a ∈ A ↔ ∃ a', a' ∈ y ∧ a = a' ∧ ∀ w, pair a' w ∈ f → w ∈ a'
  have mem_A_iff : ∀ {a : bSet 𝔹} {Γ' : 𝔹}, Γ' ≤ a ∈ᴮ A ↔
      Γ' ≤ ⨆ v, v ∈ᴮ y ⊓ (a =ᴮ v ⊓ ⨅ w, pair v w ∈ᴮ f ⟹ w ∈ᴮ v) :=
    fun {a Γ'} => mem_comprehend_iff₂ _ y H_Bext_A
  -- Step 1: Prove A = ∅
  suffices H_empty : Γ ≤ A =ᴮ ∅ by
    -- From A = ∅: if ¬(x ⊆ w') we'd get x ∈ A, contradiction
    apply bv_by_contra; rw [← deduction]
    -- goal: Γ ⊓ (x ⊆ w')ᶜ ≤ ⊥
    -- H_contra: ¬(x ⊆ w'), so by Ord.lt_of_not_le: w' ∈ x
    have H_x_ord : Γ ⊓ (x ⊆ᴮ w')ᶜ ≤ Ord x :=
      Ord_of_mem_Ord (inf_le_left.trans H₄) (inf_le_left.trans H₁)
    have H_w'_ord : Γ ⊓ (x ⊆ᴮ w')ᶜ ≤ Ord w' := by
      apply Ord_of_mem_Ord _ (inf_le_left.trans H₁)
      exact mem_of_mem_subset (inf_le_left.trans H₂)
        (mem_codomain_of_is_function (inf_le_left.trans Hw') (inf_le_left.trans H_func))
    have H_w'_mem_x : Γ ⊓ (x ⊆ᴮ w')ᶜ ≤ w' ∈ᴮ x :=
      Ord.lt_of_not_le H_x_ord H_w'_ord inf_le_right
    -- x ∈ A since x ∈ y and ∀ w, pair x w ∈ f → w ∈ x
    have Hx_A : Γ ⊓ (x ⊆ᴮ w')ᶜ ≤ x ∈ᴮ A := by
      rw [mem_A_iff]
      apply le_iSup_of_le x
      refine le_inf (inf_le_left.trans H₄) (le_inf bv_refl ?_)
      apply le_iInf; intro w; rw [← deduction]
      -- need: (Γ ⊓ (x⊆w')ᶜ) ⊓ pair x w ∈ f ≤ w ∈ x
      -- pair x w ∈ f and pair x w' ∈ f → w = w' (by func uniqueness)
      set ctx := Γ ⊓ (x ⊆ᴮ w')ᶜ ⊓ pair x w ∈ᴮ f
      have Hw_eq : ctx ≤ w =ᴮ w' :=
        eq_of_is_function_of_eq (inf_le_left.trans (inf_le_left.trans H_func))
          bv_refl inf_le_right (inf_le_left.trans (inf_le_left.trans Hw'))
      exact bv_rw'' (bv_symm Hw_eq) (inf_le_left.trans H_w'_mem_x) B_ext_mem_left
    -- x ∈ A but A = ∅, contradiction
    exact bv_exfalso (bot_of_mem_empty
      (bv_rw'' (inf_le_left.trans H_empty) Hx_A B_ext_mem_right))
  -- Step 2: Prove A = ∅ by regularity
  apply bv_by_contra; rw [← deduction]
  -- goal: Γ ⊓ (A =ᴮ ∅)ᶜ ≤ ⊥
  -- Get minimal a ∈ A by regularity
  have H_A_ne : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ (A =ᴮ ∅)ᶜ := inf_le_right
  have H_reg := bSet_axiom_of_regularity A H_A_ne
  obtain ⟨a, Ha⟩ := exists_convert H_reg
    (B_ext_inf B_ext_mem_left (B_ext_iInf (h := fun z' =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_neg (h := B_ext_mem_right)))))
  have Ha_A : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ a ∈ᴮ A := Ha.trans inf_le_left
  have Ha_min : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ ⨅ z', z' ∈ᴮ A ⟹ (z' ∈ᴮ a)ᶜ := Ha.trans inf_le_right
  -- From a ∈ A: ∃ a', a' ∈ y ∧ a = a' ∧ ∀ w, pair a' w ∈ f → w ∈ a'
  have Ha_in_A : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ ⨆ v, v ∈ᴮ y ⊓ (a =ᴮ v ⊓ ⨅ w, pair v w ∈ᴮ f ⟹ w ∈ᴮ v) :=
    mem_A_iff.mp Ha_A
  obtain ⟨a', Ha'⟩ := exists_convert Ha_in_A
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_bv_eq_right H_Bext_A))
  have Ha'_y : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ a' ∈ᴮ y := Ha'.trans inf_le_left
  have Ha'_eq : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ a =ᴮ a' := Ha'.trans (inf_le_right.trans inf_le_left)
  have Ha'_cond : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ ⨅ w, pair a' w ∈ᴮ f ⟹ w ∈ᴮ a' :=
    Ha'.trans (inf_le_right.trans inf_le_right)
  -- a ∈ y via a = a' ∈ y
  have Ha_y : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ a ∈ᴮ y :=
    bv_rw'' (bv_symm Ha'_eq) Ha'_y B_ext_mem_left
  -- Get wa: total function gives pair a wa ∈ f
  have H_total_a : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ ⨆ wa, wa ∈ᴮ z ⊓ pair a wa ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (H_total.trans (iInf_le _ a))) Ha_y) bv_imp_elim
  obtain ⟨wa, Hwa⟩ := exists_convert H_total_a (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hwa_z : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ wa ∈ᴮ z := Hwa.trans inf_le_left
  have Hwa_pair : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ pair a wa ∈ᴮ f := Hwa.trans inf_le_right
  -- wa ∈ a via the comprehend condition on a': pair a' wa ∈ f → wa ∈ a'
  -- From pair a wa ∈ f and a = a', get pair a' wa ∈ f
  have Hwa_pair' : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ pair a' wa ∈ᴮ f :=
    bv_rw'' (ϕ := fun v => pair v wa ∈ᴮ f) Ha'_eq Hwa_pair B_ext_pair_mem_left
  have Hwa_a' : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ wa ∈ᴮ a' :=
    le_trans (le_inf (Ha'_cond.trans (iInf_le _ wa)) Hwa_pair') bv_imp_elim
  -- wa ∈ a (= a')
  have Hwa_mem_a : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ wa ∈ᴮ a :=
    bv_rw'' (bv_symm Ha'_eq) Hwa_a' B_ext_mem_right
  -- wa ∈ y (since wa ∈ z ⊆ y)
  have Hwa_y : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ wa ∈ᴮ y :=
    mem_of_mem_subset (inf_le_left.trans H₂) Hwa_z
  -- wa ∈ A: wa ∈ y and ∀ wa', pair wa wa' ∈ f → wa' ∈ wa
  have Hwa_A : Γ ⊓ (A =ᴮ ∅)ᶜ ≤ wa ∈ᴮ A := by
    rw [mem_A_iff]
    apply le_iSup_of_le wa
    refine le_inf Hwa_y (le_inf bv_refl ?_)
    apply le_iInf; intro wa'; rw [← deduction]
    -- need: (Γ ⊓ (A=∅)ᶜ) ⊓ pair wa wa' ∈ f ≤ wa' ∈ wa
    set ctx2 := Γ ⊓ (A =ᴮ ∅)ᶜ ⊓ pair wa wa' ∈ᴮ f
    -- wa' ∈ z (codomain of f): from pair wa wa' ∈ f
    have Hwa'_z : ctx2 ≤ wa' ∈ᴮ z :=
      mem_codomain_of_is_function inf_le_right (inf_le_left.trans (inf_le_left.trans H_func))
    -- Use eps_iso_mem: wa ∈ a → wa' ∈ wa
    --   eps_iso y z f, wa∈y, a∈y, wa∈a, wa'∈z, pair wa wa' ∈ f, wa∈z, pair a wa ∈ f
    exact eps_iso_mem (inf_le_left.trans (inf_le_left.trans H₃))
      (inf_le_left.trans Hwa_y) (inf_le_left.trans Ha_y)
      (inf_le_left.trans Hwa_mem_a)
      Hwa'_z inf_le_right
      (inf_le_left.trans Hwa_z) (inf_le_left.trans Hwa_pair)
  -- wa ∈ A and wa ∈ a contradicts minimality of a
  have H_min_wa := le_trans (le_inf (Ha_min.trans (iInf_le _ wa)) Hwa_A) bv_imp_elim
  exact bv_absurd _ Hwa_mem_a H_min_wa

-- src/bvm_extras2.lean:505
lemma eq_of_Ord_eps_iso_aux {x y : bSet 𝔹} {Γ : 𝔹} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso y x f) (H_mem : Γ ≤ x ∈ᴮ y) : Γ ≤ ⊥ := by
  -- Get a concrete f from the existential
  have B_eps_iso_f : B_ext (fun f : bSet 𝔹 => eps_iso y x f) := by
    unfold eps_iso is_surj strong_eps_hom
    exact B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_is_function_right)
      (h₂ := B_ext_iInf (h := fun z₁ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iInf (h := fun z₂ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
          B_ext_iInf (h := fun w₁ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
            B_ext_iInf (h := fun w₂ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
              B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
                B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const)))))))))))) (h₂ :=
      B_ext_iInf (h := fun v => B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun w => B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_mem_right)))))
  obtain ⟨f, Hf⟩ := exists_convert H_eps_iso B_eps_iso_f
  have H_function := is_function_of_eps_iso Hf
  have H_total := is_total_of_is_function H_function
  -- Get w = f(x) with w ∈ x and pair x w ∈ f
  have H_total_x : Γ ≤ ⨆ w, w ∈ᴮ x ⊓ pair x w ∈ᴮ f :=
    le_trans (le_inf (H_total.trans (iInf_le _ x)) H_mem) bv_imp_elim
  obtain ⟨w, Hw⟩ := exists_convert H_total_x (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hw_x : Γ ≤ w ∈ᴮ x := Hw.trans inf_le_left
  have Hw_pair : Γ ≤ pair x w ∈ᴮ f := Hw.trans inf_le_right
  -- x ⊆ y (since x ∈ y and y is an ordinal)
  have H_x_sub_y : Γ ≤ x ⊆ᴮ y := subset_of_mem_Ord H_mem Hy_ord
  -- Apply eps_iso_mono: x ⊆ w
  have H_x_sub_w : Γ ≤ x ⊆ᴮ w :=
    eps_iso_mono Hy_ord H_x_sub_y Hf H_mem w Hw_pair
  -- From x ⊆ w, get either x ∈ w or x = w
  have H_w_ord : Γ ≤ Ord w := Ord_of_mem_Ord Hw_x Hx_ord
  have H_lor : Γ ≤ x ∈ᴮ w ⊔ x =ᴮ w :=
    (Ord.le_iff_lt_or_eq Hx_ord H_w_ord).mp H_x_sub_w
  -- Case split: x ∈ w → bot_of_mem_mem' with w ∈ x; x = w → w ∈ w from w ∈ x
  apply le_trans (le_inf H_lor le_rfl)
  apply bv_or_elim_left
  · -- x ∈ w and w ∈ x → contradiction
    exact bot_of_mem_mem' x w inf_le_left (inf_le_right.trans Hw_x)
  · -- x = w and w ∈ x → w ∈ w → contradiction
    apply bot_of_mem_self'
    exact bv_rw'' (ϕ := fun v => w ∈ᴮ v) inf_le_left (inf_le_right.trans Hw_x) B_ext_mem_right

-- src/bvm_extras2.lean:526
lemma eq_of_Ord_eps_iso {x y : bSet 𝔹} {Γ : 𝔹} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso x y f) : Γ ≤ x =ᴮ y := by
  -- Use ordinal trichotomy: x = y, x ∈ y, or y ∈ x
  have H_tri := Ord.trichotomy Hx_ord Hy_ord
  -- trichotomy: (x=y ⊔ x∈y) ⊔ y∈x (left-assoc)
  apply le_trans (le_inf H_tri le_rfl)
  apply bv_or_elim_left
  · -- Case x=y ⊔ x∈y
    apply bv_or_elim_left
    · -- Case x = y: done
      exact inf_le_left
    · -- Case x ∈ y: get eps_iso y x (inverse), then contradiction
      apply bv_exfalso
      -- Swap direction: eps_iso x y → eps_iso y x
      have H_eps_iso_sym : (x ∈ᴮ y) ⊓ Γ ≤ ⨆ f, eps_iso y x f :=
        (eps_iso_symm (inf_le_right.trans Hx_ord) (inf_le_right.trans Hy_ord)).mp
          (inf_le_right.trans H_eps_iso)
      exact eq_of_Ord_eps_iso_aux (inf_le_right.trans Hx_ord) (inf_le_right.trans Hy_ord)
        H_eps_iso_sym inf_le_left
  · -- Case y ∈ x: eps_iso x y f and y ∈ x → contradiction
    apply bv_exfalso
    exact eq_of_Ord_eps_iso_aux (inf_le_right.trans Hy_ord) (inf_le_right.trans Hx_ord)
      (inf_le_right.trans H_eps_iso) inf_le_left

end eps_iso

-- ============================================================
-- src/bvm_extras2.lean:539-597: remainder
-- ============================================================

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:541
def is_limit (η : bSet 𝔹) : 𝔹 :=
  (∅ ∈ᴮ η) ⊓ (⨅ x, x ∈ᴮ η ⟹ ⨆ y, y ∈ᴮ η ⊓ x ∈ᴮ y)

-- src/bvm_extras2.lean:543
lemma is_epsilon_well_founded {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ epsilon_well_founded x := by
  rw [epsilon_well_founded]
  apply le_iInf; intro u; rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity u inf_le_right

-- src/bvm_extras2.lean:546
lemma Ord_succ {η : bSet 𝔹} {Γ : 𝔹} (H_Ord : Γ ≤ Ord η) : Γ ≤ Ord (succ η) := by
  -- Ord = epsilon_trichotomy ⊓ epsilon_well_founded ⊓ is_transitive
  refine le_inf (le_inf ?_ ?_) ?_
  · -- epsilon_trichotomy (succ η): use epsilon_trichotomy_of_sub_Ord
    -- Need: ⨅ x, x ∈ succ η ⟹ Ord x
    -- x ∈ succ η ↔ x = η ∨ x ∈ η
    have H_all_ord : Γ ≤ ⨅ x, x ∈ᴮ succ η ⟹ Ord x := by
      apply le_iInf; intro x; rw [← deduction]
      -- goal: Γ ⊓ x ∈ succ η ≤ Ord x
      have hx : Γ ⊓ x ∈ᴮ succ η ≤ x =ᴮ η ⊔ x ∈ᴮ η := by
        have h : x ∈ᴮ succ η = x =ᴮ η ⊔ x ∈ᴮ η := by unfold succ; exact mem_insert1
        rw [h]; exact inf_le_right
      -- Case x = η: Ord η
      have hx_eq : (x =ᴮ η) ⊓ (Γ ⊓ x ∈ᴮ succ η) ≤ Ord x :=
        bv_rw'' (ϕ := fun v => Ord v) (bv_symm inf_le_left)
          (inf_le_right.trans (inf_le_left.trans H_Ord)) B_ext_Ord
      -- Case x ∈ η: Ord x (by Ord_of_mem_Ord)
      have hx_mem : (x ∈ᴮ η) ⊓ (Γ ⊓ x ∈ᴮ succ η) ≤ Ord x :=
        Ord_of_mem_Ord inf_le_left (inf_le_right.trans (inf_le_left.trans H_Ord))
      exact le_trans (le_inf hx le_rfl) (bv_or_elim_left hx_eq hx_mem)
    -- Now use epsilon_trichotomy_of_sub_Ord
    have htri := epsilon_trichotomy_of_sub_Ord (succ η) H_all_ord
    -- htri: Γ ≤ ⨅ y, y ∈ succ η ⟹ ⨅ z, z ∈ succ η ⟹ (y=z ⊔ y∈z ⊔ z∈y)
    -- Unfold epsilon_trichotomy to match
    unfold epsilon_trichotomy
    apply le_iInf; intro y; rw [← deduction]
    apply le_iInf; intro z; rw [← deduction]
    -- ctx = Γ ⊓ y ∈ succ η ⊓ z ∈ succ η
    have hy_mem : Γ ⊓ y ∈ᴮ succ η ⊓ z ∈ᴮ succ η ≤ y ∈ᴮ succ η := inf_le_left.trans inf_le_right
    have hz_mem : Γ ⊓ y ∈ᴮ succ η ⊓ z ∈ᴮ succ η ≤ z ∈ᴮ succ η := inf_le_right
    have htri_y := le_trans (le_inf (inf_le_left.trans (inf_le_left.trans (htri.trans (iInf_le _ y)))) hy_mem) bv_imp_elim
    exact le_trans (le_inf (htri_y.trans (iInf_le _ z)) hz_mem) bv_imp_elim
  · -- epsilon_well_founded: directly from regularity
    rw [epsilon_well_founded]
    apply le_iInf; intro x; rw [← deduction, ← deduction]
    exact bSet_axiom_of_regularity x inf_le_right
  · -- is_transitive (succ η): for z ∈ succ η, z ⊆ succ η
    unfold is_transitive
    apply le_iInf; intro z; rw [← deduction]
    have hz : Γ ⊓ z ∈ᴮ succ η ≤ z =ᴮ η ⊔ z ∈ᴮ η := by
      have h : z ∈ᴮ succ η = z =ᴮ η ⊔ z ∈ᴮ η := by unfold succ; exact mem_insert1
      rw [h]; exact inf_le_right
    have h1 : (z =ᴮ η) ⊓ (Γ ⊓ z ∈ᴮ succ η) ≤ z ⊆ᴮ succ η :=
      bv_rw'' (ϕ := fun v => v ⊆ᴮ succ η) (bv_symm inf_le_left)
        (inf_le_right.trans subset_succ) B_ext_subset_left
    have h2 : (z ∈ᴮ η) ⊓ (Γ ⊓ z ∈ᴮ succ η) ≤ z ⊆ᴮ succ η :=
      subset_trans' (subset_of_mem_Ord inf_le_left (inf_le_right.trans (inf_le_left.trans H_Ord)))
                    (inf_le_right.trans subset_succ)
    exact le_trans (le_inf hz le_rfl) (bv_or_elim_left h1 h2)

-- src/bvm_extras2.lean:563
lemma Ord.succ_le_of_lt {η ρ : bSet 𝔹} {Γ : 𝔹} (H_Ord' : Γ ≤ Ord ρ) (H_lt : Γ ≤ η ∈ᴮ ρ) :
    Γ ≤ succ η ⊆ᴮ ρ := by
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  set ctx := Γ ⊓ w ∈ᴮ succ η
  have hw : ctx ≤ w ∈ᴮ succ η := inf_le_right
  rw [show w ∈ᴮ succ η = w =ᴮ η ⊔ w ∈ᴮ η from mem_insert1] at hw
  have h_eta_mem : ctx ≤ η ∈ᴮ ρ := inf_le_left.trans H_lt
  have h_rho_trans : ctx ≤ is_transitive ρ := inf_le_left.trans (H_Ord'.trans inf_le_right)
  have h_eta_sub : ctx ≤ η ⊆ᴮ ρ :=
    le_trans (le_inf (h_rho_trans.trans (iInf_le _ η)) h_eta_mem) bv_imp_elim
  -- case 1: w = η → w ∈ ρ
  have hcase1 : ctx ⊓ (w =ᴮ η) ≤ w ∈ᴮ ρ := by
    have h1a : ctx ⊓ (w =ᴮ η) ≤ w =ᴮ η := inf_le_right
    have h1b : ctx ⊓ (w =ᴮ η) ≤ η ∈ᴮ ρ := inf_le_left.trans h_eta_mem
    exact bv_rw'' (bv_symm h1a) h1b B_ext_mem_left
  -- case 2: w ∈ η → w ∈ ρ (η ⊆ ρ)
  have hcase2 : ctx ⊓ (w ∈ᴮ η) ≤ w ∈ᴮ ρ := by
    rw [subset_unfold'] at h_eta_sub
    exact le_trans (le_inf (inf_le_left.trans (h_eta_sub.trans (iInf_le _ w))) inf_le_right)
      bv_imp_elim
  -- combine
  calc ctx ≤ (w =ᴮ η ⊔ w ∈ᴮ η) ⊓ ctx := le_inf hw le_rfl
       _ = ctx ⊓ (w =ᴮ η) ⊔ ctx ⊓ (w ∈ᴮ η) := by rw [inf_comm, inf_sup_left]
       _ ≤ w ∈ᴮ ρ := sup_le hcase1 hcase2
-- src/bvm_extras2.lean:572
lemma omega_least_is_limit {Γ : 𝔹} :
    Γ ≤ ⨅ η, Ord η ⟹ ((is_limit η) ⟹ omega ⊆ᴮ η) := by
  apply le_iInf; intro η; rw [← deduction, ← deduction]
  -- ctx = Γ ⊓ Ord η ⊓ is_limit η
  -- Goal: ctx ≤ omega ⊆ᴮ η
  -- omega ⊆ η unfolds via subset_unfold to ⨅ j : ULift ℕ, ⊤ ⟹ of_nat j.down ∈ η
  rw [subset_unfold]
  apply le_iInf; intro j
  simp only [omega_bval, omega_func, top_imp]
  -- Goal: Γ ⊓ Ord η ⊓ is_limit η ≤ of_nat j.down ∈ᴮ η
  -- Prove by induction on j.down
  set ctx := Γ ⊓ Ord η ⊓ is_limit η
  have H_η : ctx ≤ Ord η := inf_le_left.trans inf_le_right
  have H_limit : ctx ≤ is_limit η := inf_le_right
  have H_zero : ctx ≤ (∅ : bSet 𝔹) ∈ᴮ η := H_limit.trans inf_le_left
  have H_succ : ctx ≤ ⨅ x, x ∈ᴮ η ⟹ ⨆ y, y ∈ᴮ η ⊓ x ∈ᴮ y := H_limit.trans inf_le_right
  -- Induction on j.down
  induction j.down with
  | zero =>
    -- of_nat 0 = 0 = ∅ ∈ η
    apply bv_rw' (H := zero_eq_empty) (H_new := H_zero) (h_congr := B_ext_mem_left)
  | succ n ih =>
    -- of_nat (n+1) = succ (of_nat n) ∈ η
    rw [check_succ_eq_succ_check]
    -- ih : ctx ≤ of_nat n ∈ᴮ η
    -- H_succ applied to of_nat n gives ⨆ y, y ∈ η ⊓ of_nat n ∈ y
    have h_spec : ctx ≤ ⨆ y, y ∈ᴮ η ⊓ (of_nat n) ∈ᴮ y :=
      le_trans (le_inf (H_succ.trans (iInf_le _ (of_nat n))) ih) bv_imp_elim
    -- Get y with y ∈ η ∧ of_nat n ∈ y
    obtain ⟨y, Hy⟩ := exists_convert h_spec
      (B_ext_inf B_ext_mem_left B_ext_mem_right)
    have Hy_η : ctx ≤ y ∈ᴮ η := Hy.trans inf_le_left
    have Hn_y : ctx ≤ (of_nat n) ∈ᴮ y := Hy.trans inf_le_right
    -- y ∈ η means Ord y (by Ord_of_mem_Ord)
    have Hy_ord : ctx ≤ Ord y := Ord_of_mem_Ord Hy_η H_η
    -- We need succ (of_nat n) ∈ η
    -- of_nat n ∈ y and Ord η, Ord y means either succ (of_nat n) ⊆ y or y ∈ succ (of_nat n)
    -- Use Ord.succ_le_of_lt: of_nat n ∈ y → succ (of_nat n) ⊆ y
    have h_sub : ctx ≤ succ (of_nat n) ⊆ᴮ y :=
      Ord.succ_le_of_lt Hy_ord Hn_y
    -- From Ord.le_iff_lt_or_eq: succ (of_nat n) ⊆ y → succ (of_nat n) ∈ y ∨ succ (of_nat n) = y
    have h_lor : ctx ≤ succ (of_nat n) ∈ᴮ y ⊔ succ (of_nat n) =ᴮ y :=
      (Ord.le_iff_lt_or_eq (Ord_succ Ord_of_nat) Hy_ord).mp h_sub
    -- Case succ (of_nat n) ∈ y: then succ (of_nat n) ∈ η by mem_of_mem_Ord
    have hcase1 : (succ (of_nat n) ∈ᴮ y) ⊓ ctx ≤ succ (of_nat n) ∈ᴮ η :=
      mem_of_mem_Ord inf_le_left (inf_le_right.trans Hy_η) (inf_le_right.trans H_η)
    -- Case succ (of_nat n) = y: then succ (of_nat n) ∈ η (since y ∈ η)
    have hcase2 : (succ (of_nat n) =ᴮ y) ⊓ ctx ≤ succ (of_nat n) ∈ᴮ η :=
      bv_rw'' (ϕ := fun v => v ∈ᴮ η) (bv_symm inf_le_left) (inf_le_right.trans Hy_η) B_ext_mem_left
    exact le_trans (le_inf h_lor le_rfl) (bv_or_elim_left hcase1 hcase2)

end bSet

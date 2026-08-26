/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/forcing_CH.lean (645 lines) — Task 21

import ErdosProblems.Erdos501.Flypitch4.Collapse
import ErdosProblems.Erdos501.Flypitch4.AlephOne

set_option relaxedAutoImplicit true

open scoped Flypitch
open Lattice

universe u

open Set TopologicalSpace Cardinal

-- Local notation for Boolean implication / biimplication
local infix:65 " ⟹ " => Lattice.imp
local infix:50 " ⇔ " => Lattice.biimp
-- ≺ means "strictly smaller" (negation of larger_than via complement)
local infix:75 " ≺ " => (fun x y => (bSet.larger_than x y)ᶜ)
-- ≼ means "injects into"
local infix:75 " ≼ " => (fun x y => bSet.injects_into x y)

-- ℵ₁ as a pSet
noncomputable abbrev pSet_aleph1 : PSet.{u} := PSet.card_ex (Cardinal.aleph 1)

-- local ω shorthand
local notation "ω" => (bSet.omega)

attribute [local instance] Classical.propDecidable

-- ============================================================
-- namespace bSet
-- ============================================================

namespace bSet

-- ============================================================
-- section aleph_one (src lines 25-42)
-- ============================================================

section aleph_one

variable {𝔹 : Type*} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:31
noncomputable def aleph_one : bSet 𝔹 := a1

-- src/forcing_CH.lean:33
lemma aleph_one_satisfies_spec {Γ : 𝔹} :
    Γ ≤ aleph_one_Ord_spec (aleph_one (𝔹 := 𝔹)) :=
  a1_spec

-- src/forcing_CH.lean:36
lemma aleph_one_check_sub_aleph_one {Γ : 𝔹} :
    Γ ≤ (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) ⊆ᴮ aleph_one :=
  aleph_one_check_sub_aleph_one_aux a1_Ord a1_spec

-- src/forcing_CH.lean:39
lemma aleph_one_le_of_omega_lt {Γ : 𝔹} :
    Γ ≤ le_of_omega_lt (aleph_one (𝔹 := 𝔹)) :=
  a1_le_of_omega_lt

end aleph_one

-- ============================================================
-- section lemmas (src lines 44-353)
-- ============================================================

section lemmas

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:51-53
/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing'. -/
lemma check_forall (x : PSet.{u}) (ϕ : bSet 𝔹 → 𝔹) {b : 𝔹} :
    (∀ (y : x.Type), b ≤ ϕ (check (x.Func y))) →
    (b ≤ (⨅ (y : x.Type), ϕ (check (x.Func y)))) :=
  fun H => le_iInf H

-- src/forcing_CH.lean:55-62
lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹}
    (H : Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹)ᶜ) :
    Γ ≤ (check pSet_aleph1 : bSet 𝔹) =ᴮ (aleph_one (𝔹 := 𝔹)) := by
  -- Port from src/forcing_CH.lean:55-62
  refine subset_ext aleph_one_check_sub_aleph_one ?_
  have hspec := @aleph_one_satisfies_spec 𝔹 _ Γ
  unfold aleph_one_Ord_spec at hspec
  have hspec_rr : Γ ≤ ⨅ y, Ord y ⟹ ((injects_into y bSet.omega)ᶜ ⟹ a1 ⊆ᴮ y) :=
    le_trans hspec (le_trans inf_le_right inf_le_right)
  have happ : Γ ≤ Ord (check pSet_aleph1) ⟹ ((injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹
      a1 ⊆ᴮ check pSet_aleph1) :=
    le_trans hspec_rr (iInf_le _ _)
  have hOrd : Γ ≤ Ord (check pSet_aleph1) := Ord_card_ex (Cardinal.aleph 1)
  have hnotinj : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ := by
    rw [← imp_bot, ← deduction]
    apply bv_absurd (larger_than bSet.omega (check pSet_aleph1))
    · apply larger_than_of_surjects_onto
      exact surjects_onto_of_injects_into' inf_le_right aleph_one_check_exists_mem
    · exact le_trans inf_le_left H
  have step1 : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹ a1 ⊆ᴮ check pSet_aleph1 :=
    le_trans (le_inf happ hOrd) bv_imp_elim
  exact le_trans (le_inf step1 hnotinj) bv_imp_elim

-- src/forcing_CH.lean:64-77
theorem CH_true_aux
    (H_aleph_one : ∀ {Γ : 𝔹}, Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹))
    (H_not_lt    : ∀ {Γ : 𝔹}, Γ ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ)
    : ∀ {Γ : 𝔹}, Γ ≤ CH := by
  -- Port from src/forcing_CH.lean:64-77
  intro Γ
  -- Goal: Γ ≤ CH
  -- CH = (⨆ x, Ord x ⊓ ⨆ y, (larger_than ω x)ᶜ ⊓ (larger_than x y)ᶜ ⊓ injects_into y (𝒫ω))ᶜ
  -- Proof: show the inner iSup ≤ ⊥, i.e., for any x, y: absurd from H_aleph_one and H_not_lt
  unfold CH
  rw [← imp_bot, ← deduction]
  -- Goal after deduction: Γ ⊓ (⨆ x, Ord x ⊓ ⨆ y, ...) ≤ ⊥
  rw [inf_iSup_eq']
  apply iSup_le; intro x
  simp_rw [inf_iSup_eq']
  apply iSup_le; intro y
  -- Context: Γ ⊓ (Ord x ⊓ ((larger_than ω x)ᶜ ⊓ (larger_than x y)ᶜ ⊓ injects_into y (𝒫ω))) ≤ ⊥
  set ctx := Γ ⊓ (Ord x ⊓ ((larger_than bSet.omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
               injects_into y (bv_powerset bSet.omega)))
  have hOrd : ctx ≤ Ord x :=
    inf_le_right.trans inf_le_left
  have hLtX : ctx ≤ (larger_than bSet.omega x)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hLtY : ctx ≤ (larger_than x y)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hInj : ctx ≤ injects_into y (bv_powerset bSet.omega) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  -- From H_aleph_one: check ℵ₁ ≼ x
  -- le_of_omega_lt = ⨅ z, Ord z ⟹ ((larger_than ω z)ᶜ ⟹ injects_into (check ℵ₁) z)
  have hInj_a1_x : ctx ≤ injects_into (check pSet_aleph1) x :=
    -- H_aleph_one : ctx ≤ ⨅ z, Ord z ⟹ ((larger_than ω z)ᶜ ⟹ injects_into (check ℵ₁) z)
    -- Instantiate at z = x, then apply modus ponens twice
    le_trans (le_inf
      (le_trans (le_inf
        (H_aleph_one.trans (iInf_le _ x))
        hOrd)
        bv_imp_elim)
      hLtX)
      bv_imp_elim
  -- check ℵ₁ ≼ x and (larger_than x y)ᶜ → (larger_than (check ℵ₁) y)ᶜ
  have hLt_a1_y : ctx ≤ (larger_than (check pSet_aleph1) y)ᶜ :=
    bSet_lt_of_le_of_lt hInj_a1_x hLtY
  -- (larger_than (check ℵ₁) y)ᶜ and y ≼ 𝒫ω → (larger_than (check ℵ₁) (𝒫ω))ᶜ
  have hLt_a1_cont : ctx ≤ (larger_than (check pSet_aleph1) (bv_powerset bSet.omega))ᶜ :=
    bSet_lt_of_lt_of_le hLt_a1_y hInj
  -- H_not_lt gives larger_than (check ℵ₁) (𝒫ω)
  have hPos : ctx ≤ larger_than (check pSet_aleph1) (bv_powerset bSet.omega) := by
    have h : ctx ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ := H_not_lt
    simp only [compl_compl] at h
    exact h
  exact bv_absurd _ hPos hLt_a1_cont

-- src/forcing_CH.lean:79-81
def rel_of_array (x y : bSet 𝔹) (af : x.type → y.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun pr : (prod x y).type => af pr.1 pr.2)

-- src/forcing_CH.lean:82-102
lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_wide : ∀ j, (⨆ i, af i j) = ⊤) {Γ}
    : Γ ≤ (is_surj x y (rel_of_array x y af)) := by
  -- is_surj x y f = ⨅ v, v ∈ y ⟹ (⨆ w, w ∈ x ⊓ pair w v ∈ f)
  apply le_iInf; intro v
  rw [← deduction]
  -- Goal: Γ ⊓ v ∈ᴮ y ≤ ⨆ w, w ∈ᴮ x ⊓ pair w v ∈ᴮ rel_of_array x y af
  -- Use bounded_exists to express target as ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  rw [← @bounded_exists 𝔹 _ x (fun w => pair w v ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_pair_mem_left)]
  -- Unfold v ∈ y, distribute
  rw [mem_unfold, inf_iSup_eq']
  apply iSup_le; intro j₀
  -- ctx = Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀)
  -- Goal: ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  -- Key: first show ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  -- Then use bv_rw' with v =ᴮ y.func j₀ to replace y.func j₀ with v
  -- Step 1: show ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  have step1 : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤
      ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ᴮ rel_of_array x y af := by
    apply le_trans le_top
    rw [← H_wide j₀]
    apply iSup_le; intro i₀
    apply le_iSup_of_le i₀
    refine le_inf ?_ ?_
    · rw [H_bval₁]; exact le_top
    · -- pair (x.func i₀) (y.func j₀) ∈ rel_of_array ≥ af i₀ j₀
      unfold rel_of_array
      rw [mem_unfold]
      simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
      apply le_iSup_of_le (i₀, j₀)
      simp [bv_eq_refl]
  -- Step 2: use bv_rw' with v =ᴮ y.func j₀ to convert
  have heq : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤ v =ᴮ y.func j₀ :=
    inf_le_right.trans inf_le_right
  -- Use bv_rw' with v =ᴮ y.func j₀ to get ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  -- from step1: ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  exact @bv_rw' 𝔹 _ v (y.func j₀) _ heq
    (ϕ := fun z => ⨆ i, x.bval i ⊓ pair (x.func i) z ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_iSup (h := fun i => B_ext_inf B_ext_const B_ext_pair_mem_right))
    (H_new := step1)

-- src/forcing_CH.lean:104-113
lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_left : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    : Γ ≤ w₁ ∈ᴮ x := by
  -- rel_of_array x y af = set_of_indicator (fun pr => af pr.1 pr.2) on prod x y
  -- pair w₁ w₂ ∈ rel_of_array x y af = ⨆ pr, af pr.1 pr.2 ⊓ pair w₁ w₂ =ᴮ pair (x.func pr.1) (y.func pr.2)
  unfold rel_of_array at H_mem_left
  rw [mem_unfold] at H_mem_left
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_left
  -- H_mem_left : Γ ≤ ⨆ pr, af pr.1 pr.2 ⊓ pair w₁ w₂ =ᴮ pair (x.func pr.1) (y.func pr.2)
  -- Goal: Γ ≤ w₁ ∈ x = ⨆ i, x.bval i ⊓ w₁ =ᴮ x.func i
  rw [mem_unfold]
  apply H_mem_left.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le i
  refine le_inf ?_ ?_
  · rw [H_bval₁]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_left

-- src/forcing_CH.lean:115-124
lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    : Γ ≤ w₂ ∈ᴮ y := by
  unfold rel_of_array at H_mem_right
  rw [mem_unfold] at H_mem_right
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_right
  rw [mem_unfold]
  apply H_mem_right.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le j
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_right

-- src/forcing_CH.lean:128-169
lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ (is_func (rel_of_array x y af)) := by
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]
  -- Goal: Γ ⊓ (pair w₁ v₁ ∈ rel ⊓ pair w₂ v₂ ∈ rel) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Unfold the membership in rel_of_array
  unfold rel_of_array
  simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func, prod_func] at *
  -- H_mem₁: Γ ⊓ (⨆ pr₁, af pr₁.1 pr₁.2 ⊓ pair w₁ v₁ =ᴮ pair (x.func pr₁.1) (y.func pr₁.2)) ⊓
  --        (⨆ pr₂, af pr₂.1 pr₂.2 ⊓ pair w₂ v₂ =ᴮ pair (x.func pr₂.1) (y.func pr₂.2)) ⊓
  --        (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Distribute the iSup through the meet
  -- Goal: Γ ⊓ (⨆ p₁ : x.type × y.type, ...) ⊓ (⨆ p₂, ...) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  simp_rw [iSup_inf_eq', inf_iSup_eq', iSup_inf_eq']
  apply iSup_le; intro p₁
  obtain ⟨i₁, j₁⟩ := p₁
  apply iSup_le; intro p₂
  obtain ⟨i₂, j₂⟩ := p₂
  simp only []
  -- Context structure (from simp_rw of iSup_inf_eq', inf_iSup_eq'):
  -- Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
  --      (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Extract the pair equalities
  have hpair₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hpair₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have haf₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₁ j₁ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have haf₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₂ j₂ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have heq_w : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              w₁ =ᴮ w₂ := inf_le_right
  -- Get component equalities from pair equalities
  have hw₁ := hpair₁.trans (eq_of_eq_pair_left (x := w₁) (y := v₁))
  have hv₁ := hpair₁.trans (eq_of_eq_pair_right (x := w₁) (y := v₁))
  have hw₂ := hpair₂.trans (eq_of_eq_pair_left (x := w₂) (y := v₂))
  have hv₂ := hpair₂.trans (eq_of_eq_pair_right (x := w₂) (y := v₂))
  -- x.func i₁ =ᴮ x.func i₂ from transitivity
  have hxi := bv_trans (bv_symm hw₁) (bv_trans heq_w hw₂)
  -- Case analysis on j₁ = j₂
  by_cases hjj : j₁ = j₂
  · -- j₁ = j₂: v₁ =ᴮ y.func j₁ =ᴮ v₂ since y.func j₁ = y.func j₂ and v₂ =ᴮ y.func j₂
    -- Use transitivity: ctx ≤ v₁ =ᴮ y.func j₁ and ctx ≤ y.func j₁ =ᴮ v₂
    -- y.func j₁ =ᴮ v₂ = y.func j₂ =ᴮ v₂ (since j₁ = j₂)
    -- but we can't rewrite because it changes ctx too
    -- Instead: the proof is ctx ≤ v₁ =ᴮ v₂ = (v₁ =ᴮ y.func j₁) ⊓ (y.func j₁ =ᴮ v₂) via bv_trans
    -- y.func j₁ =ᴮ v₂: since j₁ = j₂, v₂ =ᴮ y.func j₁ from hv₂ + hjj
    -- bv_symm hv₂ : ctx ≤ y.func j₂ =ᴮ v₂
    -- show ctx ≤ y.func j₁ =ᴮ v₂ using convert or by rewriting at goal level:
    apply bv_trans hv₁
    -- Goal: ctx ≤ y.func j₁ =ᴮ v₂
    -- hv₂ : ctx ≤ v₂ =ᴮ y.func j₂ and j₁ = j₂
    -- so y.func j₁ =ᴮ v₂ = y.func j₂ =ᴮ v₂ ... same problem
    -- Use convert to handle the j₁ ↔ j₂ discrepancy
    convert bv_symm hv₂ using 2
    exact congrArg y.func hjj
  · -- j₁ ≠ j₂: must get contradiction
    -- Case analysis on i₁ = i₂
    by_cases hii : i₁ = i₂
    · -- i₁ = i₂: by H_anti, af i₁ j₁ ⊓ af i₁ j₂ ≤ ⊥
      -- We have haf₁ : ctx ≤ af i₁ j₁ and haf₂ : ctx ≤ af i₂ j₂ = af i₁ j₂ (since i₁ = i₂)
      have haf₂_rw : af i₂ j₂ = af i₁ j₂ := by rw [hii]
      have : af i₁ j₁ ⊓ af i₂ j₂ ≤ ⊥ := by rw [haf₂_rw]; exact H_anti i₁ j₁ j₂ hjj
      exact bv_exfalso (le_trans (le_inf haf₁ haf₂) this)
    · -- i₁ ≠ i₂: H_inj says ⊥ < x.func i₁ =ᴮ x.func i₂ → i₁ = i₂
      -- So ¬ (⊥ < x.func i₁ =ᴮ x.func i₂), i.e., x.func i₁ =ᴮ x.func i₂ ≤ ⊥
      have hbot : x.func i₁ =ᴮ x.func i₂ ≤ ⊥ := by
        rw [le_bot_iff]
        by_contra h
        exact hii (H_inj i₁ i₂ (bot_lt_iff_ne_bot.mpr h))
      exact bv_exfalso (hxi.trans hbot)

-- src/forcing_CH.lean:171-191
lemma rel_of_array_is_func' (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_tall : ∀ i, (⨆ j, af i j) = ⊤)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ is_func' x y (rel_of_array x y af) := by
  -- is_func' = is_func ⊓ is_total
  refine le_inf (rel_of_array_extensional x y af H_anti H_inj) ?_
  -- Now show is_total x y (rel_of_array x y af)
  rw [is_total_iff_is_total']
  -- is_total' x y f = ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ f
  apply le_iInf; intro i₀
  rw [← deduction]
  -- Goal: Γ ⊓ x.bval i₀ ≤ ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel_of_array x y af
  -- pair (x.func i₀) (y.func j₀) ∈ rel = ⨆ (i,j), af i j ⊓ pair (x.func i₀) (y.func j₀) =ᴮ pair (x.func i) (y.func j)
  -- This contains af i₀ j₀ ⊓ pair (x.func i₀) (y.func j₀) =ᴮ pair (x.func i₀) (y.func j₀) = af i₀ j₀
  -- So ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel
  --   ≥ ⨆ j₀, ⊤ ⊓ af i₀ j₀ = ⨆ j₀, af i₀ j₀ = H_tall i₀ = ⊤
  -- Goal: Γ ⊓ x.bval i₀ ≤ ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ᴮ rel_of_array x y af
  -- Use H_tall i₀ : ⨆ j₀, af i₀ j₀ = ⊤ to show ⨆ j₀, y.bval j₀ ⊓ pair... = ⊤
  -- bound: ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel ≥ ⨆ j₀, af i₀ j₀ = ⊤
  apply le_trans le_top
  rw [← H_tall i₀]
  apply iSup_le; intro j₀
  apply le_iSup_of_le j₀
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  · -- pair (x.func i₀) (y.func j₀) ∈ rel_of_array ≥ af i₀ j₀
    unfold rel_of_array
    rw [mem_unfold]
    simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
    apply le_iSup_of_le (i₀, j₀)
    simp [bv_eq_refl]

-- ============================================================
-- section function_reflect (src lines 193-350)
-- ============================================================

section function_reflect

-- Private auxiliary for function_reflect_of_omega_closed.
-- We prove existence of the full sequence at the Prop level using Nat.rec.
-- This avoids the Classical.choose definitional reduction issue.
private lemma fBrec_exists
    {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {D : Set 𝔹} {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_nonzero : ⊥ < Γ)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)
    -- The inductive invariant: we have a current Boolean B and can extend one more step
    : ∀ (n : ℕ) (Bprev : 𝔹), ⊥ < Bprev → Bprev ≤ is_func' bSet.omega (check y) g →
        ∃ (j : y.Type) (B : 𝔹), ⊥ < B ∧ B ≤ Bprev ∧
          B ≤ is_func' bSet.omega (check y) g ∧
          B ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func j)) ∈ᴮ g ∧
          B ∈ D := by
  intro n Bprev hpos hfunc
  have ae := AE PSet.omega y hfunc hpos (⟨n⟩ : PSet.omega.Type)
  obtain ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩ := ae
  exact ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩

open Flypitch in
-- src/forcing_CH.lean:216-348: function_reflect_of_omega_closed
-- Port of the complex recursive construction from Lean 3.
lemma function_reflect_of_omega_closed
    {D : Set 𝔹} (H_docs : Flypitch.DenseOmegaClosed D)
    {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_function : Γ ≤ is_function bSet.omega (check y) g)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)
    : ∃ (f : PSet.{u}) (Γ' : 𝔹), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      (Γ' ≤ check f =ᴮ g) ∧ PSet.is_func PSet.omega y f := by
  -- Port of src/forcing_CH.lean:216-348 (function_reflect_of_omega_closed).
  -- Strategy: build the sequence at the Prop level using nat-induction, avoiding
  -- Classical.choose definitional unfolding issues.
  -- Step 1: Prove by induction that for each n, given any Bprev with ⊥ < Bprev and
  -- Bprev ≤ is_func', there exists (j, B) with the required properties.
  -- This is just fBrec_exists.
  -- Step 2: Build a concrete sequence by simultaneously choosing (j_n, B_n) at each step
  -- using the inductive invariant Bprev = B_{n-1}.
  -- We carry the state (Bprev, ⊥<Bprev, Bprev≤func') inductively.
  -- Build the sequence of (j_n, B_n) pairs as a Type-valued function using Classical.choice.
  -- The inductive state: (B : 𝔹) × (⊥ < B) × (B ≤ is_func' ω ŷ g)
  -- At each step n, we have state_n = (B_n, pos_n, func_n)
  -- and (j_n, B_n) come from fBrec_exists n B_{n-1} pos_{n-1} func_{n-1}
  -- We build the sequence using Nat.rec at the level of (y.Type × 𝔹 × ...):
  -- state : ℕ → Σ' (j : y.Type) (B : 𝔹), ⊥ < B ∧ B ≤ is_func' bSet.omega (check y) g
  -- But we need the le-chain property: B_{n+1} ≤ B_n and B_0 ≤ Γ.
  -- The key insight: use a Prop-only induction to prove the existence of the entire chain,
  -- then apply Classical.choice once to get all the data.

  -- Prove: ∀ n, ∃ (fr : Fin (n+1) → y.Type) (fB : Fin (n+1) → 𝔹),
  --   ∀ k < n+1, ⊥ < fB k ∧ (k < n → fB (k+1) ≤ fB k) ∧ fB 0 ≤ Γ ∧
  --     fB k ≤ is_func' ω ŷ g ∧ fB k ≤ pair(...) ∈ g ∧ fB k ∈ D
  -- This is unwieldy. Instead, prove a simpler inductive fact:

  -- Key: prove by induction that ∃ sequences fr : ℕ → y.Type and fB : ℕ → 𝔹 such that
  -- (1) fB 0 ≤ Γ, (2) ∀ n, fB(n+1) ≤ fB n, (3) ∀ n, ⊥ < fB n,
  -- (4) ∀ n, fB n ≤ is_func' ω ŷ g, (5) ∀ n, fB n ≤ pair(ω_n)(y_{fr n}) ∈ g,
  -- (6) ∀ n, fB n ∈ D.
  -- This Prop-level statement is provable by building the sequence step-by-step.
  -- The sequence exists: choose using dependent choice (or Nat.rec on existence).
  -- Define the "good state" predicate for a Boolean B:
  -- GoodB B means ⊥ < B and B ≤ is_func' ω ŷ g.
  let GoodB : 𝔹 → Prop := fun B => ⊥ < B ∧ B ≤ is_func' bSet.omega (check y) g
  -- step_exists: given a GoodB, the step function produces the next (j, B) with GoodB.
  have step_exists : ∀ n (Bprev : 𝔹), GoodB Bprev →
      ∃ (j : y.Type) (B : 𝔹), GoodB B ∧ B ≤ Bprev ∧
        B ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func j)) ∈ᴮ g ∧ B ∈ D :=
    fun n Bprev ⟨hpos, hfunc⟩ => by
      obtain ⟨j, B, hpos', hle, hfunc', hpair, hmem⟩ :=
        fBrec_exists H_is_func' H_nonzero AE n Bprev hpos hfunc
      exact ⟨j, B, ⟨hpos', hfunc'⟩, hle, hpair, hmem⟩
  -- Build the sequence by Nat.rec at the TYPE level.
  -- State: {B : 𝔹 // GoodB B} (analogous to KonigLemma's {a : α // (Ici a).Infinite})
  -- The step function maps state_n to state_{n+1} (and produces j_n as a side effect).
  -- We carry both j and B:
  let mkState : ℕ → {j : y.Type // True} × {B : 𝔹 // GoodB B} :=
    Nat.rec
      (-- Base: apply step_exists at n=0 with Bprev = Γ
        let h₀ := step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩
        ⟨⟨h₀.choose, trivial⟩, ⟨h₀.choose_spec.choose, h₀.choose_spec.choose_spec.1⟩⟩)
      (-- Inductive step: apply step_exists at n+1 with Bprev = prev state's B
        fun n prev =>
          let h := step_exists (n + 1) prev.2.1 prev.2.2
          ⟨⟨h.choose, trivial⟩, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩⟩)
  -- Extract sequences:
  let fr : ℕ → y.Type := fun n => (mkState n).1.1
  let fBᵦ : ℕ → 𝔹 := fun n => (mkState n).2.1
  -- GoodB property (pos and func') come directly from the subtype:
  have fBᵦ_pos : ∀ n, ⊥ < fBᵦ n := fun n => (mkState n).2.2.1
  have fBᵦ_func' : ∀ n, fBᵦ n ≤ is_func' bSet.omega (check y) g :=
    fun n => (mkState n).2.2.2
  -- Properties proved by induction (NOT definitional reduction).
  -- At step 0: the step_exists applied to Γ gives j₀, B₀ with all props.
  -- At step n+1: the step_exists applied to B_n gives j_{n+1}, B_{n+1} with all props.
  -- Key: we prove these by applying step_exists to (mkState n).2 at each step.
  --      This gives us the SAME j,B that mkState produces, via Classical.choose_spec.
  -- The trick: (mkState (n+1)).2.1 = (step_exists (n+1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose
  -- And Classical.choose_spec gives all the properties of this B.
  -- We use "unicity" of Classical.choose_spec: for a SPECIFIC Bprev, step_exists Bprev
  -- gives a SPECIFIC (j, B) via Classical.choose. The properties are provable by
  -- noting that (mkState (n+1)).2.1 IS that specific Classical.choose value.
  -- But we can't prove this by rfl (definitional equality issue).
  -- HOWEVER, we can prove by induction that all properties hold:
  have fBᵦ_le : ∀ n, fBᵦ (n + 1) ≤ fBᵦ n := by
    intro n
    -- fBᵦ (n+1) = (mkState (n+1)).2.1
    -- mkState (n+1) = step applied to mkState n
    -- In the step function, h = step_exists (n+1) (mkState n).2.1 (mkState n).2.2
    -- and (mkState (n+1)).2.1 = h.choose_spec.choose
    -- h.choose_spec.choose_spec.2.1 : h.choose_spec.choose ≤ (mkState n).2.1
    -- So: fBᵦ (n+1) ≤ fBᵦ n.
    -- The challenge: we need to relate mkState (n+1) to step applied to mkState n.
    -- By the succ equation of Nat.rec:
    --   mkState (n+1) = (fun k prev => ...) n (mkState n)
    --               = let h := step_exists (n+1) (mkState n).2.1 (mkState n).2.2;
    --                 ⟨⟨h.choose, trivial⟩, ⟨h.choose_spec.choose, ...⟩⟩
    -- So (mkState (n+1)).2.1 = h.choose_spec.choose where h is as above.
    -- And h.choose_spec.choose_spec.2.1 : h.choose_spec.choose ≤ (mkState n).2.1
    -- This requires Lean to reduce Nat.rec at succ, which it CAN do.
    -- Let's try:
    exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.1
  have fBᵦ0_le_Γ : fBᵦ 0 ≤ Γ := by
    -- mkState 0 uses step_exists 0 Γ ..., so fBᵦ 0 = that choose_spec.choose ≤ Γ
    exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.1
  have fBᵦ_pair : ∀ n, fBᵦ n ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr n))) ∈ᴮ g := by
    intro n
    cases n with
    | zero =>
      -- fBᵦ 0 and fr 0 come from step_exists 0 Γ ...
      exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.2.1
    | succ n =>
      -- fBᵦ (n+1) and fr (n+1) come from step_exists (n+1) (mkState n).2.1 ...
      exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.2.1
  have fBᵦ_mem : ∀ n, fBᵦ n ∈ D := by
    intro n
    cases n with
    | zero =>
      exact (step_exists 0 Γ ⟨H_nonzero, H_is_func'⟩).choose_spec.choose_spec.2.2.2
    | succ n =>
      exact (step_exists (n + 1) (mkState n).2.1 (mkState n).2.2).choose_spec.choose_spec.2.2.2
  -- Build f' from fr.
  let fr' : PSet.omega.Type → y.Type := fun k => fr k.down
  let f' : PSet.{u} :=
    PSet.function_mk.mk (x := PSet.omega) (fun (k : PSet.omega.Type) => y.Func (fr' k))
      (fun i j heqv => by
        have hij : i = j := PSet.omega_inj heqv
        subst hij; exact PSet.Equiv.refl _)
  have f'_is_func : PSet.is_func PSet.omega y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr' i))
  -- Γ' = ⨅ n, fBᵦ n.
  have Γ'_pos : ⊥ < ⨅ n, fBᵦ n :=
    nonzero_iInf_of_mem_DenseOmegaClosed H_docs fBᵦ_le fBᵦ_mem
  have Γ'_le_Γ : (⨅ n, fBᵦ n) ≤ Γ :=
    (iInf_le _ 0).trans fBᵦ0_le_Γ
  -- iInf_fBᵦ_pair: Γ' ≤ each pair in g
  have iInf_fBᵦ_pair : ∀ n, (⨅ m, fBᵦ m) ≤ pair (check (PSet.omega.Func ⟨n⟩)) (check (y.Func (fr' ⟨n⟩))) ∈ᴮ g :=
    fun n => (iInf_le _ n).trans (fBᵦ_pair n)
  -- pair (ω.Func i) (y.Func (fr' i)) ∈ check f' for each i:
  have f'_mem : ∀ (i : PSet.omega.Type),
      (⊤ : 𝔹) ≤ pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ (check f' : bSet 𝔹) := by
    intro i
    -- function_mk.mk_mem : pSet_pair (ω.Func i) (y.Func (fr' i)) ∈ f'
    have hmem : PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i)) ∈ f' :=
      PSet.function_mk.mk_mem
    -- check_mem gives: check (pSet_pair ...) ∈ check f' at Γ = ⊤
    have h : (⊤ : 𝔹) ≤ check (PSet.pSet_pair (PSet.omega.Func i) (y.Func (fr' i))) ∈ᴮ check f' :=
      check_mem hmem
    -- check_pset_pair gives: check (pSet_pair a b) =ᴮ pair (check a) (check b)
    exact subst_congr_mem_left' (check_pset_pair (Γ := (⊤ : 𝔹))) h
  -- Γ' ≤ check f' =ᴮ g via bSet.funext.
  -- Abbreviate Γ' for convenience
  -- (1) Γ' ≤ is_function (check PSet.omega) (check y) (check f')
  -- (2) Γ' ≤ is_function bSet.omega (check y) g
  -- (3) Γ' ≤ ⨅ p, p ∈ prod (check PSet.omega) (check y) ⟹ (p ∈ check f' ⇔ p ∈ g)
  have hΓ'_f'_is_function : (⨅ n, fBᵦ n) ≤ is_function (check PSet.omega) (check y) (check f') :=
    le_trans le_top (check_is_func f'_is_func)
  have hΓ'_g_is_function : (⨅ n, fBᵦ n) ≤ is_function bSet.omega (check y) g :=
    (iInf_le _ 0).trans (fBᵦ0_le_Γ.trans H_function)
  -- is_func' sub-facts for eq_of_is_func'_of_eq
  have hΓ'_f'_is_func' : (⨅ n, fBᵦ n) ≤ is_func' (check PSet.omega) (check y) (check f') :=
    hΓ'_f'_is_function.trans inf_le_left
  have hΓ'_g_is_func' : (⨅ n, fBᵦ n) ≤ is_func' bSet.omega (check y) g :=
    hΓ'_g_is_function.trans inf_le_left
  have Γ'_le_eq : (⨅ n, fBᵦ n) ≤ check f' =ᴮ g := by
    -- Use mem_ext directly (which is what funext uses internally):
    -- check f' =ᴮ g iff (⨅ z, z ∈ check f' ⟹ z ∈ g) ⊓ (⨅ z, z ∈ g ⟹ z ∈ check f')
    -- We go directly without funext to avoid the name collision with _root_.funext.
    -- We also use bv_eq_unfold' or mem_ext.
    apply mem_ext
    · -- ⊆ direction: ∀ z, z ∈ check f' ⟹ z ∈ g
      apply le_iInf; intro z; rw [← deduction]
      -- Goal: (⨅ n, fBᵦ n) ⊓ z ∈ check f' ≤ z ∈ g
      -- Unfold z ∈ check f' = ⨆ k, z =ᴮ check (f'.Func k)
      -- By check_is_func, check f' is a function ω → y, so z ∈ check f' gives z = pair (check (ω.Func i)) (check (y.Func (fr' i))) for some i.
      -- Then z ∈ g follows from iInf_fBᵦ_pair.
      -- Use the fact that check f' ⊆ prod (check ω) (check y) from is_function.
      -- More directly: from z ∈ check f', we extract the pair structure.
      -- z ∈ check f' = ⨆ k : f'.Type, z =ᴮ check (f'.Func k)
      -- f' = function_mk, f'.Type = PSet.omega.Type, f'.Func i = pSet_pair (ω.Func i) (y.Func (fr' i))
      -- So z ∈ check f' = ⨆ i : PSet.omega.Type, z =ᴮ check (pSet_pair (ω.Func i) (y.Func (fr' i)))
      --                  = ⨆ i : PSet.omega.Type, z =ᴮ pair (check (ω.Func i)) (check (y.Func (fr' i)))
      --                    (using check_pset_pair_eq)
      -- Distribute inf over iSup, then for each i, we have z =ᴮ pair ... and can substitute.
      have hz_in_f' := inf_le_right (a := ⨅ n, fBᵦ n) (b := z ∈ᴮ check f')
      rw [mem_unfold] at hz_in_f'
      -- hz_in_f' : ... ≤ ⨆ k, (check f').bval k ⊓ z =ᴮ (check f').func k
      -- Since check f' has bval = ⊤ (from check), this simplifies.
      -- (check f').func k = check (f'.Func k)
      -- f'.Func k = pSet_pair (ω.Func k.down) (y.Func (fr' k.down)) [by function_mk construction]
      -- But to avoid unfolding f', use f'_mem instead.
      -- Alternative: just use bSet.funext's subset_prod_of_is_function path.
      -- Actually the cleanest path: from z ∈ check f', extract (i, j) s.t. z =ᴮ pair (check (ω.Func i)) (check (y.Func j)) and j = fr' i.
      -- Then z ∈ g follows.
      -- Use the is_function structure: check f' ⊆ prod (check ω) (check y)
      -- So z ∈ check f' implies z ∈ prod (check ω) (check y) implies z = pair (check (ω.Func i)) (check (y.Func j)) for some i, j.
      -- Then use check f' functional + f'_mem to get j = fr' i, then iInf_fBᵦ_pair.
      -- Simplest: use (⨅ n, fBᵦ n) ≤ is_function check ω (check y) (check f') and
      --           is_function check ω (check y) g and bSet.funext.
      -- Let me use a different route: show (⨅ n, fBᵦ n) ≤ ⨅ z, z ∈ check f' ⟹ z ∈ g
      -- by going through the indexed representation.
      -- Since check f' ⊆ prod (check ω) (check y) (from is_function), z ∈ check f' implies
      -- z ∈ prod (check ω) (check y) = ⨆ ij, z =ᴮ pair (check (ω.Func ij.1)) (check (y.Func ij.2)) (bval ⊤).
      -- Distribute: ctx ⊓ z ∈ check f' ≤ ⨆ ij, z =ᴮ pair ...
      -- For each ij: ctx ⊓ z ∈ check f' ⊓ z =ᴮ pair (ω.Func i) (y.Func j) ≤ z ∈ g.
      --   - From check f' func'ness: z =ᴮ pair (ω.Func i) (y.Func j) ∈ check f'
      --     and pair (ω.Func i) (y.Func (fr' i)) ∈ check f' gives j = fr' i (equality in bv sense)
      --   - Then pair (ω.Func i) (y.Func (fr' i)) ∈ g from iInf_fBᵦ_pair
      --   - Substitute z =ᴮ pair ... and j = fr' i to get z ∈ g.
      -- This is getting complex. Let me use the subset + product approach.
      -- Key: (⨅ n, fBᵦ n) ⊓ z ∈ check f' ≤ z ∈ prod (check ω) (check y)
      have hz_in_prod : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ≤ z ∈ᴮ prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_f'_is_function)) inf_le_right
      -- z ∈ prod (check ω) (check y) = ⨆ ij, ⊤ ⊓ z =ᴮ pair (check (ω.Func ij.1)) (check (y.Func ij.2))
      -- So (⨅ n, fBᵦ n) ⊓ z ∈ check f' ≤ ⨆ ij, z =ᴮ pair (ω.Func ij.1) (y.Func ij.2)
      -- hz_in_prod : ... ≤ z ∈ prod (check ω) (check y)
      -- The prod has type PSet.omega.Type × y.Type, bval = ⊤, func = pair check check.
      -- Use the membership in prod to get the indexed form, then case-split.
      -- Since (prod (check ω) (check y)).type = PSet.omega.Type × y.Type (definitionally),
      -- z ∈ prod (check ω) (check y) = ⨆ ij, (prod ...).bval ij ⊓ z =ᴮ (prod ...).func ij
      --    = ⨆ ij, ⊤ ⊓ z =ᴮ pair (check (ω.Func ij.1)) (check (y.Func ij.2))
      -- Bound: ctx ≤ ⨆ ij, ctx ⊓ z =ᴮ pair ...
      -- This follows from: ctx ≤ ctx ⊓ z ∈ prod ... ≤ ctx ⊓ ⨆ ij, z =ᴮ pair ... = ⨆ ij, ctx ⊓ z =ᴮ pair ...
      -- where the prod membership unfolds.
      -- Direct proof using poset_yoneda-style case split:
      -- For each ij : (prod ...).type, ctx ⊓ (prod ...).bval ij ⊓ z =ᴮ (prod ...).func ij ≤ z ∈ g
      -- which after simplifying bval = ⊤ and func = pair ... becomes ctx ⊓ z =ᴮ pair ... ≤ z ∈ g.
      -- Use: ctx ≤ ⨆ ij : (prod ...).type, ctx ⊓ (prod ...).bval ij ⊓ z =ᴮ (prod ...).func ij
      -- which follows from: ctx ≤ ctx ⊓ z ∈ prod ... = ctx ⊓ ⨆ ij, bval ij ⊓ ... = ⨆ ij, ctx ⊓ ...
      rw [mem_unfold] at hz_in_prod
      -- hz_in_prod : ctx ≤ ⨆ (i : (prod ...).type), (prod ...).bval i ⊓ z =ᴮ (prod ...).func i
      -- ctx ≤ ctx ⊓ ⨆ i, ...
      have hctx_le : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ≤
          ⨆ (ij : (prod (check PSet.omega) (check y)).type),
          (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) := by
        rw [← inf_iSup_eq]
        apply le_inf
        · exact le_refl _
        · exact hz_in_prod
      -- For each ij : (prod (check ω) (check y)).type = PSet.omega.Type × y.Type,
      -- show: ctx ⊓ (prod ...).bval ij ⊓ z =ᴮ (prod ...).func ij ≤ z ∈ g
      -- Key sub-lemma: for each (i : PSet.omega.Type, j : y.Type),
      --   ctx ⊓ z =ᴮ pair (check (ω.Func i)) (check (y.Func j)) ≤ z ∈ g
      -- (which is what hctx_le gives after dropping bval = ⊤)
      -- Use show_step: for each ij, we have bval = ⊤ and func = pair check... check...,
      -- so context ⊓ (⊤ ⊓ z =ᴮ pair ...) ≤ z ∈ g, which reduces to ctx ⊓ z =ᴮ pair ... ≤ z ∈ g.
      -- The step-by-step proof for each ij:
      apply hctx_le.trans
      apply iSup_le; intro ij
      -- ij : PSet.omega.Type × y.Type (= (prod (check ω) (check y)).type)
      -- Simplify bval and func at ij = (ij.1, ij.2):
      have hstep : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ g := by
        -- Reduce to the simpler form using prod_check_bval, prod_func, check_func
        have hbval : (prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        -- Goal: ctx ⊓ z =ᴮ (prod (check ω) (check y)).func ij ≤ z ∈ g
        -- (prod ...).func ij = pair ((check ω).func ij.1) ((check y).func ij.2)
        --                     = pair (check (ω.Func (check_cast ij.1))) (check (y.Func (check_cast ij.2)))
        -- Cast to PSet.omega.Type:
        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        -- Key: (prod ...).func ij = pair (check (ω.Func i)) (check (y.Func j))
        have hfunc : (prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        -- Now: ctx ⊓ z =ᴮ pair (check (ω.Func i)) (check (y.Func j)) ≤ z ∈ g
        have hpair_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ check f')
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hf'_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have h_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_f'_is_func')
            bv_refl hpair_eq hf'_fri
        have hg_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have hg_j : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ check f' ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ g)
            (h_congr := B_ext_pair_mem_right) (H_new := hg_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ g)
          (h_congr := B_ext_mem_left) (H_new := hg_j)
      exact hstep
    · -- ⊇ direction: ∀ z, z ∈ g ⟹ z ∈ check f'
      apply le_iInf; intro z; rw [← deduction]
      -- Symmetric to the above, using g's functional nature.
      have hz_in_prod : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod (check PSet.omega) (check y) :=
        mem_of_mem_subset (le_trans inf_le_left (subset_prod_of_is_function hΓ'_g_is_function)) inf_le_right
      -- Rewrite only the RHS (z ∈ prod ...) to iSup form, NOT the LHS (z ∈ g)
      conv at hz_in_prod => rw [show z ∈ᴮ prod (check PSet.omega) (check y) =
          ⨆ (i : (prod (check PSet.omega) (check y)).type),
          (prod (check PSet.omega) (check y)).bval i ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func i
          from mem_unfold]
      -- ctx ≤ ⨆ ij, ctx ⊓ (bval ij ⊓ z =ᴮ func ij)
      -- Proof: ctx ≤ ⨆ ij, bval ij ⊓ z =ᴮ func ij (from hz_in_prod)
      -- So ctx ≤ ctx ⊓ ⨆ ij, bval ij ⊓ ...  ← by le_inf (le_refl) hz_in_prod
      -- = ⨆ ij, ctx ⊓ (bval ij ⊓ ...) ← by inf_iSup_eq
      -- Prove: ctx ≤ ⨆ ij, ctx ⊓ (bval ij ⊓ z =ᴮ func ij)
      -- Strategy: for any specific ij₀, if bval ij₀ ⊓ z =ᴮ func ij₀ is hit by hz_in_prod,
      -- then ctx ≤ ctx ⊓ (bval ij₀ ⊓ z =ᴮ func ij₀).
      -- But we can't extract a specific ij₀ from hz_in_prod.
      -- Proper way: ctx ≤ ctx ⊓ ⨆ ij, bval ij ⊓ z =ᴮ func ij (use le_inf)
      --           = ⨆ ij, ctx ⊓ (bval ij ⊓ z =ᴮ func ij) (by inf_iSup_eq)
      -- The le_inf approach keeps giving "Type mismatch" for `exact hz_in_prod`.
      -- Let's try without `apply le_inf` and directly use `inf_le_intro`:
      have hctx_le : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤
          ⨆ (ij : (prod (check PSet.omega) (check y)).type),
          (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) := by
        have heq : (⨆ (ij : (prod (check PSet.omega) (check y)).type),
              (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
              ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij)) =
              (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
              ⨆ (ij : (prod (check PSet.omega) (check y)).type),
              (prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij :=
          (inf_iSup_eq _ _).symm
        rw [heq]
        refine le_inf le_rfl ?_
        have : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ≤
            ⨆ (ij : (prod (check PSet.omega) (check y)).type),
            (prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij :=
          hz_in_prod
        exact this
      apply hctx_le.trans
      apply iSup_le; intro ij
      -- Reduce bval = ⊤ and func = pair check... check... for ij : PSet.omega.Type × y.Type
      have hstep : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
          ((prod (check PSet.omega) (check y)).bval ij ⊓ z =ᴮ (prod (check PSet.omega) (check y)).func ij) ≤
          z ∈ᴮ check f' := by
        have hbval : (prod (check PSet.omega) (check y)).bval ij = ⊤ := prod_check_bval
        rw [hbval, top_inf_eq]
        let i : PSet.omega.Type := check_cast ij.1
        let j : y.Type := check_cast ij.2
        have hfunc : (prod (check PSet.omega) (check y)).func ij =
            pair (check (PSet.omega.Func i)) (check (y.Func j)) := by
          simp only [prod_func, check_func]
          rfl
        rw [hfunc]
        have hpair_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ g :=
          bv_rw' (bv_symm inf_le_right) (ϕ := fun z => z ∈ᴮ g)
            (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans inf_le_right)
        have hg_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ g :=
          le_trans (inf_le_left.trans inf_le_left) (iInf_fBᵦ_pair i.down)
        have h_eq : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            check (y.Func j) =ᴮ check (y.Func (fr' i)) :=
          eq_of_is_func'_of_eq (le_trans (inf_le_left.trans inf_le_left) hΓ'_g_is_func')
            bv_refl hpair_eq hg_fri
        have hf'_fri : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func (fr' i))) ∈ᴮ check f' :=
          le_trans le_top (f'_mem i)
        have hf'_j : (⨅ n, fBᵦ n) ⊓ z ∈ᴮ g ⊓
            z =ᴮ pair (check (PSet.omega.Func i)) (check (y.Func j)) ≤
            pair (check (PSet.omega.Func i)) (check (y.Func j)) ∈ᴮ check f' :=
          bv_rw' h_eq (ϕ := fun z => pair (check (PSet.omega.Func i)) z ∈ᴮ check f')
            (h_congr := B_ext_pair_mem_right) (H_new := hf'_fri)
        exact bv_rw' inf_le_right (ϕ := fun z => z ∈ᴮ check f')
          (h_congr := B_ext_mem_left) (H_new := hf'_j)
      exact hstep
  exact ⟨f', ⨅ n, fBᵦ n, Γ'_pos, Γ'_le_Γ, Γ'_le_eq, f'_is_func⟩

end function_reflect

end lemmas

end bSet

-- ============================================================
-- namespace collapse_algebra (src lines 356-645)
-- ============================================================

namespace collapse_algebra

open bSet Flypitch

-- The collapse Boolean algebra for forcing CH.
noncomputable def 𝔹_collapse : Type u :=
  CollapseAlgebra (pSet_aleph1 : PSet.{u}).Type
    (PSet.powerset PSet.omega : PSet.{u}).Type

private instance : Nonempty (PSet.powerset PSet.omega : PSet.{u}).Type := by
  simp only [PSet.powerset, PSet.Type]; exact ⟨Set.univ⟩

private instance : Nonempty ((pSet_aleph1 : PSet.{u}).Type →
    (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  ⟨fun _ => Classical.arbitrary _⟩

noncomputable instance 𝔹_collapse_ncba :
    NontrivialCompleteBooleanAlgebra 𝔹_collapse :=
  collapseAlgebra_ncba (X := (pSet_aleph1 : PSet.{u}).Type)
    (Y := (PSet.powerset PSet.omega : PSet.{u}).Type)

-- Register the collapseSpace topology so RegularOpens lemmas work
local instance collapseSpaceInstFCH :
    TopologicalSpace ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  collapseSpace (pSet_aleph1 : PSet.{u}).Type (PSet.powerset PSet.omega : PSet.{u}).Type

-- ============================================================
-- Nonzero witness for dense omega-closed sets (src lines 377-388)
-- ============================================================

-- src/forcing_CH.lean:377-388
lemma nonzero_wit'' {𝓑 : Type*} [NontrivialCompleteBooleanAlgebra 𝓑] {D : Set 𝓑}
    (H_docs : DenseOmegaClosed D) {I : Type*} {s : I → 𝓑} {Γ : 𝓑}
    (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i, s i) :
    ∃ j : I, ∃ Γ' : 𝓑, ⊥ < Γ' ∧ Γ' ≤ s j ⊓ Γ ∧ Γ' ∈ D := by
  obtain ⟨j, Hj⟩ := nonzero_wit' H_nonzero H_le
  rcases H_docs.1 with ⟨_, H_dense₂⟩
  rcases H_dense₂ (s j ⊓ Γ) Hj with ⟨Γ', HΓ'₁, HΓ'₂⟩
  exact ⟨j, Γ', nonzero_of_mem_DenseOmegaClosed H_docs HΓ'₁, HΓ'₂, HΓ'₁⟩

-- ============================================================
-- AE_of_check_func_check (src lines 371-444)
-- ============================================================

-- src/forcing_CH.lean:390-411: AE for check functions in collapse algebra
lemma AE_of_check_func_check' (x y : PSet.{u})
    {f : bSet 𝔹_collapse} {Γ : 𝔹_collapse}
    (H : Γ ≤ is_func' (check x) (check y) f)
    (H_nonzero : ⊥ < Γ)
    (i : x.Type) :
    ∃ (j : y.Type) (Γ' : 𝔹_collapse), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      Γ' ≤ is_func' (check x) (check y) f ∧
      Γ' ≤ pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ f ∧
      Γ' ∈ Set.range
        (@collapseInclusion (pSet_aleph1 : PSet.{u}).Type
                           (PSet.powerset PSet.omega : PSet.{u}).Type) := by
  -- Step 1: From is_total, get ⨆ j, pair (x.Func i)̌ (y.Func (check_cast j))̌ ∈ f
  have Htot : Γ ≤ is_total (check x) (check y) f := is_total_of_is_func' H
  have hmem : Γ ≤ (check (x.Func i)) ∈ᴮ check x := by
    simp [check_bval_top]
  have htot_i_raw : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ f :=
    le_trans (le_inf (le_trans Htot (iInf_le _ (check (x.Func i)))) hmem) bv_imp_elim
  -- Convert to indexed form using bounded_exists
  rw [← @bounded_exists 𝔹_collapse _ (check y) (fun w => pair (check (x.Func i)) w ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at htot_i_raw
  simp only [check_bval_top, top_inf_eq] at htot_i_raw
  -- htot_i_raw : Γ ≤ ⨆ j₀, pair (check (x.Func i)) (check y).func j₀ ∈ f
  -- Step 2: Build H' : Γ ≤ ⨆ j₀, is_func' ⊓ pair... j₀ ∈ f (nonzero_wit'' adds ⊓ Γ automatically)
  have H' : Γ ≤ ⨆ (j₀ : (check y).type),
      is_func' (check x) (check y) f ⊓ pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := by
    calc Γ ≤ is_func' (check x) (check y) f ⊓
              ⨆ j₀, pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f :=
          le_inf H htot_i_raw
      _ = ⨆ j₀, is_func' (check x) (check y) f ⊓
              pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := inf_iSup_eq _ _
  obtain ⟨j₀, Γ', HΓ'_nonzero, HΓ'_le, HΓ'_mem⟩ := nonzero_wit''
    principalOpens_denseOmegaClosed H_nonzero H'
  -- HΓ'_le : Γ' ≤ (is_func' ⊓ pair (x.Func i)̌ (check y).func j₀ ∈ f) ⊓ Γ
  refine ⟨check_cast j₀, Γ', HΓ'_nonzero, HΓ'_le.trans inf_le_right,
    HΓ'_le.trans (inf_le_left.trans inf_le_left), ?_, HΓ'_mem⟩
  -- Γ' ≤ pair (check (x.Func i)) (check (y.Func (check_cast j₀))) ∈ f
  have h := HΓ'_le.trans (inf_le_left.trans inf_le_right)
  simp only [check_func] at h
  exact h

-- src/forcing_CH.lean:416-444
lemma check_functions_eq_functions (y : PSet.{u}) {Γ : 𝔹_collapse} :
    Γ ≤ check (PSet.functions PSet.omega y) =ᴮ functions bSet.omega (check y) := by
  -- Port of src/forcing_CH.lean:416-444.
  -- Strategy: use subset_ext with check_functions_subset_functions (one direction already proven)
  -- For the reverse direction, use a density argument:
  -- for each g in functions ω (check y), show g ∈ check(functions ω y) via function_reflect_of_omega_closed.
  refine subset_ext check_functions_subset_functions ?_
  -- Goal: Γ ≤ functions bSet.omega (check y) ⊆ᴮ check (PSet.functions PSet.omega y)
  rw [subset_unfold']
  apply le_iInf; intro g; rw [← deduction]
  -- Goal: Γ ⊓ g ∈ᴮ functions bSet.omega (check y) ≤ g ∈ᴮ check (PSet.functions PSet.omega y)
  set B := Γ ⊓ g ∈ᴮ functions bSet.omega (check y) with hB
  set A := g ∈ᴮ check (PSet.functions PSet.omega y) with hA
  -- Show B ≤ A by showing RelDense B.val A.val then applying p_p_eq_univ_of_rel_dense_of_open.
  have hB_open : IsOpen B.val := Flypitch.Regular.isOpen_of_isRegularOpen B.property
  have hA_reg : A.valᵖᵖ = A.val := Flypitch.Regular.isRegularOpen_eq_p_p A.property
  -- Prove RelDense B.val A.val
  have hRelDense : Flypitch.RelDense B.val A.val := by
    apply Flypitch.rel_dense_of_dense_in_basis B.val A.val collapseSpaceBasis_spec
    -- Goal: RelDenseInBasis B.val A.val collapseSpaceBasis_spec
    intro D HD hDB
    rcases HD with rfl | ⟨p, -, rfl⟩
    · -- D = ∅: (∅ ∩ B.val) = ∅ is not nonempty
      exact absurd hDB (by simp)
    · -- D = principalOpen p
      let P := collapseInclusion p
      have hP_val : P.val = CollapsePoset.principalOpen p := rfl
      -- (principalOpen p ∩ B.val).Nonempty ↔ (P ⊓ B).val.Nonempty
      have hPB_val : (CollapsePoset.principalOpen p ∩ B.val) = (P ⊓ B).val := by
        simp only [RegularOpens.inf_val, P, collapseInclusion]; rfl
      rw [hPB_val] at hDB
      -- P ⊓ B > ⊥ from nonemptiness
      have hPB_pos : ⊥ < P ⊓ B := RegularOpens.bot_lt_iff.mpr hDB
      -- P ⊓ B ≤ g ∈ functions bSet.omega (check y) ≤ is_function, is_func'
      have hPB_le_Bg : P ⊓ B ≤ g ∈ᴮ functions bSet.omega (check y) :=
        inf_le_right.trans inf_le_right
      have hPB_func : P ⊓ B ≤ is_function bSet.omega (check y) g :=
        mem_functions_iff.mp hPB_le_Bg
      have hPB_func' : P ⊓ B ≤ is_func' bSet.omega (check y) g :=
        is_func'_of_is_function hPB_func
      -- Apply function_reflect_of_omega_closed to get PSet function f
      obtain ⟨f, Γ', hΓ'_pos, hΓ'_le, hΓ'_eq, hf_func⟩ :=
        function_reflect_of_omega_closed
          principalOpens_denseOmegaClosed hPB_pos hPB_func' hPB_func
          (fun px py {f} {Γ'} hfunc hpos i => AE_of_check_func_check' px py hfunc hpos i)
      -- Get g ∈ check(functions ω y) at Γ'
      have hΓ'_le_A : Γ' ≤ A := by
        rw [hA]
        exact bv_rw' (bv_symm hΓ'_eq)
          (ϕ := fun z => z ∈ᴮ check (PSet.functions PSet.omega y))
          (h_congr := B_ext_mem_left)
          (H_new := check_mem ((PSet.mem_functions_iff f).mpr hf_func))
      -- Get witness h from ⊥ < Γ'
      obtain ⟨h, hh⟩ := RegularOpens.bot_lt_iff.mp hΓ'_pos
      -- h ∈ D ∩ B.val ∩ A.val where D = principalOpen p
      -- principalOpen p = P.val, so h ∈ P.val ∩ B.val ∩ A.val
      refine ⟨h, ?_, hΓ'_le_A hh⟩
      rw [Set.mem_inter_iff]
      exact ⟨hP_val ▸ (RegularOpens.le_iff_subset.mp (hΓ'_le.trans inf_le_left) hh),
             RegularOpens.le_iff_subset.mp (hΓ'_le.trans inf_le_right) hh⟩
  -- From RelDense B.val A.val + B.val open + A regular open, conclude B ≤ A
  -- Use p_p_eq_univ_of_rel_dense_of_open: B.val ∩ A.valᵖᵖ = B.val
  -- Then A.valᵖᵖ = A.val (A is regular open), so B.val ∩ A.val = B.val, i.e., B.val ⊆ A.val
  have h := Flypitch.RegularOpens.p_p_eq_univ_of_rel_dense_of_open hB_open hRelDense
  -- h : B.val ∩ A.valᵖᵖ = B.val
  rw [hA_reg] at h
  -- h : B.val ∩ A.val = B.val
  exact Set.inter_eq_left.mp h

-- ============================================================
-- π_af definitions (src lines 446-551)
-- ============================================================

-- The cylinder set function for the collapse algebra:
-- π_af η S = {g : ℵ₁.Type → 𝒫(ω).Type | g(η) = S}
noncomputable def π_af :
    (check pSet_aleph1 : bSet 𝔹_collapse).type →
    (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type → 𝔹_collapse :=
  fun η S =>
    let η' : (pSet_aleph1 : PSet.{u}).Type := check_cast η
    let S' : (PSet.powerset PSet.omega : PSet.{u}).Type := check_cast S
    ⟨{g : (pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type |
        g η' = S'},
     by
       haveI : TopologicalSpace
         ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
         collapseSpace _ _
       exact isRegular_setOf⟩

-- src/forcing_CH.lean:458-460
lemma aleph_one_type_uncountable :
    Cardinal.aleph 0 < # (pSet_aleph1 : PSet.{u}).Type := by
  simp [PSet.mk_type_mk_eq''']

-- src/forcing_CH.lean:464-485
lemma π_af_wide :
    ∀ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    (⨆ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type), π_af i j) = (⊤ : 𝔹_collapse) := by
  intro j
  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  rcases collapseSpaceBasis_spec.exists_subset_of_mem_open hg hU with ⟨B, HB_basis, HB_mem, HB_sub⟩
  rcases HB_basis with rfl | ⟨p, -, rfl⟩
  · exact absurd HB_mem (by simp)
  · -- p : CollapsePoset pSet_aleph1.Type PSet.omega.powerset.Type (Order.succ ℵ₀)
    -- Find η' ∉ PFun.Dom p.f using exists_mem_compl_of_mk_lt_mk
    -- p.Hc : # (PFun.Dom p.f) < Order.succ ℵ₀ = ℵ₁ = # pSet_aleph1.Type
    -- (universe unification: p's X = pSet_aleph1.Type at u_1 = u via rcases unification)
    obtain ⟨η', Hη'⟩ := exists_mem_compl_of_mk_lt_mk (PFun.Dom p.f) (by
      calc # (PFun.Dom p.f) < Order.succ (ℵ₀ : Cardinal) := p.Hc
        _ = ℵ₁ := Cardinal.succ_aleph0
        _ = # pSet_aleph1.Type := by
              simp [pSet_aleph1, PSet.mk_type_mk_eq'''])
    -- Build trivial extension mapping η' to check_cast j
    let h := CPFun.trivial_extension p.f (check_cast j)
    have Hh_open : h ∈ CollapsePoset.principalOpen p := trivialExtension_mem_principalOpen
    have Hh_val : h η' = check_cast j := CPFun.trivial_extension_neg (Set.mem_compl_iff _ _ |>.mp Hη')
    refine ⟨h, HB_sub Hh_open, ?_⟩
    simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]
    exact ⟨(π_af (check_cast_symm η') j).val,
      ⟨_, ⟨check_cast_symm η', rfl⟩, rfl⟩,
      by simp [π_af, Hh_val]⟩

-- src/forcing_CH.lean:487-501
lemma π_af_tall :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type),
    (⨆ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type), π_af i j) =
    (⊤ : 𝔹_collapse) := by
  -- π_af i j = {g | g (check_cast i) = check_cast j}
  -- For fixed i, ⋃ j, {g | g (check_cast i) = check_cast j}
  -- = {g | ∃ j, g (check_cast i) = check_cast j}
  -- Since check_cast is bijective, for any g: g (check_cast i) = check_cast (check_cast_symm (g (check_cast i)))
  -- So the union = Set.univ, hence dense, hence sSup = ⊤
  intro i
  -- For fixed i, ⋃ j, {g | g (check_cast i) = check_cast j} = Set.univ
  -- since for any g, g(check_cast i) = check_cast (check_cast_symm (g (check_cast i)))
  -- Hence the union is dense (= univ), so ⨆ j, π_af i j = ⊤
  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  -- g ∈ ⋃₀ (image (·.val) (range (π_af i)))
  simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]
  -- Witness: j = check_cast_symm (g (check_cast i)), then g (check_cast i) = check_cast j
  refine ⟨(π_af i (check_cast_symm (g (check_cast i)))).val,
    ⟨_, ⟨check_cast_symm (g (check_cast i)), rfl⟩, rfl⟩, ?_⟩
  -- Show g ∈ {h | h (check_cast i) = check_cast (check_cast_symm (g (check_cast i)))}
  simp [π_af]

-- src/forcing_CH.lean:503-505
lemma π_af_anti :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type)
      (j₁ j₂ : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ := by
  -- Port of src/forcing_CH.lean:503: {g | g η = S₁} ∩ {g | g η = S₂} = ∅ when S₁ ≠ S₂
  intro i j₁ j₂ hne
  -- π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ in 𝔹_collapse = CollapseAlgebra X Y = RegularOpens (X → Y)
  -- It suffices to show the underlying sets are disjoint
  -- (π_af i j₁).val ∩ (π_af i j₂).val = ∅
  rw [le_bot_iff]
  -- Goal: π_af i j₁ ⊓ π_af i j₂ = ⊥
  apply Subtype.ext
  -- Goal: (π_af i j₁ ⊓ π_af i j₂).val = (⊥ : 𝔹_collapse).val
  -- (π_af i j₁ ⊓ π_af i j₂).val = π_af i j₁ ∩ π_af i j₂ = {g | g η = S₁} ∩ {g | g η = S₂} = ∅
  simp only [RegularOpens.inf_val, RegularOpens.bot_val, π_af]
  apply Set.eq_empty_of_subset_empty
  intro g ⟨h₁, h₂⟩
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have heq : check_cast j₁ = check_cast j₂ := h₁.symm.trans h₂
  apply hne
  simp only [check_cast, cast_inj] at heq
  exact heq

-- src/forcing_CH.lean:507-523
lemma check_index_inj_of_pSet_index_inj {x : PSet.{u}}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂) :
    ∀ i₁ i₂ : (check x : bSet 𝔹_collapse).type,
    ⊥ < (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ → i₁ = i₂ := by
  -- Port of src/forcing_CH.lean:507-523
  intro i₁ i₂ H
  by_contra hne
  have hne' : check_cast i₁ ≠ check_cast i₂ := by
    intro h; apply hne; simp only [check_cast, cast_inj] at h; exact h
  have hnotequiv : ¬ PSet.Equiv (x.Func (check_cast i₁)) (x.Func (check_cast i₂)) :=
    fun h => hne' (H_inj (check_cast i₁) (check_cast i₂) h)
  have heq_bot : (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ = ⊥ := by
    simp only [check_func]; exact check_bv_eq_bot_of_not_equiv hnotequiv
  rw [heq_bot] at H; exact absurd H (lt_irrefl ⊥)

-- src/forcing_CH.lean:525-527
lemma aleph_one_inj :
    ∀ i₁ i₂ : (check pSet_aleph1 : bSet 𝔹_collapse).type,
    ⊥ < (check pSet_aleph1 : bSet 𝔹_collapse).func i₁ =ᴮ
        (check pSet_aleph1 : bSet 𝔹_collapse).func i₂ → i₁ = i₂ :=
  check_index_inj_of_pSet_index_inj (by
    -- pSet_aleph1 = ordinalMk (aleph 1).ord
    -- PSet.ordinalMk_inj: i ≠ j → ¬ Equiv (Func i) (Func j)
    -- We need: Equiv (Func i₁) (Func i₂) → i₁ = i₂
    intro i₁ i₂ H
    by_contra hne
    exact PSet.ordinalMk_inj (Cardinal.aleph 1).ord i₁ i₂ hne H)

-- src/forcing_CH.lean:529-530
noncomputable def π : bSet 𝔹_collapse :=
  rel_of_array (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π_af

-- src/forcing_CH.lean:532-537
lemma π_is_func {Γ : 𝔹_collapse} : Γ ≤ is_func π :=
  rel_of_array_extensional _ _ _ π_af_anti aleph_one_inj

-- src/forcing_CH.lean:539-545
lemma π_is_func' {Γ : 𝔹_collapse} :
    Γ ≤ is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_is_func' _ _ _
    (fun _ => check_bval_top _) π_af_tall π_af_anti aleph_one_inj

-- src/forcing_CH.lean:547
lemma π_is_functional {Γ : 𝔹_collapse} : Γ ≤ is_functional π :=
  is_functional_of_is_func _ π_is_func

-- src/forcing_CH.lean:549-550
lemma π_is_surj {Γ : 𝔹_collapse} :
    Γ ≤ is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_surj _ _ _
    (fun _ => check_bval_top _) (fun _ => check_bval_top _) π_af_wide

-- src/forcing_CH.lean:552
lemma π_spec {Γ : 𝔹_collapse} :
    Γ ≤ (is_func π) ⊓
    ⨅ v, v ∈ᴮ (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) ⟹
      (⨆ w, w ∈ᴮ (check pSet_aleph1 : bSet 𝔹_collapse) ⊓ pair w v ∈ᴮ π) :=
  le_inf π_is_func π_is_surj

-- src/forcing_CH.lean:554
lemma π_spec' {Γ : 𝔹_collapse} :
    Γ ≤ (is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π) ⊓
    is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  le_inf π_is_func' π_is_surj

-- src/forcing_CH.lean:556-557
lemma aleph1_larger_than_continuum {Γ : 𝔹_collapse} :
    Γ ≤ larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by
  apply bv_use (check pSet_aleph1)
  apply bv_use π
  rw [inf_assoc]
  exact le_inf subset_self π_spec'

lemma no_pset_surj_omega_aleph_one {h : PSet.{u}}
    (hh_func : PSet.is_func PSet.omega pSet_aleph1 h) :
    ¬ PSet.is_surj PSet.omega pSet_aleph1 h := by
  intro Hsurj
  obtain ⟨hf_sub, hf_uniq⟩ := hh_func
  have hg_exist : ∀ i : PSet.omega.Type, ∃ j : pSet_aleph1.Type,
      ZFSet.pair (ZFSet.mk (PSet.omega.Func i)) (ZFSet.mk (pSet_aleph1.Func j)) ∈ ZFSet.mk h := by
    intro i
    have hi_mem : ZFSet.mk (PSet.omega.Func i) ∈ ZFSet.mk PSet.omega :=
      ZFSet.mk_mem_iff.mpr (PSet.func_mem PSet.omega i)
    obtain ⟨w, hw_pair, _⟩ := hf_uniq _ hi_mem
    have hw_in_aleph1 : w ∈ ZFSet.mk pSet_aleph1 := by
      have h_in_prod := hf_sub hw_pair
      rw [ZFSet.mem_prod] at h_in_prod
      obtain ⟨a, _, b, hb, hab⟩ := h_in_prod
      exact (ZFSet.pair_injective hab).2 ▸ hb
    obtain ⟨j, hj⟩ : ∃ j : pSet_aleph1.Type, ZFSet.mk (pSet_aleph1.Func j) = w := by
      have hwp : w.out ∈ pSet_aleph1 := by
        have : ZFSet.mk w.out ∈ ZFSet.mk pSet_aleph1 := by
          simp [ZFSet.mk_out, hw_in_aleph1]
        exact ZFSet.mk_mem_iff.mp this
      rw [PSet.mem_def] at hwp
      obtain ⟨j, hj⟩ := hwp
      exact ⟨j, (ZFSet.sound hj.symm).trans (ZFSet.mk_out w)⟩
    exact ⟨j, hj ▸ hw_pair⟩
  let G : PSet.omega.Type → pSet_aleph1.Type := fun i => (hg_exist i).choose
  have hG_surj : Function.Surjective G := by
    intro j
    obtain ⟨a, ha_omega, ha_pair⟩ := Hsurj (pSet_aleph1.Func j) (PSet.func_mem pSet_aleph1 j)
    obtain ⟨i, hi⟩ : ∃ i : PSet.omega.Type, PSet.Equiv (PSet.omega.Func i) a := by
      rw [PSet.mem_def] at ha_omega
      obtain ⟨i, hi⟩ := ha_omega
      exact ⟨i, hi.symm⟩
    refine ⟨i, ?_⟩
    have hi_mem : ZFSet.mk (PSet.omega.Func i) ∈ ZFSet.mk PSet.omega :=
      ZFSet.mk_mem_iff.mpr (PSet.func_mem PSet.omega i)
    obtain ⟨_, _, huniq⟩ := hf_uniq _ hi_mem
    have hi_pair_j : ZFSet.pair (ZFSet.mk (PSet.omega.Func i)) (ZFSet.mk (pSet_aleph1.Func j)) ∈
        ZFSet.mk h := by
      rwa [← ZFSet.sound hi] at ha_pair
    have h1 := (hg_exist i).choose_spec
    have heq : ZFSet.mk (pSet_aleph1.Func (G i)) = ZFSet.mk (pSet_aleph1.Func j) :=
      (huniq (ZFSet.mk (pSet_aleph1.Func (G i))) h1).trans
      (huniq (ZFSet.mk (pSet_aleph1.Func j)) hi_pair_j).symm
    by_contra hne
    exact PSet.ordinalMk_inj (Cardinal.aleph 1).ord (G i) j hne (ZFSet.exact heq)
  have hcard_le : #(pSet_aleph1.Type) ≤ #(PSet.omega.Type) :=
    Cardinal.mk_le_of_surjective hG_surj
  rw [@PSet.mk_type_mk_eq'' (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1),
      PSet.mk_omega_eq_mk_omega] at hcard_le
  exact absurd hcard_le (not_le.mpr PSet.omega_lt_aleph_one)

-- src/forcing_CH.lean:559-593
-- src/forcing_CH.lean:559-593
set_option maxHeartbeats 800000 in
lemma surjection_reflect {Γ : 𝔹_collapse} (H_bot_lt : ⊥ < Γ)
    (H_surj : Γ ≤ surjects_onto (bSet.omega : bSet 𝔹_collapse)
                    (check pSet_aleph1 : bSet 𝔹_collapse))
    : ∃ (f : PSet.{u}),
      PSet.is_func PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f ∧
      PSet.is_surj PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f := by
  by_contra H
  simp only [not_exists, not_and_or] at H
  have Hf_ex := exists_surjection_of_surjects_onto H_surj
  obtain ⟨f, Γ_1, hΓ1_pos, hΓ1_le, _hΓ1_mem⟩ :=
    nonzero_wit'' principalOpens_denseOmegaClosed H_bot_lt Hf_ex
  have Hf_left : Γ_1 ≤ is_function bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_left)
  have Hf_right : Γ_1 ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_right)
  have hrefl := function_reflect_of_omega_closed
      principalOpens_denseOmegaClosed hΓ1_pos
      (is_func'_of_is_function Hf_left) Hf_left
      (fun px py {g} {Γ''} hg'' hpos'' i => AE_of_check_func_check' px py hg'' hpos'' i)
  let h := hrefl.choose
  let hΓ' : 𝔹_collapse := hrefl.choose_spec.choose
  let hΓ'_pos : ⊥ < hΓ' := hrefl.choose_spec.choose_spec.1
  let hΓ'_le : hΓ' ≤ Γ_1 := hrefl.choose_spec.choose_spec.2.1
  let hΓ'_eq : hΓ' ≤ check h =ᴮ f := hrefl.choose_spec.choose_spec.2.2.1
  let hh_func : PSet.is_func PSet.omega pSet_aleph1 h := hrefl.choose_spec.choose_spec.2.2.2
  have hh_not_surj : ¬ PSet.is_surj PSet.omega pSet_aleph1 h :=
    no_pset_surj_omega_aleph_one hh_func
  have hΓ'_surj : hΓ' ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ'_le.trans Hf_right
  have B_ext_is_surj_last : B_ext (fun z : bSet 𝔹_collapse =>
      is_surj bSet.omega (check pSet_aleph1) z) :=
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  exact false_of_bot_lt_and_le_bot hΓ'_pos
    (check_not_is_surj hh_not_surj
      (bv_rw' hΓ'_eq (ϕ := fun z => is_surj bSet.omega (check pSet_aleph1) z)
        (h_congr := B_ext_is_surj_last) (H_new := hΓ'_surj)))

-- src/forcing_CH.lean:595-608
set_option maxHeartbeats 800000 in
lemma omega_lt_aleph_one_collapse {Γ : 𝔹_collapse} :
    Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹_collapse)ᶜ := by
  -- Strategy: assume ⊥ < Γ ⊓ larger_than ω aleph1 and derive contradiction.
  rw [← imp_bot, ← deduction]
  by_contra H
  have H_pos : ⊥ < Γ ⊓ larger_than bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) :=
    bot_lt_iff_not_le_bot.mpr H
  have H_surj : Γ ⊓ larger_than bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) ≤
      surjects_onto bSet.omega (check pSet_aleph1 : bSet 𝔹_collapse) :=
    surjects_onto_of_larger_than_and_exists_mem inf_le_right
      (le_trans inf_le_right aleph_one_check_exists_mem)
  -- Mirror surjection_reflect: extract bSet function then reflect to PSet
  have Hf_ex := exists_surjection_of_surjects_onto H_surj
  obtain ⟨f, Γ_1, hΓ1_pos, hΓ1_le, _hΓ1_mem⟩ :=
    nonzero_wit'' principalOpens_denseOmegaClosed H_pos Hf_ex
  have Hf_left : Γ_1 ≤ is_function bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_left)
  have Hf_right : Γ_1 ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ1_le.trans (inf_le_left.trans inf_le_right)
  have hrefl := function_reflect_of_omega_closed
      principalOpens_denseOmegaClosed hΓ1_pos
      (is_func'_of_is_function Hf_left) Hf_left
      (fun px py {g} {Γ''} hg'' hpos'' i => AE_of_check_func_check' px py hg'' hpos'' i)
  let h := hrefl.choose
  let hΓ' : 𝔹_collapse := hrefl.choose_spec.choose
  let hΓ'_pos : ⊥ < hΓ' := hrefl.choose_spec.choose_spec.1
  let hΓ'_le : hΓ' ≤ Γ_1 := hrefl.choose_spec.choose_spec.2.1
  let hΓ'_eq : hΓ' ≤ check h =ᴮ f := hrefl.choose_spec.choose_spec.2.2.1
  let hh_func : PSet.is_func PSet.omega pSet_aleph1 h := hrefl.choose_spec.choose_spec.2.2.2
  have hh_not_surj : ¬ PSet.is_surj PSet.omega pSet_aleph1 h :=
    no_pset_surj_omega_aleph_one hh_func
  -- Contradiction: h is both surjective (from H_surj) and not surjective (from cardinality)
  have hΓ'_surj : hΓ' ≤ is_surj bSet.omega (check pSet_aleph1) f :=
    hΓ'_le.trans Hf_right
  have B_ext_is_surj_last : B_ext (fun z : bSet 𝔹_collapse =>
      is_surj bSet.omega (check pSet_aleph1) z) :=
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))
  exact false_of_bot_lt_and_le_bot hΓ'_pos
    (check_not_is_surj hh_not_surj
      (bv_rw' hΓ'_eq (ϕ := fun z => is_surj bSet.omega (check pSet_aleph1) z)
        (h_congr := B_ext_is_surj_last) (H_new := hΓ'_surj)))

-- src/forcing_CH.lean:610-615
lemma aleph_one_check_le_of_omega_lt_collapse (Γ : 𝔹_collapse) :
    Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹_collapse) := by
  -- Use bSet.aleph_one_check_is_aleph_one_of_omega_lt and aleph_one_le_of_omega_lt
  apply bv_rw' (bSet.aleph_one_check_is_aleph_one_of_omega_lt omega_lt_aleph_one_collapse)
  · exact B_ext_le_of_omega_lt
  · exact aleph_one_le_of_omega_lt

-- src/forcing_CH.lean:617-630
lemma continuum_le_continuum_check {Γ : 𝔹_collapse} :
    Γ ≤ bv_powerset (bSet.omega : bSet 𝔹_collapse) ≼
      (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by
  -- Port of src/forcing_CH.lean:617-630.
  -- Strategy:
  -- bv_powerset ω ≼ functions ω 𝟚  [powerset_injects_into_functions]
  -- functions ω 𝟚 = check(functions ω 2) = check(functions ω (ofNat 2))  [check_functions_eq_functions]
  -- check(functions ω (ofNat 2)) ≼ check(powerset ω)  [check_is_injective_function + functions_2_injects_into_powerset]
  -- Step 1: Get check(functions ω 2) ≼ check(powerset ω) from PSet injection
  have h_pset_inj := PSet.functions_2_injects_into_powerset PSet.omega
  obtain ⟨f_pset, Hf_pset⟩ := h_pset_inj
  -- h1: Γ ≤ injects_into (check (functions ω 2)) (check (powerset ω))
  have h1 : Γ ≤ injects_into
      (check (PSet.functions PSet.omega (PSet.ofNat 2)))
      (check (PSet.powerset PSet.omega)) := by
    rw [injects_into_iff_injection_into]
    exact le_trans le_top (le_iSup_of_le (check f_pset) (check_is_injective_function Hf_pset))
  -- Step 2: Rewrite check(functions ω 2) = functions ω 𝟚 using check_functions_eq_functions
  -- check_functions_eq_functions (PSet.ofNat 2) : Γ ≤ check(functions ω 2) =ᴮ functions ω (check 2)
  -- and check (PSet.ofNat 2) = 𝟚
  have h2 : Γ ≤ injects_into
      (functions bSet.omega (𝟚 : bSet 𝔹_collapse))
      (check (PSet.powerset PSet.omega)) :=
    bv_rw'' (check_functions_eq_functions (PSet.ofNat 2))
      (H_new := h1) (h_congr := B_ext_injects_into_left)
  -- Step 3: Combine: bv_powerset ω ≼ functions ω 𝟚 ≼ check(powerset ω)
  exact injects_into_trans (powerset_injects_into_functions bSet.omega) h2

-- src/forcing_CH.lean:632-637
-- ≺ = (larger_than _ _)ᶜ
-- The statement: (check ℵ₁ ≺ 𝒫ω)ᶜ = larger_than (check ℵ₁) (𝒫ω)
-- Proof: by contradiction from aleph1_larger_than_continuum and continuum_le_continuum_check
lemma aleph_one_not_lt_powerset_omega :
    ∀ {Γ : 𝔹_collapse},
    Γ ≤ ((check pSet_aleph1 : bSet 𝔹_collapse) ≺ 𝒫 bSet.omega)ᶜ := by
  intro Γ
  simp only [compl_compl]
  -- Goal: Γ ≤ larger_than (check ℵ₁) (bv_powerset ω)
  rw [← compl_compl (larger_than (check pSet_aleph1) (bv_powerset bSet.omega)),
      ← imp_bot, ← deduction]
  -- Goal: Γ ⊓ (larger_than (check ℵ₁) (bv_powerset ω))ᶜ ≤ ⊥
  apply bv_absurd (larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega)))
  · exact le_trans inf_le_left aleph1_larger_than_continuum
  · exact le_trans inf_le_right (bSet_lt_of_lt_of_le le_rfl continuum_le_continuum_check)

-- ============================================================
-- The main theorems: CH_true and CH₂_true (src lines 639-644)
-- ============================================================

-- src/forcing_CH.lean:639
/-- The continuum hypothesis holds in the collapse Boolean-valued model. -/
theorem CH_true : (⊤ : 𝔹_collapse) ≤ CH :=
  CH_true_aux (𝔹 := 𝔹_collapse)
    (fun {Γ} => aleph_one_check_le_of_omega_lt_collapse Γ)
    (fun {_} => aleph_one_not_lt_powerset_omega)

-- src/forcing_CH.lean:642
theorem CH₂_true : (⊤ : 𝔹_collapse) ≤ CH₂ :=
  CH_iff_CH₂.mp CH_true

end collapse_algebra

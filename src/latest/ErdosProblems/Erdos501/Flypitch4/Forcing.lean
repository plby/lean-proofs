/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/forcing.lean (567 lines) — Task 18 -/

import ErdosProblems.Erdos501.Flypitch4.BvmExtras
import ErdosProblems.Erdos501.Flypitch4.CantorSpace
import Mathlib.SetTheory.Cardinal.Pigeonhole

set_option relaxedAutoImplicit true

open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

-- ============================================================
-- src/forcing.lean:34-103: section cardinal_preservation
-- ============================================================

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing.lean:36-48
lemma AE_of_check_larger_than_check'' {x y : PSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ is_surj_onto (check x) (check y) f)
    (H_nonempty : ∃ z, z ∈ y) :
    ∀ i : y.Type, ∃ j : x.Type, ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  intro i
  -- is_surj_onto = is_func' ⊓ is_surj
  have H_func' : Γ ≤ is_func' (check x) (check y) f := le_trans H inf_le_left
  have H_surj : Γ ≤ is_surj (check x) (check y) f := le_trans H inf_le_right
  -- Apply is_surj at v = check (y.Func i): since check (y.Func i) ∈ check y by mem_check_of_mem
  -- get ⨆ w, w ∈ check x ⊓ pair w (check (y.Func i)) ∈ f
  have H_surj_i : Γ ≤ ⨆ w, w ∈ᴮ check x ⊓ pair w (check (y.Func i)) ∈ᴮ f := by
    have h_step := le_trans H_surj (iInf_le (f := fun v => v ∈ᴮ check y ⟹
        ⨆ w, w ∈ᴮ check x ⊓ pair w v ∈ᴮ f) (check (y.Func i)))
    exact le_trans (le_inf h_step mem_check_of_mem) (imp_inf_le _ _)
  -- Use bounded_exists to rewrite ⨆ w, w ∈ check x ⊓ ϕ w = ⨆ j, ϕ (check (x.Func j))
  rw [← @bounded_exists 𝔹 _ (check x) (fun w => pair w (check (y.Func i)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at H_surj_i
  simp only [check_bval_top, top_inf_eq] at H_surj_i
  -- H_surj_i : Γ ≤ ⨆ j : x.Type, pair (check (x.Func (check_cast j))) (check (y.Func i)) ∈ᴮ f
  -- Combine with H_func' to get ⨆ j, is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ f
  have H_combined : ⊥ < ⨆ j : (check x : bSet 𝔹).type,
      is_func f ⊓ pair ((check x : bSet 𝔹).func j) (check (y.Func i)) ∈ᴮ f := by
    apply lt_of_lt_of_le H_nonzero
    calc Γ
        ≤ is_func' (check x) (check y) f ⊓ ⨆ j, pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          le_inf H_func' H_surj_i
      _ = ⨆ j, is_func' (check x) (check y) f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          inf_iSup_eq'
      _ ≤ ⨆ j, is_func f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          iSup_mono fun j => le_inf (is_func_of_is_func' inf_le_left) inf_le_right
  obtain ⟨j, Hj⟩ := nonzero_wit H_combined
  exact ⟨check_cast j, by rwa [← check_func]⟩

-- src/forcing.lean:50-56
lemma AE_of_check_larger_than_check' {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ surjects_onto (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  -- surjects_onto (check x) (check y) = ⨆ f, is_func' (check x) (check y) f ⊓ is_surj ...
  -- Use maximum_principle to extract a specific f
  -- From surjects_onto, extract a concrete f using maximum_principle
  -- surjects_onto (check x) (check y) = ⨆ f, is_surj_onto (check x) (check y) f
  -- By maximum_principle, ∃ f, ⨆ g, is_surj_onto ... g = is_surj_onto ... f
  -- But B_ext proof for is_surj_onto f is needed; use is_function_right + simp
  -- B_ext (fun f => is_surj_onto (check x) (check y) f)
  -- = B_ext (fun f => is_func' x y f ⊓ is_surj x y f)
  -- = B_ext (fun f => (is_func f ⊓ is_total x y f) ⊓ is_surj x y f)
  -- Extract f from surjects_onto = ⨆ f, is_surj_onto (check x) (check y) f
  simp only [surjects_onto] at H
  obtain ⟨f, Hf⟩ := nonzero_wit' H_nonzero H
  -- Hf : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ
  -- Use the context Γ' = is_surj_onto f ⊓ Γ which is nonzero and ≤ is_surj_onto f
  have Hf_nonzero : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ := Hf
  have Hf_le : is_surj_onto (check x) (check y) f ⊓ Γ ≤ is_surj_onto (check x) (check y) f :=
    inf_le_left
  exact ⟨f, AE_of_check_larger_than_check'' f Hf_nonzero Hf_le H_mem⟩

-- src/forcing.lean:58-62
lemma AE_of_check_larger_than_check {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ larger_than (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f :=
  AE_of_check_larger_than_check' H_nonzero
    (surjects_onto_of_larger_than_and_exists_mem H
      (by obtain ⟨z, hz⟩ := H_mem; exact le_trans le_top (le_iSup_of_le (check z) (check_mem hz))))
    H_mem

-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)

include H_infinite H_lt H_inj₂ f H in
-- src/forcing.lean:71-100
lemma not_CCC_of_uncountable_fiber
    (H_ex : ∃ ξ : η₁.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ})) : ¬ CCC 𝔹 := by
  obtain ⟨ξ, H_ξ⟩ := H_ex
  let 𝓐 : (g⁻¹' {ξ}) → 𝔹 :=
    fun β => is_func f ⊓ pair (check (η₁.Func (g β.val))) (check (η₂.Func β.val)) ∈ᴮ f
  have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β := fun β => H β.val
  have 𝓐_anti : ∀ β₁ β₂ : (g⁻¹' {ξ}), β₁ ≠ β₂ → 𝓐 β₁ ⊓ 𝓐 β₂ ≤ ⊥ := by
    intro β₁ β₂ h_sep
    apply poset_yoneda; intro Γ a
    simp only [le_inf_iff] at a
    obtain ⟨ha₁, ha₂⟩ := a
    obtain ⟨H_func₁, H_mem₁⟩ := le_inf_iff.mp ha₁
    obtain ⟨_, H_mem₂⟩ := le_inf_iff.mp ha₂
    have hg₁ : g β₁.val = ξ := β₁.property
    have hg₂ : g β₂.val = ξ := β₂.property
    rw [hg₁] at H_mem₁; rw [hg₂] at H_mem₂
    have H_le_eq : Γ ≤ check (η₂.Func β₁.val) =ᴮ check (η₂.Func β₂.val) :=
      eq_of_is_func_of_eq H_func₁ bv_refl H_mem₁ H_mem₂
    apply le_trans H_le_eq
    rw [le_bot_iff]
    exact check_bv_eq_bot_of_not_equiv (H_inj₂ _ _ (fun heq => h_sep (Subtype.ext heq)))
  intro H_CCC
  exact absurd (le_antisymm (lt_iff_le_and_ne.mp H_ξ).1
    (H_CCC _ 𝓐 𝓐_nontriv 𝓐_anti)) (lt_iff_le_and_ne.mp H_ξ).2

end cardinal_preservation

end bSet

open bSet

-- ============================================================
-- src/forcing.lean:107-121: namespace PSet
-- ============================================================

namespace PSet

-- src/forcing.lean:109: ℵ₁ (as PSet)
@[reducible] noncomputable def pSet_aleph1 : PSet.{0} := ordinalMk (Cardinal.aleph 1).ord

-- src/forcing.lean:111: ℵ₂ (as PSet)
@[reducible] noncomputable def pSet_aleph2 : PSet.{0} := ordinalMk (Cardinal.aleph 2).ord

-- src/forcing.lean:113
lemma pSet_aleph2_unfold : pSet_aleph2 = ⟨pSet_aleph2.Type, pSet_aleph2.Func⟩ := by
  cases pSet_aleph2; rfl

-- src/forcing.lean:115-120: Union lemmas (not needed for the main result)

end PSet

open PSet

-- ============================================================
-- src/forcing.lean:125-133: 𝔹_cohen and instances
-- ============================================================

/-- The Cohen boolean algebra: regular opens on Set(PSet.pSet_aleph2.Type × ℕ) -/
noncomputable def 𝔹_cohen : Type :=
  @Flypitch.RegularOpens (Set (PSet.pSet_aleph2.Type × ℕ)) inferInstance

local notation "𝔹" => 𝔹_cohen

instance H_nonempty : Nonempty (Set (PSet.pSet_aleph2.Type × ℕ)) := ⟨∅⟩

noncomputable instance 𝔹_boolean_algebra :
    NontrivialCompleteBooleanAlgebra 𝔹 :=
  @Flypitch.RegularOpens.instNontrivialCBA _ _ H_nonempty

-- src/forcing.lean:134
lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.val ⊆ y.val :=
  Flypitch.RegularOpens.le_iff_subset

-- src/forcing.lean:136
lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, isRegularOpen_empty⟩ := by
  apply Flypitch.RegularOpens.ext; rfl

-- Type equality lemmas for cast operations
-- These hold because check x has .type = x.Type by the definition of check
private lemma eq₀ : (check (PSet.pSet_aleph2) : bSet 𝔹).type = PSet.pSet_aleph2.Type :=
  check_type'

private lemma eq₁ :
    ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg (· × ℕ) eq₀

private lemma eq₂ :
    Set ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Set (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Set eq₁

private lemma eq₃ :
    Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Finset (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Finset eq₁

-- src/forcing.lean:149-176: cast helper lemmas
universe w in
lemma pi₂_cast₁ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    HEq p.1 q.1 := by
  subst H'; exact heq_of_eq (congr_arg Prod.fst (eq_of_heq H))

universe w in
lemma pi₂_cast₂ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    p.2 = q.2 := by
  subst H'; exact congr_arg Prod.snd (eq_of_heq H)

universe w in
lemma compl_cast₂ {α β : Type w} {a : Set α} {b : Set β} (H' : α = β) (H : HEq aᶜ b) :
    HEq a bᶜ := by
  subst H'; exact heq_of_eq ((eq_of_heq H) ▸ (compl_compl a).symm)

lemma eq₁_cast (p : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) :
    cast eq₁ p = (cast eq₀ p.1, p.2) := by
  -- p : (check pSet_aleph2).type × ℕ =: α × ℕ, cast eq₁ p : pSet_aleph2.Type × ℕ
  have hcast : HEq p (cast eq₁ p) := (cast_heq eq₁ p).symm
  apply Prod.ext
  · -- need (cast eq₁ p).1 = cast eq₀ p.1
    -- pi₂_cast₁ eq₀ hcast : HEq p.1 (cast eq₁ p).1
    -- cast_heq eq₀ p.1 : HEq (cast eq₀ p.1) p.1
    apply eq_of_heq
    exact (pi₂_cast₁ eq₀ hcast).symm.trans (cast_heq eq₀ p.1).symm
  · exact (pi₂_cast₂ eq₀ hcast).symm

lemma eq₁_cast' (p : PSet.pSet_aleph2.Type × ℕ) :
    cast eq₁.symm p = (cast eq₀.symm p.1, p.2) := by
  have hcast : HEq p (cast eq₁.symm p) := (cast_heq eq₁.symm p).symm
  apply Prod.ext
  · apply eq_of_heq
    exact (pi₂_cast₁ eq₀.symm hcast).symm.trans (cast_heq eq₀.symm p.1).symm
  · exact (pi₂_cast₂ eq₀.symm hcast).symm

-- src/forcing.lean:178-179
theorem 𝔹_CCC : CCC 𝔹 :=
  Flypitch.RegularOpens.CCC_regular_opens CantorSpace.countable_chain_condition_set

local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191
/-- The principal regular open associated to a pair (ν, n) -/
noncomputable def principal_open (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
  ⟨CantorSpace.principalOpen (cast eq₁ (ν, n)),
   isRegularOpen_of_isClopen CantorSpace.isClopen_principalOpen⟩

lemma is_clopen_principal_open {ν n} : IsClopen (principal_open ν n).val :=
  CantorSpace.isClopen_principalOpen

-- src/forcing.lean:202-203
lemma perp_eq_compl_of_clopen {β : Type*} [TopologicalSpace β] {S : Set β}
    (H : IsClopen S) : Sᵖ = Sᶜ := by
  unfold Flypitch.perp; rw [IsClosed.closure_eq H.1]

-- src/forcing.lean:205-209
lemma mem_neg_principal_open_of_not_mem {ν n S} :
    (cast eq₁ (ν, n) ∈ Sᶜ) → S ∈ ((principal_open ν n)ᶜ).val := by
  intro H
  -- (principal_open ν n)ᶜ in 𝔹 = RegularOpens has val = perp of (principal_open ν n).val
  -- Since principal_open is clopen, perp = complement
  -- (principal_open ν n)ᶜ in 𝔹 has val = perp of (principal_open ν n).val (by RegularOpens.compl_val)
  -- and perp = compl since principal_open is clopen
  have hval : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᶜ := by
    have h1 : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᵖ :=
      Flypitch.RegularOpens.compl_val (principal_open ν n)
    rw [h1, perp_eq_compl_of_clopen is_clopen_principal_open]
  rw [hval]
  -- Goal: S ∈ (principal_open ν n).valᶜ  i.e. S ∉ (principal_open ν n).val
  -- (principal_open ν n).val = CantorSpace.principalOpen (cast eq₁ (ν,n)) = {S | cast eq₁ (ν,n) ∈ S}
  simp only [Set.mem_compl_iff, principal_open, CantorSpace.principalOpen, Set.mem_setOf_eq]
  exact H

-- src/forcing.lean:211-214: structure 𝒞
structure 𝒞 : Type where
  ins : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  out : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  H : ins ∩ out = ∅

-- src/forcing.lean:216
@[reducible] def π₂ : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ → ℕ := fun x => x.2

-- src/forcing.lean:223-245: ι definition
private noncomputable def ι : 𝒞 → 𝔹 :=
  fun p => ⟨{S | (p.ins.toSet) ⊆ (cast eq₂.symm S) ∧
                  (p.out.toSet) ⊆ (cast eq₂.symm Sᶜ)},
    isRegularOpen_of_isClopen (by
      -- Cast membership: x ∈ cast eq₂.symm S ↔ cast eq₁ x ∈ S
      have cast_mem_iff : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      -- The set equals principalOpenFinset (cast eq₃ p.ins) ∩ coPrincipalOpenFinset (cast eq₃ p.out)
      have hset : {S : Set (PSet.pSet_aleph2.Type × ℕ) |
                    p.ins.toSet ⊆ cast eq₂.symm S ∧ p.out.toSet ⊆ cast eq₂.symm Sᶜ} =
                  CantorSpace.principalOpenFinset (cast eq₃ p.ins) ∩
                  CantorSpace.coPrincipalOpenFinset (cast eq₃ p.out) := by
        ext S
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, CantorSpace.mem_principalOpenFinset_iff,
          CantorSpace.coPrincipalOpenFinset, Set.mem_setOf_eq]
        -- LHS: ∀ x ∈ p.ins.toSet, cast eq₁ x ∈ S  and  ∀ x ∈ p.out.toSet, cast eq₁ x ∉ S
        -- RHS: (cast eq₃ p.ins).toSet ⊆ S  and  (cast eq₃ p.out).toSet ⊆ Sᶜ
        -- Key: use cast_mem_iff directly to relate membership
        -- For x ∈ cast eq₃ F ↔ cast eq₁.symm x ∈ F, we use:
        -- eq₃ = congr_arg Finset eq₁, so cast eq₃ F = cast (congr_arg Finset eq₁) F
        -- and x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F (by subst h)
        have cast_finset_mem : ∀ (F : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ))
            (x : PSet.pSet_aleph2.Type × ℕ),
            x ∈ (cast eq₃ F : Finset (PSet.pSet_aleph2.Type × ℕ)) ↔ cast eq₁.symm x ∈ F := by
          intro F x
          -- cast eq₃ F : Finset B. Membership: x ∈ cast eq₃ F ↔ eq₁.symm cast x ∈ F
          -- Use: cast eq₃ = Equiv.cast of the Finset type equality
          -- Since eq₃ = congr_arg Finset eq₁, cast eq₃ maps Finset A → Finset B
          -- and is the image map: cast eq₃ F = F.image (cast eq₁)
          -- So x ∈ cast eq₃ F ↔ cast eq₁.symm x ∈ F (bijective)
          have key : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
              x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
            intro A B h; subst h; intro F x; simp
          have heq : eq₃ = congr_arg Finset eq₁ := rfl
          rw [heq]; exact key eq₁ F x
        constructor
        · intro ⟨h₁, h₂⟩
          constructor
          · -- S ∈ principalOpenFinset (cast eq₃ p.ins): ∀ x ∈ cast eq₃ p.ins, x ∈ S
            intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx
            -- hx : cast eq₁.symm x ∈ p.ins
            have hmem := (cast_mem_iff eq₁ S (cast eq₁.symm x)).mp (h₁ (Finset.mem_coe.mpr hx))
            -- hmem : cast eq₁ (cast eq₁.symm x) ∈ S; reduce to x ∈ S
            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
          · intro x hx
            rw [Finset.mem_coe, cast_finset_mem] at hx
            have hmem := (cast_mem_iff eq₁ Sᶜ (cast eq₁.symm x)).mp (h₂ (Finset.mem_coe.mpr hx))
            have hx_eq : cast eq₁ (cast eq₁.symm x) = x := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm x
            rw [hx_eq] at hmem; exact hmem
        · intro ⟨h₁, h₂⟩
          constructor
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₁
            rw [Finset.mem_coe, cast_finset_mem]
            -- Goal: cast eq₁.symm (cast eq₁ y) ∈ p.ins; reduce to y ∈ p.ins
            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
          · intro y hy
            rw [cast_mem_iff eq₁]
            apply h₂
            rw [Finset.mem_coe, cast_finset_mem]
            have hcast : cast eq₁.symm (cast eq₁ y) = y := by
              rw [cast_eq_iff_heq]; exact cast_heq eq₁ y
            rw [hcast]; exact hy
      rw [hset]
      exact (CantorSpace.isClopen_principalOpenFinset _).inter
        (CantorSpace.isClopen_coPrincipalOpenFinset _))⟩

open CantorSpace

-- src/forcing.lean:249-250
universe w₁ in
lemma prop_decidable_cast_lemma {α β : Type w₁} (H : α = β) {a b : α} {a' b' : β}
    (H_a : HEq a a') (H_b : HEq b b') :
    HEq (Classical.propDecidable (a = b)) (Classical.propDecidable (a' = b')) := by
  subst H; cases H_a; cases H_b; rfl

-- src/forcing.lean:252-272: 𝒞_dense_basis
lemma 𝒞_dense_basis : ∀ T ∈ @standardBasis (PSet.pSet_aleph2.Type × ℕ), ∀ _h : T ≠ ∅,
    ∃ p : 𝒞, (ι p).val ⊆ T := by
  intro T hT _h
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hT
  rcases hT with ⟨p_ins, p_out, hTeq, hDisj⟩ | hTe
  · -- T = p_ins.inf principalOpen ∩ p_out.inf coPrincipalOpen
    -- Helpers for casting
    -- General: x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F
    have key_finset_mem : ∀ {A B : Type} (h : A = B) (F : Finset A) (x : B),
        x ∈ cast (congr_arg Finset h) F ↔ cast h.symm x ∈ F := by
      intro A B h; subst h; intro F x; simp
    -- General: x ∈ cast (congr_arg Set h).symm S ↔ cast h x ∈ S
    have key_set_mem : ∀ {A B : Type} (h : A = B) (S : Set B) (x : A),
        x ∈ cast (congr_arg Set h).symm S ↔ cast h x ∈ S := by
      intro A B h; subst h; intro S x; simp
    -- (1) a ∈ cast eq₃.symm F' ↔ cast eq₁ a ∈ F' (for F' : Finset B, a : A)
    have cast_finset_symm : ∀ (F' : Finset (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ (cast eq₃.symm F' : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)) ↔ cast eq₁ a ∈ F' := by
      intro F' a
      -- cast eq₃.symm F' = cast (congr_arg Finset eq₁.symm) F' (since eq₃.symm = congr_arg Finset eq₁.symm)
      -- Then by key_finset_mem with h = eq₁.symm: a ∈ cast (congr_arg Finset eq₁.symm) F' ↔ cast eq₁ a ∈ F'
      have heq : eq₃.symm = congr_arg Finset eq₁.symm := rfl
      rw [heq, key_finset_mem eq₁.symm F' a]
    -- (2) a ∈ cast eq₂.symm S ↔ cast eq₁ a ∈ S (for S : Set B, a : A)
    have cast_set_symm : ∀ (S : Set (PSet.pSet_aleph2.Type × ℕ))
        (a : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ),
        a ∈ cast eq₂.symm S ↔ cast eq₁ a ∈ S := by
      intro S a
      have heq : eq₂.symm = (congr_arg Set eq₁).symm := by rfl
      rw [heq, key_set_mem eq₁ S a]
    -- Construct p' with ins = cast eq₃.symm p_ins, out = cast eq₃.symm p_out
    let p' : 𝒞 :=
      { ins := cast eq₃.symm p_ins
        out := cast eq₃.symm p_out
        H := by
          have hd := Finset.disjoint_left.mp hDisj
          ext a
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
          intro ⟨ha1, ha2⟩
          exact hd ((cast_finset_symm p_ins a).mp ha1) ((cast_finset_symm p_out a).mp ha2) }
    refine ⟨p', ?_⟩
    -- Show (ι p').val ⊆ T
    -- T = principalOpenFinset p_ins ∩ coPrincipalOpenFinset p_out
    rw [hTeq, ← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter]
    intro S hS
    simp only [ι, Set.mem_setOf_eq] at hS
    obtain ⟨hS_ins, hS_out⟩ := hS
    simp only [Set.mem_inter_iff, mem_principalOpenFinset_iff, coPrincipalOpenFinset,
      Set.mem_setOf_eq]
    -- Helper: cast eq₁ (cast eq₁.symm z) = z for z : B
    have cast_eq₁_symm_eq : ∀ (z : PSet.pSet_aleph2.Type × ℕ),
        cast eq₁ (cast eq₁.symm z) = z := by
      intro z; rw [cast_eq_iff_heq]; exact cast_heq eq₁.symm z
    constructor
    · intro z hz
      -- z ∈ p_ins, need z ∈ S
      -- cast eq₁.symm z ∈ cast eq₃.symm p_ins: by cast_finset_symm
      have ha : cast eq₁.symm z ∈ p'.ins := (cast_finset_symm p_ins (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_ins (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem
    · intro z hz hzS
      -- z ∈ p_out, need z ∉ S
      have ha : cast eq₁.symm z ∈ p'.out := (cast_finset_symm p_out (cast eq₁.symm z)).mpr
        (by rw [cast_eq₁_symm_eq]; exact hz)
      have hmem := hS_out (Finset.mem_coe.mpr ha)
      rw [cast_set_symm] at hmem
      rw [cast_eq₁_symm_eq] at hmem
      exact hmem hzS
  · -- T = ∅, contradicts _h
    exact absurd hTe _h

-- src/forcing.lean:274-284: 𝒞_dense
lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, ι p ≤ b := by
  have hne : b.val ≠ ∅ := by
    intro heq
    exact H.ne (Flypitch.RegularOpens.ext (Flypitch.RegularOpens.bot_val.trans heq.symm))
  obtain ⟨S_wit, H_wit⟩ := Set.nonempty_iff_ne_empty.mpr hne
  change ∃ p, (ι p).val ⊆ b.val
  rcases (is_topological_basis_standardBasis.exists_subset_of_mem_open H_wit
      (isOpen_of_isRegularOpen b.property))
    with ⟨v, Hv₁, Hv₂, Hv₃⟩
  obtain ⟨p, H_p⟩ := 𝒞_dense_basis v Hv₁ (fun hv => by rw [hv] at Hv₂; exact Hv₂)
  exact ⟨p, Set.Subset.trans H_p Hv₃⟩

-- src/forcing.lean:286-288
lemma to_set_inter {α : Type*} {p₁ p₂ : Finset α} :
    (p₁ ∩ p₂).toSet = p₁.toSet ∩ p₂.toSet := by
  ext; simp [Finset.mem_coe, Finset.mem_inter]

-- src/forcing.lean:292-299
lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : Finset α}
    (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  intro H' H''
  have : a ∈ p₁.toSet ∩ p₂.toSet := ⟨H', H''⟩
  rw [← to_set_inter] at this
  rw [congr_arg Finset.toSet H] at this
  exact absurd this (by simp [Finset.toSet])

-- src/forcing.lean:301-303
lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : Finset α}
    (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  rw [Finset.inter_comm] at H; exact not_mem_of_inter_empty_left H

-- src/forcing.lean:305-319: 𝒞_nonzero
lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ ι p := by
  -- Show ι p ≠ ⊥ by exhibiting an element S ∈ ι p
  -- The witness is S = cast eq₂ p.ins.toSet
  intro H
  -- H : ⊥ = ι p, so (ι p).val = ∅ (since ⊥ in 𝔹 has empty val)
  have hval_empty : (ι p).val = ∅ := by
    rw [← H]; exact Flypitch.RegularOpens.bot_val
  -- But S := cast eq₂ p.ins.toSet ∈ (ι p).val
  let S : 𝒳 := cast eq₂ p.ins.toSet
  have hS_mem : S ∈ (ι p).val := by
    simp only [ι, Set.mem_setOf_eq]
    constructor
    · -- p.ins.toSet ⊆ cast eq₂.symm S = p.ins.toSet
      intro x hx
      -- Need: x ∈ cast eq₂.symm (cast eq₂ p.ins.toSet)
      -- cast eq₂.symm ∘ cast eq₂ = id
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T) ↔ x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      exact (key eq₁ p.ins.toSet x).mpr hx
    · -- p.out.toSet ⊆ cast eq₂.symm Sᶜ = (p.ins.toSet)ᶜ
      intro x hx
      -- Need: x ∈ cast eq₂.symm (cast eq₂ p.ins.toSet)ᶜ = (p.ins.toSet)ᶜ
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T1) (x : T1),
          x ∈ cast (congr_arg Set h).symm (cast (congr_arg Set h) T)ᶜ ↔ x ∉ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [key eq₁]
      -- We need x ∉ p.ins.toSet.
      -- p.H : p.ins ∩ p.out = ∅, x ∈ p.out.toSet
      intro h_ins
      have : x ∈ p.ins ∩ p.out := by
        simp only [Finset.mem_inter, Finset.mem_coe] at *
        exact ⟨h_ins, hx⟩
      rw [p.H] at this
      exact absurd this (Finset.notMem_empty _)
  -- But (ι p).val = ∅ so S ∉ (ι p).val
  exact absurd hS_mem (by rw [hval_empty]; simp)

-- src/forcing.lean:323-350: 𝒞_disjoint_row
lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : PSet.pSet_aleph2.Type,
    (cast eq₁.symm (ξ, n)) ∉ p.ins ∧ (cast eq₁.symm (ξ, n)) ∉ p.out := by
  -- Let Y' = image π₂ (p.ins ∪ p.out)
  let Y' := Finset.image π₂ (p.ins ∪ p.out)
  by_cases h_empty : (p.ins ∪ p.out) = ∅
  · -- Case: p.ins ∪ p.out = ∅, so p.ins = ∅ and p.out = ∅
    use 0; intro ξ
    have h_ins : p.ins = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_left)
    have h_out : p.out = ∅ := Finset.subset_empty.mp (h_empty ▸ Finset.subset_union_right)
    refine ⟨?_, ?_⟩
    all_goals intro h
    · rw [h_ins] at h; exact Finset.notMem_empty _ h
    · rw [h_out] at h; exact Finset.notMem_empty _ h
  · -- Case: Y' is nonempty
    have h_Y'_nonempty : Y'.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.nonempty_of_ne_empty h_empty
    let N := Y'.max' h_Y'_nonempty
    use N + 1
    intro ξ
    constructor
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_left _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)
    · intro H_mem
      rw [eq₁_cast'] at H_mem
      have hNmem : N + 1 ∈ Y' := by
        simp only [Y', Finset.mem_image]
        exact ⟨_, Finset.mem_union_right _ H_mem, rfl⟩
      exact Nat.not_succ_le_self N (Finset.le_max' _ _ hNmem)

-- src/forcing.lean:352-353
lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁ := by
  intro H₁ H₂
  intro S hS
  obtain ⟨hS₁, hS₂⟩ := hS
  exact ⟨fun x hx => hS₁ (H₁ hx), fun x hx => hS₂ (H₂ hx)⟩

-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ -/
noncomputable def χ (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : ℕ → 𝔹 :=
  fun n => principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) -/
-- Definitionally `@set_of_indicator 𝔹 _ omega (fun n => χ ν n.down)` (the
-- Lean 3 definition); written out and marked reducible so that `(mk ν).type`
-- reduces to `ULift ℕ` at reducible transparency (needed by `simp` in
-- Lean ≥ 4.34).
@[reducible] noncomputable def mk (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : bSet 𝔹 :=
  ⟨ULift ℕ, fun n => of_nat n.down, fun n => χ ν n.down⟩

example (ν) : mk ν = @set_of_indicator 𝔹 _ omega (fun n => χ ν n.down) := rfl

@[simp] lemma mk_type {ν} : (mk ν).type = ULift ℕ := rfl

@[simp] lemma mk_func {ν} {n} : (mk ν).func n = of_nat (n.down) := rfl

@[simp] lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl

/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mk_bval, mk_func]
  -- Goal: χ ν i.down ⊓ Γ ≤ of_nat i.down ∈ᴮ omega
  exact le_trans inf_le_left (le_trans le_top omega_definite)

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

-- src/forcing.lean:379-386
lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ of_nat n ∈ᴮ mk ν₁)
    (H₂ : Γ ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ) :
    Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := by
  -- Show: (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥, which is equivalent
  -- Use le_neg_of_inf_eq_bot: to show Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ, show (mk ν₁ =ᴮ mk ν₂) ⊓ Γ = ⊥
  apply le_neg_of_inf_eq_bot
  rw [le_antisymm_iff]; constructor
  · -- (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥
    apply le_bot_iff.mpr
    -- Use subst_congr_mem_right: mk ν₁ =ᴮ mk ν₂ ⊓ of_nat n ∈ᴮ mk ν₁ ≤ of_nat n ∈ᴮ mk ν₂
    rw [eq_bot_iff]
    have hmem : mk ν₁ =ᴮ mk ν₂ ⊓ Γ ≤ of_nat n ∈ᴮ mk ν₂ :=
      le_trans (le_inf inf_le_left (le_trans inf_le_right H₁)) subst_congr_mem_right
    exact le_trans (le_inf hmem (le_trans inf_le_right H₂)) inf_compl_eq_bot.le
  · exact bot_le

-- src/forcing.lean:388-398
lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν, n) ∈ p.out) :
    ι p ≤ (of_nat n ∈ᴮ mk ν)ᶜ := by
  rw [mem_unfold, compl_iSup]
  apply le_iInf; intro k
  rw [compl_inf]
  by_cases hk : n = k.down
  · subst hk
    simp only [mk_bval, mk_func]
    rw [bv_eq_refl, compl_top, sup_bot_eq]
    intro S hS
    apply mem_neg_principal_open_of_not_mem
    have hS₂ := hS.2 (Finset.mem_coe.mpr H)
    have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
        x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
      intro T1 T2 h; subst h; intro T x; simp
    exact (key eq₁ Sᶜ (ν, k.down)).mp hS₂
  · have : of_nat n =ᴮ (of_nat k.down : bSet 𝔹) = ⊥ := of_nat_inj' hk
    simp only [mk_bval, mk_func, this, compl_bot, sup_top_eq]; exact le_top

-- src/forcing.lean:400-406
private lemma inj_cast_lemma (ν' : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n' : ℕ) :
    cast eq₁.symm (cast eq₀ ν', n') = (ν', n') := by
  rw [eq₁_cast']; simp [cast_cast]

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : mk ν₁ =ᴮ mk ν₂ ≤ (⊥ : 𝔹) := by
  by_contra h
  replace h : ⊥ < mk ν₁ =ᴮ mk ν₂ := lt_of_le_of_ne bot_le (Ne.symm (mt le_bot_iff.mpr h))
  obtain ⟨p, H_p⟩ := 𝒞_dense h
  obtain ⟨n, H_n⟩ := 𝒞_disjoint_row p
  -- p'.ins = insert (ν₁, n) p.ins, p'.out = insert (ν₂, n) p.out
  -- Note: ν₁, ν₂ : (check pSet_aleph2).type, so (ν₁, n), (ν₂, n) are in the right type
  -- H_n gives: cast eq₁.symm (cast eq₀ ν₁, n) = (ν₁, n) ∉ p.ins ∧ ∉ p.out (by inj_cast_lemma)
  have Hν₁_ins : (ν₁, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₁)).1
    rwa [inj_cast_lemma] at this
  have Hν₁_out : (ν₁, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₁)).2
    rwa [inj_cast_lemma] at this
  have Hν₂_ins : (ν₂, n) ∉ p.ins := by
    have := (H_n (cast eq₀ ν₂)).1
    rwa [inj_cast_lemma] at this
  have Hν₂_out : (ν₂, n) ∉ p.out := by
    have := (H_n (cast eq₀ ν₂)).2
    rwa [inj_cast_lemma] at this
  let p' : 𝒞 :=
    { ins := insert (ν₁, n) p.ins
      out := insert (ν₂, n) p.out
      H := by
        ext a
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
        intro ⟨ha_ins, ha_out⟩
        simp only [Finset.mem_insert] at ha_ins ha_out
        rcases ha_ins with rfl | ha_ins
        · -- a = (ν₁, n), and ha_out : (ν₁, n) = (ν₂, n) ∨ (ν₁, n) ∈ p.out
          rcases ha_out with h_eq | ha_out
          · -- (ν₁, n) = (ν₂, n), so ν₁ = ν₂
            exact H_neq (Prod.mk.inj h_eq).1
          · exact Hν₁_out ha_out
        · -- a ∈ p.ins
          rcases ha_out with rfl | ha_out
          · -- (ν₂, n) ∈ p.ins, contradicts Hν₂_ins
            exact Hν₂_ins ha_ins
          · -- a ∈ p.ins ∩ p.out = ∅
            have : a ∈ p.ins ∩ p.out := Finset.mem_inter.mpr ⟨ha_ins, ha_out⟩
            rw [p.H] at this
            exact Finset.notMem_empty _ this }
  -- ι p' ≤ ι p (by 𝒞_anti, since p'.ins ⊇ p.ins and p'.out ⊇ p.out)
  have anti : ι p' ≤ ι p :=
    𝒞_anti (fun i hi => Finset.mem_insert_of_mem hi)
           (fun i hi => Finset.mem_insert_of_mem hi)
  -- ι p' ≤ of_nat n ∈ᴮ mk ν₁
  have this₁ : ι p' ≤ of_nat n ∈ᴮ mk ν₁ := by
    rw [mem_unfold]
    apply le_iSup_of_le (ULift.up n)
    simp only [mk_bval, mk_func, χ, bv_refl, le_inf_iff]
    constructor
    · -- ι p' ≤ principal_open ν₁ n
      intro S hS
      simp only [ι, Set.mem_setOf_eq] at hS
      have hins : (ν₁, n) ∈ (p' : 𝒞).ins.toSet :=
        Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      have hmem := hS.1 hins
      -- hmem : (ν₁, n) ∈ cast eq₂.symm S, i.e., cast eq₁ (ν₁, n) ∈ S
      have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
          x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
        intro T1 T2 h; subst h; intro T x; simp
      rw [show (principal_open ν₁ n).val = CantorSpace.principalOpen (cast eq₁ (ν₁, n)) from rfl]
      exact (key eq₁ S (ν₁, n)).mp hmem
    · trivial  -- bv_refl : of_nat n =ᴮ of_nat n = ⊤ simplified to True
  -- ι p' ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ
  have this₂ : ι p' ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ :=
    not_mem_of_not_mem (Finset.mem_insert_self (ν₂, n) p.out)
  -- ι p' ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ (from sep)
  have this₃ : ι p' ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := sep this₁ this₂
  -- ι p' ≤ mk ν₁ =ᴮ mk ν₂ (via ι p' ≤ ι p ≤ mk ν₁ =ᴮ mk ν₂)
  have this₄ : ι p' ≤ mk ν₁ =ᴮ mk ν₂ := le_trans anti H_p
  -- Contradiction: ι p' = ⊥, but 𝒞_nonzero says ⊥ ≠ ι p'
  have this₅ : ι p' = ⊥ := le_antisymm (le_trans (le_inf this₄ this₃) inf_compl_eq_bot.le) bot_le
  exact (𝒞_nonzero p') this₅.symm

end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457
lemma uncountable_fiber_of_regular' (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂) (α : Type u) (H_α : #α = κ₁)
    (β : Type u) (H_β : #β = κ₂) (g : β → α) :
    ∃ (ξ : α), Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
  -- Use Cardinal.infinite_pigeonhole: if ℵ₀ ≤ #β and #α < (#β).ord.cof, then some fiber has #β
  have h₁ : Cardinal.aleph0 ≤ #β := H_β ▸ le_of_lt (lt_of_le_of_lt H_inf H_lt)
  have h₂ : #α < (#β).ord.cof := by
    rw [H_α, H_β, H]; exact H_lt
  obtain ⟨ξ, Hξ⟩ := Cardinal.infinite_pigeonhole g h₁ h₂
  -- Hξ : #(g⁻¹'{ξ}) = #β, and ℵ₀ ≤ #β = κ₂ > κ₁ ≥ ℵ₀
  refine ⟨ξ, ?_⟩
  rw [Hξ, H_β]
  exact lt_of_le_of_lt H_inf H_lt

-- src/forcing.lean:459-466
lemma uncountable_fiber_of_regular (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂)
    (g : (PSet.card_ex κ₂).Type → (PSet.card_ex κ₁).Type) :
    ∃ (ξ : (PSet.card_ex κ₁).Type), Cardinal.aleph0 < #↥((fun β => g β)⁻¹' {ξ}) :=
  uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H _
    (PSet.mk_type_mk_eq κ₁ H_inf) _ (PSet.mk_type_mk_eq κ₂ (le_of_lt (lt_of_le_of_lt H_inf H_lt))) g

-- src/forcing.lean:468-487
lemma cardinal_inequality_of_regular (κ₁ κ₂ : Cardinal)
    (H_reg₁ : Cardinal.IsRegular κ₁) (H_reg₂ : Cardinal.IsRegular κ₂)
    (H_inf : Cardinal.aleph0 ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} :
    Γ ≤ (larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)))ᶜ := by
  -- Prove by contradiction: if Γ ≤ larger_than κ₁ κ₂, derive ¬CCC 𝔹, contradicting 𝔹_CCC
  apply le_neg_of_inf_eq_bot
  rw [inf_comm]
  -- Goal: Γ ⊓ larger_than (check κ₁) (check κ₂) ≤ ⊥ ... actually need = ⊥
  -- wait le_neg_of_inf_eq_bot needs b ⊓ a = ⊥ to conclude a ≤ bᶜ
  -- So need larger_than ... ⊓ Γ = ⊥ i.e. Γ ⊓ larger_than ... = ⊥
  rw [eq_bot_iff]
  -- Goal: Γ ⊓ larger_than ... ≤ ⊥
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  -- Apply AE_of_check_larger_than_check to get f and g
  have H_larger : Γ ⊓ larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) ≤
      larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) := inf_le_right
  rcases AE_of_check_larger_than_check H_nonzero H_larger
    (PSet.exists_mem_of_regular H_reg₂) with ⟨f, Hf⟩
  -- Extract g : κ₂.Type → κ₁.Type from Hf
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  -- Use not_CCC_of_uncountable_fiber with the extracted g
  have H_inf₁ : Cardinal.aleph0 ≤ #((PSet.card_ex κ₁).Type) := by simp [H_inf]
  have H_lt₁ : #((PSet.card_ex κ₁).Type) < #((PSet.card_ex κ₂).Type) := by
    rw [@PSet.mk_type_mk_eq'' κ₁ H_inf, @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))]
    exact H_lt
  have H_inj₂₁ : ∀ i j, i ≠ j → ¬ PSet.Equiv ((PSet.card_ex κ₂).Func i) ((PSet.card_ex κ₂).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : (PSet.card_ex κ₁).Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
    apply uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H_reg₂.cof_ord
    · exact @PSet.mk_type_mk_eq'' κ₁ H_inf
    · exact @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))
  exact absurd 𝔹_CCC (not_CCC_of_uncountable_fiber (PSet.card_ex κ₁) (PSet.card_ex κ₂)
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex)

-- src/forcing.lean:489-504
lemma aleph0_lt_aleph1_bSet : (⊤ : 𝔹) ≤
    (larger_than omega (check (PSet.card_ex (Cardinal.aleph 1))))ᶜ := by
  -- omega = check PSet.omega, so we use the same pattern as cardinal_inequality_of_regular
  -- but with η₁ = PSet.omega
  apply le_neg_of_inf_eq_bot
  rw [inf_comm, eq_bot_iff]
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  rcases AE_of_check_larger_than_check H_nonzero (le_trans inf_le_right (le_refl _))
    (PSet.exists_mem_of_regular PSet.is_regular_aleph_one) with ⟨f, Hf⟩
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  suffices h : ¬ CCC 𝔹 from absurd 𝔹_CCC h
  -- η₁ = PSet.omega (type = ULift ℕ, #type = aleph0)
  -- η₂ = PSet.card_ex (aleph 1) (type = (card_ex aleph1).Type, #type = aleph1)
  have H_omega_card : #(PSet.omega.Type) = Cardinal.aleph0 := PSet.mk_omega_eq_mk_omega
  have H_aleph1_card : #((PSet.card_ex (Cardinal.aleph 1)).Type) = Cardinal.aleph 1 :=
    @PSet.mk_type_mk_eq'' (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1)
  have H_inf₁ : Cardinal.aleph0 ≤ #(PSet.omega.Type) := H_omega_card.symm ▸ le_refl _
  have H_lt₁ : #(PSet.omega.Type) < #((PSet.card_ex (Cardinal.aleph 1)).Type) := by
    rw [H_omega_card, H_aleph1_card]; exact Cardinal.aleph0_lt_aleph_one
  have H_inj₂₁ : ∀ i j, i ≠ j →
      ¬ PSet.Equiv ((PSet.card_ex (Cardinal.aleph 1)).Func i)
                   ((PSet.card_ex (Cardinal.aleph 1)).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : PSet.omega.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) :=
    uncountable_fiber_of_regular' (Cardinal.aleph 0) (Cardinal.aleph 1)
      (Cardinal.aleph0_le_aleph 0)
      (by rw [Cardinal.aleph_lt_aleph]; exact zero_lt_one)
      PSet.is_regular_aleph_one.cof_ord
      PSet.omega.Type (H_omega_card.trans Cardinal.aleph_zero.symm)
      (PSet.card_ex (Cardinal.aleph 1)).Type H_aleph1_card g
  exact not_CCC_of_uncountable_fiber PSet.omega (PSet.card_ex (Cardinal.aleph 1))
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex

-- src/forcing.lean:507-509
lemma aleph1_lt_aleph2_bSet : (⊤ : 𝔹) ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  cardinal_inequality_of_regular _ _ PSet.is_regular_aleph_one PSet.is_regular_aleph_two
    (Cardinal.aleph0_le_aleph 1) PSet.aleph_one_lt_aleph_two

lemma aleph1_lt_aleph2_bSet' {Γ : 𝔹} : Γ ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  le_trans le_top aleph1_lt_aleph2_bSet

-- src/forcing.lean:513-529: cohen_real.mk_ext
lemma cohen_real.mk_ext : ∀ (i j : (check (PSet.pSet_aleph2) : bSet 𝔹).type),
    (check (PSet.pSet_aleph2) : bSet 𝔹).func i =ᴮ (check (PSet.pSet_aleph2) : bSet 𝔹).func j ≤
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) i =ᴮ
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) j := by
  intro i j; by_cases h : i = j
  · simp [h]
  · apply poset_yoneda; intro Γ a
    rw [check_func, check_func] at a
    suffices h_bot : (check (PSet.pSet_aleph2.Func (check_cast i)) : bSet 𝔹) =ᴮ
        check (PSet.pSet_aleph2.Func (check_cast j)) ≤ ⊥ by
      exact le_trans a (le_trans h_bot bot_le)
    rw [le_bot_iff]
    apply check_bv_eq_bot_of_not_equiv
    -- pSet_aleph2 = ordinalMk (aleph 2).ord
    -- pSet_aleph2.Func (check_cast i) ≠ pSet_aleph2.Func (check_cast j) when i ≠ j
    apply PSet.ordinalMk_inj (Cardinal.aleph 2).ord
    intro H; exact h (by simp only [type] at H ⊢; exact H)

-- src/forcing.lean:531-532
noncomputable def neg_CH_func : bSet 𝔹 :=
  @functionMk _ _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x) cohen_real.mk_ext

-- src/forcing.lean:534-546
set_option maxHeartbeats 400000 in
theorem aleph2_le_powerset_omega :
    ⊤ ≤ is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func ⊓ is_inj neg_CH_func := by
  apply le_inf
  · -- is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func = is_func neg_CH_func ⊓ is_total ...
    apply le_inf
    · -- is_func neg_CH_func
      exact functionMk_is_func _ cohen_real.mk_ext
    · -- is_total (check PSet.pSet_aleph2) 𝔠 neg_CH_func
      apply le_iInf; intro w₁; rw [← deduction, top_inf_eq]
      -- w₁ ∈ check PSet.pSet_aleph2 ≤ ⨆ w₂, w₂ ∈ 𝔠 ⊓ pair w₁ w₂ ∈ neg_CH_func
      -- Unfold the membership w₁ ∈ check PSet.pSet_aleph2 to extract ν
      rw [mem_unfold]
      -- ⨆ ν, (check pSet_aleph2).bval ν ⊓ w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, ...
      apply iSup_le; intro ν
      -- (check pSet_aleph2).bval ν ⊓ w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, ...
      rw [check_bval_top, top_inf_eq]
      -- w₁ =ᴮ (check pSet_aleph2).func ν ≤ ⨆ w₂, w₂ ∈ 𝔠 ⊓ pair w₁ w₂ ∈ neg_CH_func
      apply le_iSup_of_le (cohen_real.mk ν)
      -- cohen_real.definite' : Γ ≤ cohen_real.mk ν ∈ 𝔠
      -- functionMk_self : check.bval ν ≤ pair (check.func ν) (mk ν) ∈ neg_CH_func
      -- We need: w₁ =ᴮ check.func ν ≤ mk ν ∈ 𝔠 ⊓ pair w₁ (mk ν) ∈ neg_CH_func
      apply le_inf
      · -- mk ν ∈ 𝔠
        exact le_trans le_top cohen_real.definite'
      · -- pair w₁ (mk ν) ∈ neg_CH_func
        -- w₁ =ᴮ (check pSet_aleph2).func ν; pair (check.func ν) (mk ν) ∈ neg_CH_func by functionMk_self
        -- Use bv_rw' with H := w₁ =ᴮ check.func ν (the current goal), ϕ := fun z => pair z (mk ν) ∈ neg_CH_func
        have h_func_mem : (⊤ : 𝔹) ≤ pair ((check PSet.pSet_aleph2).func ν) (cohen_real.mk ν) ∈ᴮ neg_CH_func := by
          have := @functionMk_self 𝔹 _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x)
            cohen_real.mk_ext ν
          rwa [check_bval_top] at this
        -- Γ = w₁ =ᴮ check.func ν, use bv_rw' to get pair w₁ (mk ν) ∈ neg_CH_func from pair (check.func ν) (mk ν) ∈ neg_CH_func
        exact bv_rw' (H := le_refl _) (ϕ := fun z => pair z (cohen_real.mk ν) ∈ᴮ neg_CH_func)
          (h_congr := B_ext_pair_mem_left) (H_new := le_trans le_top h_func_mem)
  · -- is_inj neg_CH_func
    exact functionMk_inj_of_inj (fun i j h => cohen_real.inj h) cohen_real.mk_ext

-- src/forcing.lean:548-550
lemma aleph1_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) :=
  Ord_card_ex _

lemma aleph2_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 2)) : bSet 𝔹) :=
  Ord_card_ex _

-- src/forcing.lean:552-562
theorem neg_CH : (⊤ : 𝔹) ≤ CHᶜ := by
  simp only [CH, compl_compl]
  exact le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 1)))
    (le_inf aleph1_Ord (le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 2)))
      (le_inf (le_inf aleph0_lt_aleph1_bSet aleph1_lt_aleph2_bSet)
        (le_iSup_of_le neg_CH_func aleph2_le_powerset_omega))))

-- src/forcing.lean:564-565
theorem neg_CH₂ : (⊤ : 𝔹) ≤ CH₂ᶜ :=
  (Lattice.bv_iff_neg CH_iff_CH₂).mp neg_CH

end neg_CH

end bSet

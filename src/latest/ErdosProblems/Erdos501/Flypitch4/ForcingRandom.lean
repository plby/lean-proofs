/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Forcing ¬CH with the ℵ₂-random algebra.
-/
import ErdosProblems.Erdos501.Flypitch4.RandomAlgebra
import ErdosProblems.Erdos501.Flypitch4.Zfc

set_option relaxedAutoImplicit true

/-!
# Forcing `¬CH` with the `ℵ₂`-random algebra

Flypitch proves the unprovability of `CH` from `ZFC` by exhibiting a Boolean-valued model
`V 𝔹_cohen` of `ZFC` in which `CH` fails, where `𝔹_cohen` is the Cohen algebra (the regular
open algebra of `2^(ℵ₂ × ω)`).  This file gives an *alternative* consistency proof of `¬CH`,
using the `ℵ₂`-random algebra `𝔹_random` (the measure algebra of the product measure on
`2^(ℵ₂ × ω)`, see `RandomAlgebra.lean`) instead.

The argument is organised as follows.

* `bSet.neg_CH_of_CCC_of_indep`: an abstract version of the "`¬CH` in the Boolean-valued
  model" argument.  For *any* nontrivial complete Boolean algebra `𝔹` satisfying the countable
  chain condition, and any family `χ : ℵ₂ → ℕ → 𝔹` of "independent bits" (in the sense that for
  `ν₁ ≠ ν₂` the Boolean value of `∀ n, χ ν₁ n ↔ χ ν₂ n` is `⊥`), `V 𝔹 ⊨ ¬CH`.  The `ccc` gives
  cardinal preservation (`ω < ℵ₁ < ℵ₂` in `V 𝔹`) exactly as in the Cohen case, and the bits give
  `ℵ₂` pairwise distinct subsets of `ω`, hence an injection `ℵ₂ ↪ 𝒫(ω)`.

  (The Cohen proof in `Forcing.lean` is the special case where `𝔹` is the Cohen algebra and
  `χ ν n` is the principal open set determined by `(ν, n)`; here we do not refactor that proof
  but re-prove the abstract statement.)

* `bSet.neg_CH₂_random`, `V_𝔹_random_models_neg_CH`, `CH_f_unprovable_random`: the
  instantiation with the random algebra, using `𝔹_random_CCC` and
  `RandomAlgebra.iInf_biimp_χ_eq_bot`.
-/

open scoped Cardinal
open Flypitch

universe u

namespace bSet

/-! ### Cardinal inequalities from the countable chain condition

These are the proofs of `cardinal_inequality_of_regular`, `aleph0_lt_aleph1_bSet` and
`aleph1_lt_aleph2_bSet` from `Forcing.lean`, which only use `𝔹_CCC` about the Cohen algebra,
re-done for an arbitrary `𝔹` satisfying `CCC`. -/

section cardinal_inequalities

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] (H_ccc : CCC 𝔹)

include H_ccc in
lemma cardinal_inequality_of_regular_of_CCC (κ₁ κ₂ : Cardinal)
    (_H_reg₁ : Cardinal.IsRegular κ₁) (H_reg₂ : Cardinal.IsRegular κ₂)
    (H_inf : Cardinal.aleph0 ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} :
    Γ ≤ (larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)))ᶜ := by
  apply le_neg_of_inf_eq_bot
  rw [inf_comm]
  rw [eq_bot_iff]
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  have H_larger : Γ ⊓ larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) ≤
      larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)) := inf_le_right
  rcases AE_of_check_larger_than_check H_nonzero H_larger
    (PSet.exists_mem_of_regular H_reg₂) with ⟨f, Hf⟩
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  have H_inf₁ : Cardinal.aleph0 ≤ #((PSet.card_ex κ₁).Type) := by simp [H_inf]
  have H_lt₁ : #((PSet.card_ex κ₁).Type) < #((PSet.card_ex κ₂).Type) := by
    rw [@PSet.mk_type_mk_eq'' κ₁ H_inf, @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))]
    exact H_lt
  have H_inj₂₁ : ∀ i j, i ≠ j →
      ¬ PSet.Equiv ((PSet.card_ex κ₂).Func i) ((PSet.card_ex κ₂).Func j) :=
    fun i j h => PSet.ordinalMk_inj _ _ _ h
  have H_ex : ∃ ξ : (PSet.card_ex κ₁).Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
    apply uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H_reg₂.cof_ord
    · exact @PSet.mk_type_mk_eq'' κ₁ H_inf
    · exact @PSet.mk_type_mk_eq'' κ₂ (le_of_lt (H_inf.trans_lt H_lt))
  exact absurd H_ccc (not_CCC_of_uncountable_fiber (PSet.card_ex κ₁) (PSet.card_ex κ₂)
    H_inf₁ H_lt₁ H_inj₂₁ f g g_spec H_ex)

include H_ccc in
lemma aleph0_lt_aleph1_bSet_of_CCC : (⊤ : 𝔹) ≤
    (larger_than omega (check (PSet.card_ex (Cardinal.aleph 1))))ᶜ := by
  apply le_neg_of_inf_eq_bot
  rw [inf_comm, eq_bot_iff]
  by_contra H_nonzero
  rw [← bot_lt_iff_not_le_bot] at H_nonzero
  rcases AE_of_check_larger_than_check H_nonzero (le_trans inf_le_right (le_refl _))
    (PSet.exists_mem_of_regular PSet.is_regular_aleph_one) with ⟨f, Hf⟩
  obtain ⟨g, g_spec⟩ := Classical.axiomOfChoice Hf
  suffices h : ¬ CCC 𝔹 from absurd H_ccc h
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

include H_ccc in
lemma aleph1_lt_aleph2_bSet_of_CCC : (⊤ : 𝔹) ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  cardinal_inequality_of_regular_of_CCC H_ccc _ _ PSet.is_regular_aleph_one
    PSet.is_regular_aleph_two (Cardinal.aleph0_le_aleph 1) PSet.aleph_one_lt_aleph_two

end cardinal_inequalities

/-! ### Reals from independent bits

Given a family of "bits" `χ : ℵ₂ → ℕ → 𝔹`, we form the `ℵ₂` names
`indep_real.mk χ ν = {n ∈ ω | χ ν n}` for subsets of `ω`.  If the bits are *independent* in the
sense that `⨅ n, (χ ν₁ n ⇔ χ ν₂ n) = ⊥` for `ν₁ ≠ ν₂`, these names are pairwise distinct
(with Boolean value `⊤`). -/

section indep_real

-- `PSet.pSet_aleph2 : PSet.{0}`, so this section is at universe level `0`.
variable {𝔹 : Type} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The independence property of a family of bits: distinct rows are (a.e.) different. -/
def IndepBits (χ : (check (PSet.pSet_aleph2) : bSet 𝔹).type → ℕ → 𝔹) : Prop :=
  ∀ ν₁ ν₂, ν₁ ≠ ν₂ → (⨅ n : ℕ, biimp (χ ν₁ n) (χ ν₂ n)) ≤ ⊥

namespace indep_real

variable (χ : (check (PSet.pSet_aleph2) : bSet 𝔹).type → ℕ → 𝔹)

/-- The subset of `ω` with characteristic function `χ ν`. -/
-- Definitionally `@set_of_indicator 𝔹 _ omega (fun n => χ ν n.down)`; written out and
-- marked reducible so that `(mk χ ν).type` reduces to `ULift ℕ` at reducible
-- transparency (Lean ≥ 4.34 `simp`), exactly as for `cohen_real.mk` in `Forcing.lean`.
@[reducible] noncomputable def mk (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : bSet 𝔹 :=
  ⟨ULift ℕ, fun n => of_nat n.down, fun n => χ ν n.down⟩

example (ν) : mk χ ν = @set_of_indicator 𝔹 _ omega (fun n => χ ν n.down) := rfl

@[simp] lemma mk_type {ν} : (mk χ ν).type = ULift ℕ := rfl

@[simp] lemma mk_func {ν} {n} : (mk χ ν).func n = of_nat (n.down) := rfl

@[simp] lemma mk_bval {ν} {n} : (mk χ ν).bval n = χ ν n.down := rfl

/-- `bSet 𝔹` believes that each `mk χ ν` is a subset of `ω`. -/
lemma definite {ν} {Γ : 𝔹} : Γ ≤ mk χ ν ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mk_bval, mk_func]
  exact le_trans inf_le_left (le_trans le_top omega_definite)

/-- `bSet 𝔹` believes that each `mk χ ν` is an element of `𝒫(ω)`. -/
lemma definite' {ν} {Γ : 𝔹} : Γ ≤ mk χ ν ∈ᴮ bv_powerset omega :=
  bv_powerset_spec.mp (definite χ)

/-- The Boolean value of `n ∈ mk χ ν` is exactly the bit `χ ν n`. -/
lemma mem_mk {ν} {n : ℕ} : (of_nat n ∈ᴮ mk χ ν) = χ ν n := by
  rw [mem_unfold]
  apply le_antisymm
  · apply iSup_le; intro k
    by_cases hk : n = k.down
    · subst hk; simp only [mk_bval, mk_func]; exact inf_le_left
    · simp only [mk_bval, mk_func, of_nat_inj' hk, inf_bot_eq]; exact bot_le
  · apply le_iSup_of_le (ULift.up n)
    simp only [mk_bval, mk_func, bv_eq_refl, inf_top_eq, le_refl]

/-- Distinct names are forced to be different reals, provided the bits are independent. -/
lemma inj (H_indep : IndepBits χ) {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) :
    mk χ ν₁ =ᴮ mk χ ν₂ ≤ (⊥ : 𝔹) := by
  refine le_trans ?_ (H_indep ν₁ ν₂ H_neq)
  apply le_iInf; intro n
  simp only [biimp]
  apply le_inf
  · rw [← deduction, ← mem_mk χ (ν := ν₁), ← mem_mk χ (ν := ν₂)]
    exact subst_congr_mem_right
  · rw [← deduction, ← mem_mk χ (ν := ν₁), ← mem_mk χ (ν := ν₂), bv_eq_symm]
    exact subst_congr_mem_right

/-- The family `ν ↦ mk χ ν` respects Boolean equality on `ℵ₂̌ ` (whose distinct elements are
forced to be distinct). -/
lemma mk_ext : ∀ (i j : (check (PSet.pSet_aleph2) : bSet 𝔹).type),
    (check (PSet.pSet_aleph2) : bSet 𝔹).func i =ᴮ (check (PSet.pSet_aleph2) : bSet 𝔹).func j ≤
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => mk χ x) i =ᴮ
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => mk χ x) j := by
  intro i j; by_cases h : i = j
  · simp [h]
  · apply poset_yoneda; intro Γ a
    rw [check_func, check_func] at a
    suffices h_bot : (check (PSet.pSet_aleph2.Func (check_cast i)) : bSet 𝔹) =ᴮ
        check (PSet.pSet_aleph2.Func (check_cast j)) ≤ ⊥ by
      exact le_trans a (le_trans h_bot bot_le)
    rw [le_bot_iff]
    apply check_bv_eq_bot_of_not_equiv
    apply PSet.ordinalMk_inj (Cardinal.aleph 2).ord
    intro H; exact h (by simp [check_cast] at H ⊢; exact H)

/-- The name of the function `ℵ₂ → 𝒫(ω)`, `ν ↦ mk χ ν`. -/
noncomputable def neg_CH_func : bSet 𝔹 :=
  @functionMk _ _ (check PSet.pSet_aleph2) (fun x => mk χ x) (mk_ext χ)

set_option maxHeartbeats 400000 in
/-- The function `ν ↦ mk χ ν` is (forced to be) an injection `ℵ₂ ↪ 𝒫(ω)`. -/
theorem aleph2_le_powerset_omega (H_indep : IndepBits χ) :
    ⊤ ≤ is_func' (check PSet.pSet_aleph2) (bv_powerset omega) (neg_CH_func χ) ⊓
      is_inj (neg_CH_func χ) := by
  apply le_inf
  · apply le_inf
    · exact functionMk_is_func _ (mk_ext χ)
    · apply le_iInf; intro w₁; rw [← deduction, top_inf_eq]
      rw [mem_unfold]
      apply iSup_le; intro ν
      rw [check_bval_top, top_inf_eq]
      apply le_iSup_of_le (mk χ ν)
      apply le_inf
      · exact le_trans le_top (definite' χ)
      · have h_func_mem : (⊤ : 𝔹) ≤
            pair ((check PSet.pSet_aleph2).func ν) (mk χ ν) ∈ᴮ neg_CH_func χ := by
          have := @functionMk_self 𝔹 _ (check PSet.pSet_aleph2) (fun x => mk χ x) (mk_ext χ) ν
          rwa [check_bval_top] at this
        exact bv_rw' (H := le_refl _) (ϕ := fun z => pair z (mk χ ν) ∈ᴮ neg_CH_func χ)
          (h_congr := B_ext_pair_mem_left) (H_new := le_trans le_top h_func_mem)
  · exact functionMk_inj_of_inj (fun i j h => inj χ H_indep h) (mk_ext χ)

end indep_real

/-- **`¬CH` from ccc and independent bits.**  If `𝔹` is a nontrivial complete Boolean algebra
satisfying the countable chain condition and `χ : ℵ₂ → ℕ → 𝔹` is a family of independent bits,
then `V 𝔹 ⊨ ¬CH`. -/
theorem neg_CH_of_CCC_of_indep (H_ccc : CCC 𝔹)
    (χ : (check (PSet.pSet_aleph2) : bSet 𝔹).type → ℕ → 𝔹) (H_indep : IndepBits χ) :
    (⊤ : 𝔹) ≤ CHᶜ := by
  simp only [CH, compl_compl]
  exact le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 1)))
    (le_inf (Ord_card_ex _) (le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 2)))
      (le_inf (le_inf (aleph0_lt_aleph1_bSet_of_CCC H_ccc) (aleph1_lt_aleph2_bSet_of_CCC H_ccc))
        (le_iSup_of_le (indep_real.neg_CH_func χ)
          (indep_real.aleph2_le_powerset_omega χ H_indep)))))

theorem neg_CH₂_of_CCC_of_indep (H_ccc : CCC 𝔹)
    (χ : (check (PSet.pSet_aleph2) : bSet 𝔹).type → ℕ → 𝔹) (H_indep : IndepBits χ) :
    (⊤ : 𝔹) ≤ CH₂ᶜ :=
  (Lattice.bv_iff_neg CH_iff_CH₂).mp (neg_CH_of_CCC_of_indep H_ccc χ H_indep)

end indep_real

/-! ### The random algebra forces `¬CH` -/

section random

local notation "𝔹" => 𝔹_random

/-- The bits of the random reals, indexed by the type of `ℵ₂̌ `. -/
noncomputable def random_bits : (check (PSet.pSet_aleph2) : bSet 𝔹).type → ℕ → 𝔹 :=
  fun ν n => RandomAlgebra.χ (check_cast ν) n

lemma random_bits_indep : IndepBits random_bits := by
  intro ν₁ ν₂ H_neq
  apply le_of_eq
  apply RandomAlgebra.iInf_biimp_χ_eq_bot
  intro H
  exact H_neq ((cast_inj _).mp H)

/-- **The random algebra forces `¬CH`.** -/
theorem neg_CH_random : (⊤ : 𝔹) ≤ CHᶜ :=
  neg_CH_of_CCC_of_indep 𝔹_random_CCC random_bits random_bits_indep

theorem neg_CH₂_random : (⊤ : 𝔹) ≤ CH₂ᶜ :=
  neg_CH₂_of_CCC_of_indep 𝔹_random_CCC random_bits random_bits_indep

end random

end bSet

/-! ### `CH` is unprovable from `ZFC` — via the random algebra -/

open Fol bSet

/-- The Boolean-valued model `V 𝔹_random` of `ZFC` satisfies `¬CH_f`. -/
lemma V_𝔹_random_models_neg_CH : ⊤ ⊩[V 𝔹_random] (bd_not CH_f : sentence L_ZFC) := by
  rw [neg_CH_f_sound]; exact neg_CH₂_random

instance V_𝔹_random_nonempty : Nonempty (V 𝔹_random) := ⟨bSet.empty⟩

/-- **The Continuum Hypothesis is not provable from `ZFC`** — proved with the `ℵ₂`-random
algebra instead of the Cohen algebra. -/
theorem CH_f_unprovable_random : ¬ (ZFC ⊢ₛ' CH_f) :=
  unprovable_of_model_neg (V 𝔹_random) bSet_models_ZFC nontrivial_bot_lt_top
    V_𝔹_random_models_neg_CH

/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Bounded-overlap finite set families

This file isolates the combinatorial counting lemma behind Guth's surface
pruning argument.  If every member of a finite set family has at least `A`
elements and distinct members overlap in at most `B` elements, then the
family has at most `2|U|/A` members as soon as `A² > 4B|U|`.
-/

open scoped BigOperators

namespace Erdos95.SetFamilyBounds

/-- Number of indexed sets which contain `x`. -/
noncomputable def multiplicity {α ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (x : α) : ℕ := by
  classical
  exact (I.filter fun i ↦ x ∈ S i).card

theorem sum_card_eq_sum_multiplicity
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α)
    (hsub : ∀ i ∈ I, S i ⊆ U) :
    (∑ i ∈ I, (S i).card) = ∑ x ∈ U, multiplicity I S x := by
  classical
  calc
    (∑ i ∈ I, (S i).card) =
        ∑ i ∈ I, ∑ x ∈ U, if x ∈ S i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hfilter : U.filter (fun x ↦ x ∈ S i) = S i := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · exact fun hx ↦ ⟨hsub i hi hx, hx⟩
      calc
        (S i).card = (U.filter fun x ↦ x ∈ S i).card :=
          congrArg Finset.card hfilter.symm
        _ = ∑ x ∈ U, if x ∈ S i then 1 else 0 := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ U, ∑ i ∈ I, if x ∈ S i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ U, multiplicity I S x := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold multiplicity
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hxi : x ∈ S i <;> simp [hxi]

private theorem multiplicity_mul_pred_eq_double_sum
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (x : α) :
    multiplicity I S x * (multiplicity I S x - 1) =
      ∑ i ∈ I, ∑ j ∈ I,
        if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
  classical
  let J := I.filter fun i ↦ x ∈ S i
  let K := (I ×ˢ I).filter fun p ↦ p.1 ≠ p.2 ∧ x ∈ S p.1 ∧ x ∈ S p.2
  have hJK : J.offDiag = K := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product, J, K]
    tauto
  have hright :
      (∑ i ∈ I, ∑ j ∈ I,
        if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0) = K.card := by
    calc
      (∑ i ∈ I, ∑ j ∈ I,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0) =
          ∑ p ∈ I ×ˢ I,
            if p.1 ≠ p.2 ∧ x ∈ S p.1 ∧ x ∈ S p.2 then 1 else 0 := by
        symm
        exact Finset.sum_product I I _
      _ = K.card := by
        symm
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hright, ← hJK]
  rw [show multiplicity I S x = J.card by
    unfold multiplicity
    dsimp only [J]
    congr 1
    ext i
    simp]
  change J.card * (J.card - 1) = J.offDiag.card
  rw [Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib]
  simp

theorem sum_multiplicity_mul_pred_le
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α) (B : ℕ)
    (hoverlap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((S i).filter fun x ↦ x ∈ S j).card ≤ B) :
    (∑ x ∈ U, multiplicity I S x * (multiplicity I S x - 1)) ≤
      B * I.card * (I.card - 1) := by
  classical
  calc
    (∑ x ∈ U, multiplicity I S x * (multiplicity I S x - 1)) =
        ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact multiplicity_mul_pred_eq_double_sum I S x
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          if i ≠ j ∧ x ∈ S i ∧ x ∈ S j then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, if i ≠ j then B else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ne_eq, not_false_eq_true, if_true]
        have hfilter :
            (U.filter fun x ↦ x ∈ S i ∧ x ∈ S j).card ≤
              ((S i).filter fun x ↦ x ∈ S j).card := by
          apply Finset.card_le_card
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx'.2.1, hx'.2.2⟩
        have hsimple :
            (∑ x ∈ U, if x ∈ S i ∧ x ∈ S j then 1 else 0) ≤ B := by
          calc
          (∑ x ∈ U, if x ∈ S i ∧ x ∈ S j then 1 else 0) =
              (U.filter fun x ↦ x ∈ S i ∧ x ∈ S j).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          _ ≤ ((S i).filter fun x ↦ x ∈ S j).card := hfilter
          _ ≤ B := hoverlap i hi j hj hij
        simpa [hij] using hsimple
    _ = B * I.card * (I.card - 1) := by
      calc
        (∑ i ∈ I, ∑ j ∈ I, if i ≠ j then B else 0) =
            ∑ i ∈ I, B * (I.card - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfilter : I.filter (fun j ↦ i ≠ j) = I.erase i := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_erase]
            tauto
          calc
            (∑ j ∈ I, if i ≠ j then B else 0) =
                ∑ j ∈ I.filter (fun j ↦ i ≠ j), B := by
              rw [Finset.sum_filter]
            _ = ∑ _j ∈ I.erase i, B := by rw [hfilter]
            _ = B * (I.card - 1) := by
              simp [Finset.card_erase_of_mem hi, Nat.mul_comm]
        _ = B * I.card * (I.card - 1) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ac_rfl

/-- Guth's many-large-sets lemma, in a denominator-free form. -/
theorem large_family_bound
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (S : ι → Finset α)
    (A B : ℕ)
    (hsub : ∀ i ∈ I, S i ⊆ U)
    (hlarge : ∀ i ∈ I, A ≤ (S i).card)
    (hoverlap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((S i).filter fun x ↦ x ∈ S j).card ≤ B)
    (hquadratic : 4 * B * U.card < A ^ 2) :
    A * I.card ≤ 2 * U.card := by
  classical
  let k : α → ℕ := multiplicity I S
  let E : ℕ := ∑ x ∈ U, k x
  have hAE : A * I.card ≤ E := by
    rw [show E = ∑ i ∈ I, (S i).card by
      symm
      exact sum_card_eq_sum_multiplicity U I S hsub]
    calc
      A * I.card = ∑ _i ∈ I, A := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ I, (S i).card :=
        Finset.sum_le_sum fun i hi ↦ hlarge i hi
  by_contra hbound
  have htwoU : 2 * U.card < A * I.card := by omega
  have htwoUE : 2 * U.card < E := htwoU.trans_le hAE
  have hcs : (E : ℝ) ^ 2 ≤
      (U.card : ℝ) * ∑ x ∈ U, (k x : ℝ) ^ 2 := by
    simpa [E] using
      (sq_sum_le_card_mul_sum_sq (s := U) (f := fun x ↦ (k x : ℝ)))
  have hover := sum_multiplicity_mul_pred_le U I S B hoverlap
  have hsumSq : (∑ x ∈ U, (k x : ℝ) ^ 2) ≤
      (E : ℝ) + (B : ℝ) * I.card * I.card := by
    have hident : ∀ x, (k x : ℝ) ^ 2 =
        (k x : ℝ) + (k x * (k x - 1) : ℕ) := by
      intro x
      have hnat : ∀ n : ℕ, n ^ 2 = n + n * (n - 1) := by
        intro n
        cases n with
        | zero => simp
        | succ n => simp [Nat.succ_eq_add_one]; ring
      exact_mod_cast hnat (k x)
    have hover' :
        (∑ x ∈ U, k x * (k x - 1)) ≤ B * I.card * I.card := by
      exact hover.trans <| Nat.mul_le_mul_left (B * I.card) (Nat.sub_le I.card 1)
    calc
      (∑ x ∈ U, (k x : ℝ) ^ 2) =
          ∑ x ∈ U, ((k x : ℝ) + (k x * (k x - 1) : ℕ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hident x
      _ = E + (∑ x ∈ U, k x * (k x - 1) : ℕ) := by
        dsimp [E]
        push_cast
        rw [Finset.sum_add_distrib]
      _ ≤ (E : ℝ) + (B : ℝ) * I.card * I.card := by
        exact_mod_cast Nat.add_le_add_left hover' E
  have hEpos : 0 < (E : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt htwoUE)
  have htwoUER : (2 : ℝ) * U.card < E := by exact_mod_cast htwoUE
  have hU_lt_halfE : (U.card : ℝ) < E / 2 := by
    nlinarith
  have hmain : (E : ℝ) ^ 2 <
      (E : ℝ) ^ 2 / 2 + (U.card : ℝ) * B * I.card ^ 2 := by
    calc
      (E : ℝ) ^ 2 ≤ (U.card : ℝ) * ∑ x ∈ U, (k x : ℝ) ^ 2 := hcs
      _ ≤ (U.card : ℝ) *
          ((E : ℝ) + (B : ℝ) * I.card * I.card) := by gcongr
      _ = (U.card : ℝ) * E + (U.card : ℝ) * B * I.card ^ 2 := by ring
      _ < (E : ℝ) ^ 2 / 2 + (U.card : ℝ) * B * I.card ^ 2 := by
        nlinarith
  have hAI : (A : ℝ) * I.card ≤ E := by exact_mod_cast hAE
  have hquadR : 4 * (B : ℝ) * U.card < (A : ℝ) ^ 2 := by
    exact_mod_cast hquadratic
  have hIz : 0 < (I.card : ℝ) := by
    have hIcard : 0 < I.card := by
      by_contra hI
      have hIz : I.card = 0 := Nat.eq_zero_of_not_pos hI
      simp [hIz] at hbound
    exact_mod_cast hIcard
  have hAI_sq : ((A : ℝ) * I.card) ^ 2 ≤ (E : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hAI
  have hquadMul :
      4 * (B : ℝ) * U.card * (I.card : ℝ) ^ 2 <
        ((A : ℝ) * I.card) ^ 2 := by
    calc
      4 * (B : ℝ) * U.card * (I.card : ℝ) ^ 2 <
          (A : ℝ) ^ 2 * (I.card : ℝ) ^ 2 := by
        exact mul_lt_mul_of_pos_right hquadR (sq_pos_of_pos hIz)
      _ = ((A : ℝ) * I.card) ^ 2 := by ring
  nlinarith

end Erdos95.SetFamilyBounds

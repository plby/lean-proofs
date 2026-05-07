/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib

/-!
# Erdős Problem 867

Is it true that if `A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N}` has no solutions to
`aᵢ + aᵢ₊₁ + ⋯ + aⱼ ∈ A`, then `|A| ≤ N/2 + O(1)`?

## Answer

**No.** Freud (1993) constructed a consecutive-sum-free set achieving
density `19/36 > 1/2`. The current best bounds are due to
Coppersmith–Phillips (1996): `13N/24 - O(1) ≤ |A| ≤ (2/3 - 1/512)N + log N`.

## Main results

* `ConsecutiveSumFree`: the consecutive-sum-free property.
* `freudSet`: Freud's explicit construction with density `19/36`.
* `freudSet_csf`: proof that `freudSet` is consecutive-sum-free.
* `construction_19_36`: for all `N`, there exists a CSF subset of
  `{1, …, N}` of size `≥ 19N/36 - O(1)`.
* `csf_exceeds_half_plus_constant`: the conjecture `|A| ≤ N/2 + O(1)`
  is **false**.

## References

* R. Freud, *Adding numbers — on a problem of P. Erdős*,
  James Cook Mathematical Notes (1993), 6199–6202.
* [Erdős Problem #867](https://www.erdosproblems.com/867).
-/

namespace Erdos867

open Finset

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.induction false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.whitespace false
set_option maxHeartbeats 800000

/-! ## Definition -/

/-- A finset `S` of natural numbers is **consecutive-sum-free** if no element of `S`
equals the sum of two or more consecutive elements of `S` (when listed in increasing order).

Formally, for every contiguous sublist of length ≥ 2 of the sorted elements of `S`,
the sum of that sublist is not an element of `S`. -/
def ConsecutiveSumFree (S : Finset ℕ) : Prop :=
  ∀ (start len : ℕ), 2 ≤ len → start + len ≤ S.card →
    (((S.sort (· ≤ ·)).drop start).take len).sum ∉ S

/-- `ConsecutiveSumFree` is decidable for finite sets. -/
instance (S : Finset ℕ) : Decidable (ConsecutiveSumFree S) := by
  unfold ConsecutiveSumFree
  apply decidable_of_iff (∀ start ∈ Finset.range S.card, ∀ len ∈ Finset.Icc 2 S.card,
    start + len ≤ S.card → (((S.sort (· ≤ ·)).drop start).take len).sum ∉ S)
  constructor
  · intro h start len hlen hbound
    exact h start (mem_range.mpr (by omega)) len (mem_Icc.mpr ⟨hlen, by omega⟩) hbound
  · intro h start _ len hmem hbound
    exact h start len (by simp [mem_Icc] at hmem; exact hmem.1) hbound

/-! ## The 19/36 Construction -/

/-- Block A of Freud's construction: `[2x - 2y, 2x + 2y]`. -/
noncomputable def setA (x y : ℕ) : Finset ℕ := Finset.Icc (2*x - 2*y) (2*x + 2*y)

/-- Block B of Freud's construction: even numbers in `[2x + 2y + 2, 4x]`. -/
noncomputable def setB (x y : ℕ) : Finset ℕ :=
  (Finset.Icc (3*x - 3*y + 1) (3*x + 3*y - 1)).filter (fun k => ¬ 3 ∣ k)

/-- Block C of Freud's construction: odd numbers in `[4x + 1, 4x + 4y + 1]`. -/
noncomputable def setC (x y : ℕ) : Finset ℕ :=
  (Finset.Icc (4*x - 4*y + 2) (4*x + 4*y - 2)).filter (fun k => 2 ∣ k)

/-- Block D of Freud's construction: `[4x + 4y + 2, 8x + 8y + 4]`. -/
noncomputable def setD (x y : ℕ) : Finset ℕ := Finset.Icc (4*x + 4*y + 2) (8*x + 8*y + 4)

/-- The Freud construction set achieving density 19/36, parametrized by y ≥ 1.
  With x = 17y - 2, we take:
  - A = {32y-4, ..., 36y-4} (4y+1 consecutive integers)
  - B = non-multiples of 3 in {48y-5, ..., 54y-7} (4y elements)
  - C = even numbers in {64y-6, ..., 72y-10} (4y-1 elements)
  - D = {72y-6, ..., 144y-12} minus deleted elements (64y-7 elements)
  Total: 76y-7 elements in {1, ..., 144y-12}. -/
def freudSet (y : ℕ) : Finset ℕ :=
  let A := Finset.Icc (32 * y - 4) (36 * y - 4)
  let B := (Finset.Icc (48 * y - 5) (54 * y - 7)).filter (fun k => ¬(3 ∣ k))
  let C := (Finset.Icc (64 * y - 6) (72 * y - 10)).filter (fun k => 2 ∣ k)
  let D := Finset.Icc (72 * y - 6) (144 * y - 12)
  let del := (Finset.Icc (96 * y - 9) (108 * y - 15)).filter (fun k => 3 ∣ k) ∪
             (Finset.Icc (128 * y - 10) (144 * y - 22)).filter (fun k => k % 4 = 2) ∪
             ({84 * y - 9, 120 * y - 14, 132 * y - 13, 118 * y - 13, 144 * y - 16} : Finset ℕ)
  A ∪ B ∪ C ∪ (D \ del)

lemma freudSet_subset (y : ℕ) (hy : 1 ≤ y) : freudSet y ⊆ Icc 1 (144*y-12) := by
  intro x hx; unfold freudSet at hx; simp_all +arith +decide; omega

lemma freudSet_card (y : ℕ) (hy : 1 ≤ y) :
    (freudSet y).card = 76 * y - 7 := by
  unfold freudSet
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr]
    · rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint] <;> norm_num
      · have hA : (Icc (32*y-4) (36*y-4)).card = 4*y+1 := by
          rcases y with (_ | _ | y) <;> simp +arith +decide [Nat.mul_succ] at *
          exact Nat.sub_eq_of_eq_add <| by ring
        have hB : ((Icc (48*y-5) (54*y-7)).filter (fun k => ¬3 ∣ k)).card = 4*y := by
          rw [Finset.filter_not, Finset.card_sdiff]; norm_num
          have key : (Icc (48*y-5) (54*y-7)).filter (Dvd.dvd 3) ∩ Icc (48*y-5) (54*y-7) =
              Finset.image (3 * ·) (Icc ((48*y-5+2)/3) ((54*y-7)/3)) := by
            ext; simp +decide [Nat.dvd_iff_mod_eq_zero]
            exact ⟨fun h => ⟨‹_›/3, ⟨by omega, by omega⟩, by omega⟩, by omega⟩
          rw [key, Finset.card_image_of_injective] <;> norm_num [Function.Injective]; lia
        have hC : ((Icc (64*y-6) (72*y-10)).filter (2 ∣ ·)).card = 4*y-1 := by
          have key : {k ∈ Icc (64*y-6) (72*y-10) | 2 ∣ k} =
              Finset.image (2 * ·) (Icc (32*y-3) (36*y-5)) := by
            ext; simp +decide [Nat.dvd_iff_mod_eq_zero]
            exact ⟨fun h => ⟨‹_›/2, ⟨by omega, by omega⟩, by omega⟩,
              by rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩; exact ⟨⟨by omega, by omega⟩, by omega⟩⟩
          rw [key, Finset.card_image_of_injective] <;> norm_num [Function.Injective]; omega
        have hD : (Icc (72*y-6) (144*y-12)).card = 72*y-5 := by
          simp +zetaDelta at *; omega
        have hDelI : ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·)).card = 4*y-1 := by
          have key : {k ∈ Icc (96*y-9) (108*y-15) | 3 ∣ k} =
              Finset.image (3 * ·) (Icc (32*y-3) (36*y-5)) := by
            ext; simp +zetaDelta at *
            exact ⟨fun h => ⟨‹_›/3, ⟨by omega, by omega⟩, by omega⟩,
              fun ⟨a, ⟨ha₁, ha₂⟩, ha₃⟩ => ⟨⟨by omega, by omega⟩, by omega⟩⟩
          rw [key, Finset.card_image_of_injective] <;> norm_num [Function.Injective]; omega
        have hDelIII : ((Icc (128*y-10) (144*y-22)).filter (· % 4 = 2)).card = 4*y-2 := by
          rw [Finset.card_eq_of_bijective]
          use fun i _ => 128*y-10 + 4*i
          · simp +zetaDelta at *
            exact fun a ha₁ ha₂ ha₃ => ⟨(a-(128*y-10))/4, by omega, by omega⟩
          · norm_num +zetaDelta at *; exact fun i hi => ⟨by omega, by omega⟩
          · grind
        have hDelV : ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ).card = 5 := by
          rcases y with (_ | _ | y) <;> simp +arith +decide [Nat.mul_succ] at *
        omega
      · norm_num [Finset.disjoint_left]; lia
      · omega
    · intro k hk; simp +zetaDelta at *; omega
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
      linarith [Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp (Finset.mem_filter.mp hx₂ |>.1),
        Nat.sub_add_cancel (show 4 ≤ 32*y by linarith),
        Nat.sub_add_cancel (show 4 ≤ 36*y by linarith),
        Nat.sub_add_cancel (show 5 ≤ 48*y by linarith),
        Nat.sub_add_cancel (show 7 ≤ 54*y by linarith)]
  · norm_num [Finset.disjoint_left]; omega
  · rw [Finset.disjoint_left]; simp +arith +decide [Finset.mem_union, Finset.mem_Icc]; omega

/-- A sorted finset is CSF if no contiguous subsum lands in the set. -/
lemma csf_of_no_interval_sum (S : Finset ℕ)
    (h : ∀ a b : ℕ, (S.filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2 →
      (S.filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∉ S) :
    ConsecutiveSumFree S := by
  intro S' len hlen hS'
  set a := (S.sort (· ≤ ·))[S']!
  set b := (S.sort (· ≤ ·))[S' + len - 1]!
  have h_filter : S.filter (fun x => a ≤ x ∧ x ≤ b) =
      (List.take len (List.drop S' (S.sort (· ≤ ·)))).toFinset := by
    ext x; constructor
    · intro hx
      obtain ⟨i, hi⟩ : ∃ i, i < S.card ∧ (S.sort (· ≤ ·))[i]! = x := by
        have : x ∈ S.sort (· ≤ ·) := by aesop
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp this; grind +suggestions
      have h_index : S' ≤ i ∧ i < S' + len := by
        have h_index : ∀ i j : ℕ, i < j → j < S.card →
            (S.sort (· ≤ ·))[i]! ≤ (S.sort (· ≤ ·))[j]! := by
          intros i j hij hj
          have h_sorted : List.Pairwise (fun x y => x ≤ y) (S.sort (· ≤ ·)) :=
            Finset.pairwise_sort _ _
          have := List.pairwise_iff_get.mp h_sorted
          convert this ⟨i, by simpa using by linarith⟩ ⟨j, by simpa using by linarith⟩ hij
          · grind
          · grind
        have h_distinct : List.Nodup (S.sort (· ≤ ·)) := Finset.sort_nodup _ _
        grind +suggestions
      simp +zetaDelta at *
      rw [List.mem_iff_get]
      use ⟨i - S', by simp +arith +decide; omega⟩
      generalize_proofs at *; grind
    · intro hx
      obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range len, x = (S.sort (· ≤ ·))[S' + i]! := by
        rw [List.mem_toFinset, List.mem_iff_get] at hx
        obtain ⟨n, hn⟩ := hx; use n; simp_all +decide
        exact ⟨by simpa using n.2.trans_le (by simp),
          by rw [← hn, List.getElem?_eq_getElem]; aesop⟩
      have h_sorted : ∀ i j : ℕ, i < j → i < (S.sort (· ≤ ·)).length →
          j < (S.sort (· ≤ ·)).length → (S.sort (· ≤ ·))[i]! ≤ (S.sort (· ≤ ·))[j]! := by
        intros i j hij hi hj
        have h_pw : List.Pairwise (fun x y => x ≤ y) (S.sort (· ≤ ·)) :=
          Finset.pairwise_sort _ _
        convert List.pairwise_iff_get.mp h_pw ⟨i, hi⟩ ⟨j, hj⟩ hij using 1 <;> grind
      simp +zetaDelta at *
      refine' ⟨_, _, _⟩
      · convert Finset.mem_sort (α := ℕ) (· ≤ ·) |>.1 _
        exact List.mem_of_mem_take hx |> List.mem_of_mem_drop
      · by_cases hi' : i = 0
        · aesop
        · exact hi.2.symm ▸ h_sorted _ _ (by omega) (by omega) (by omega)
      · by_cases hi' : i = len - 1
        · cases len <;> aesop
        · exact hi.2.symm ▸ h_sorted _ _ (by omega) (by omega) (by omega)
  convert h a b _ using 1
  · rw [h_filter, List.sum_toFinset]
    · norm_num
    · exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup (Finset.sort_nodup _ _))
  · rw [h_filter, List.toFinset_card_of_nodup]
    · simp +zetaDelta at *; omega
    · exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup (Finset.sort_nodup _ _))

/-- Every element of `freudSet y` is at least `32y - 4`. -/
lemma freudSet_min_elem (y : ℕ) (_hy : 1 ≤ y) (x : ℕ) (hx : x ∈ freudSet y) :
    32*y-4 ≤ x := by
  unfold freudSet at hx; simp +zetaDelta at *; omega

/-- Any contiguous subsum of `freudSet y` of length `≥ 2` exceeds `4y + 2`, the maximum of
block A. -/
lemma freudSet_interval_sum_lb (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2) :
    64 * y - 7 ≤ ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id := by
  have h_lower_bound : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), 32 * y - 4 ≤ x :=
    fun x hx => freudSet_min_elem y hy x <| Finset.filter_subset _ _ hx
  obtain ⟨x1, x2, hx1, hx2, hlt⟩ : ∃ x1 x2 : ℕ,
      x1 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) ∧
      x2 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) ∧ x1 < x2 := by
    obtain ⟨x1, hx1, x2, hx2, hne⟩ := Finset.one_lt_card.1 hcard
    cases lt_trichotomy x1 x2 <;> aesop
  refine' le_trans _ (Finset.sum_le_sum_of_subset
    (Finset.insert_subset hx1 (Finset.singleton_subset_iff.mpr hx2)))
  grind

/-- No contiguous subsum of `freudSet y` lands in block C. -/
lemma freudSet_interval_sum_not_in_C (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2)
    (hs : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      (Icc (64*y-6) (72*y-10)).filter (2 ∣ ·)) : False := by
  have hT_subset : {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ⊆ Icc (32*y-4) (36*y-4) := by
    intro x hx; simp_all +decide
    have hT_le : x ≤ 48*y-6 := by
      have : ∑ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), x ≥ 32*y-4 + x := by
        obtain ⟨z, hz₁, hz₂, hz₃⟩ : ∃ z ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b),
            z ≠ x ∧ z ≥ 32*y-4 := by
          obtain ⟨z, hz⟩ := Finset.exists_mem_ne hcard x
          exact ⟨z, hz.1, hz.2, freudSet_min_elem y hy z (Finset.mem_filter.mp hz.1 |>.1)⟩
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hz₁]
        exact add_le_add hz₃ (Finset.single_le_sum (fun x _ => Nat.zero_le x) (by aesop))
      omega
    unfold freudSet at hx; simp_all +decide; omega
  by_cases hT_card : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).card ≥ 3
  · have hT_sum_ge : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).sum id ≥ 3*(32*y-4) + 3 := by
      obtain ⟨x_seq, hx_seq⟩ : ∃ x_seq : Fin ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).card → ℕ,
          StrictMono x_seq ∧
          ∀ i, x_seq i ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) := by
        exact ⟨fun i => Finset.orderEmbOfFin _ (by aesop) i, by aesop_cat,
          fun i => Finset.orderEmbOfFin_mem _ (by aesop) _⟩
      have hx_seq_ge : ∀ i, x_seq i ≥ 32*y-4 + i := by
        intro i; induction' i with i ih; induction' i with i ih
        · exact Finset.mem_Icc.mp (hT_subset (hx_seq.2 _)) |>.1
        · exact lt_of_le_of_lt
            (‹∀ (ih : i < ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card),
              x_seq ⟨i, ih⟩ ≥ 32*y-4 + i› (Nat.lt_of_succ_lt ih))
            (hx_seq.1 (Nat.lt_succ_self _))
      have hT_sum_ge : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).sum id ≥
          ∑ i ∈ Finset.range ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).card, (32*y-4 + i) := by
        have : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).sum id ≥
            ∑ i ∈ Finset.univ.image x_seq, i :=
          Finset.sum_le_sum_of_subset (Finset.image_subset_iff.mpr fun i _ => hx_seq.2 i)
        rw [Finset.sum_image <| by intros i _ j _ hij; exact hx_seq.1.injective hij] at this
        simpa [Finset.sum_range] using this.trans' <| Finset.sum_le_sum fun i _ => hx_seq_ge i
      refine le_trans ?_ hT_sum_ge
      rcases n : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card
        with (_ | _ | _ | n) <;>
        simp_all +arith +decide [Finset.sum_range_succ']
    norm_num at *; omega
  · interval_cases _ : #({x ∈ freudSet y | a ≤ x ∧ x ≤ b})
    simp_all +decide
    rw [Finset.card_eq_two] at *
    obtain ⟨x, y, hxy, h⟩ := ‹_›
    cases lt_or_gt_of_ne hxy <;> simp_all +decide [Finset.ext_iff]
    · have := h x; have := h y; simp_all +decide [Finset.subset_iff]
      have := h (x + 1); simp_all +decide [freudSet]; grind
    · have := h x; have := h y; simp_all +decide [Finset.subset_iff]
      have := h (y + 1); simp_all +decide [freudSet]; grind +ring

/-- If all summands come from block A, the subsum exceeds `4y + 2` and thus cannot land in A. -/
lemma freudSet_interval_sum_all_in_A (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2)
    (hall : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), x ≤ 36*y-4)
    (hs_in_D : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈ Icc (72*y-6) (144*y-12))
    (hs_not_del : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∉
      ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·) ∪
       (Icc (128*y-10) (144*y-22)).filter (· % 4 = 2) ∪
       ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ))) :
    False := by
  have hT_eq : {x ∈ freudSet y | a ≤ x ∧ x ≤ b} = Icc (max a (32*y-4)) (min b (36*y-4)) := by
    ext x; simp [Finset.mem_filter, Finset.mem_Icc]; constructor <;> intro hx
    · exact ⟨⟨hx.2.1, by have := freudSet_min_elem y hy x hx.1; omega⟩, hx.2.2,
        hall x <| by aesop⟩
    · unfold freudSet; simp +decide [hx]
  simp_all +decide
  have h_sum_formula : ∑ x ∈ Icc (max a (32*y-4)) (min b (36*y-4)), x =
      (min b (36*y-4) - max a (32*y-4) + 1) * (max a (32*y-4) + min b (36*y-4)) / 2 := by
    erw [Finset.sum_Ico_eq_sum_range]
    rw [Nat.div_eq_of_eq_mul_left zero_lt_two, Finset.sum_add_distrib]
    norm_num [Nat.sub_add_comm (show max a (32*y-4) ≤ min b (36*y-4) from
      le_of_lt (Nat.lt_of_sub_pos (by omega)))]
    nlinarith! only [Finset.sum_range_id_mul_two (min b (36*y-4) - max a (32*y-4) + 1),
      Nat.sub_add_cancel (show max a (32*y-4) ≤ min b (36*y-4) from
        le_of_lt (Nat.lt_of_sub_pos (by omega)))]
  by_cases hT_card : min b (36*y-4) - max a (32*y-4) + 1 ≤ 4
  · interval_cases _ : min b (36*y-4) - max a (32*y-4) + 1 <;>
      simp_all +decide only [Nat.mul_comm] <;> omega
  · have h_sum_ge : ∑ x ∈ Icc (max a (32*y-4)) (min b (36*y-4)), x ≥ 5*(32*y-4) + 10 := by
      have : ∑ x ∈ Icc (max a (32*y-4)) (min b (36*y-4)), x ≥
          ∑ x ∈ Finset.range (min b (36*y-4) - max a (32*y-4) + 1), (max a (32*y-4) + x) := by
        erw [Finset.sum_Ico_eq_sum_range]; rw [Nat.sub_add_comm (by omega)]
      refine le_trans ?_ this
      refine' le_trans _ (Finset.sum_le_sum_of_subset
        (Finset.range_mono (show min b (36*y-4) - max a (32*y-4) + 1 ≥ 5 by linarith)))
      simp +arith +decide [Finset.sum]
    omega

/-- Blocks A and B are contiguous in `freudSet y`. -/
lemma freudSet_no_gap_AB (y : ℕ) (hy : 1 ≤ y) (x : ℕ) (hx : x ∈ freudSet y)
    (h1 : 36*y-3 ≤ x) (h2 : x ≤ 48*y-6) : False := by
  unfold freudSet at hx; simp_all +decide; omega

/-- Blocks B and C are contiguous in `freudSet y`. -/
lemma freudSet_no_gap_BC (y : ℕ) (hy : 1 ≤ y) (x : ℕ) (hx : x ∈ freudSet y)
    (h1 : 54*y-6 ≤ x) (h2 : x ≤ 64*y-7) : False := by
  unfold freudSet at hx; simp_all +decide; omega

/-- Blocks C and D are contiguous in `freudSet y`. -/
lemma freudSet_no_gap_CD (y : ℕ) (hy : 1 ≤ y) (x : ℕ) (hx : x ∈ freudSet y)
    (h1 : 72*y-9 ≤ x) (h2 : x ≤ 72*y-7) : False := by
  unfold freudSet at hx; simp_all +decide; omega

/-- `4y + 2` is in block B (the `3·(2y)/6` element). -/
lemma freudSet_mem_36 (y : ℕ) (hy : 1 ≤ y) : 36*y-4 ∈ freudSet y := by
  unfold freudSet; simp +decide; omega

/-- `4y + 4` is in block D. -/
lemma freudSet_mem_48 (y : ℕ) (hy : 1 ≤ y) : 48*y-5 ∈ freudSet y := by
  unfold freudSet; simp +decide; omega

/-- `4y + 4` equals `4(y+1)`. -/
lemma freudSet_mem_48_4 (y : ℕ) (hy : 1 ≤ y) : 48*y-4 ∈ freudSet y := by
  unfold freudSet; simp +decide; omega

/-- `4y + 3` is not in `freudSet y` (it falls in the gap between C and D). -/
lemma freudSet_nmem_48_3 (y : ℕ) (hy : 1 ≤ y) : 48*y-3 ∉ freudSet y := by
  unfold freudSet; simp +decide; omega


/-- A contiguous subsum of `≥ 3` elements all from D exceeds the maximum of `freudSet y`. -/
lemma freudSet_all_ge48_card3_sum_gt (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 3)
    (hall : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), 48*y-5 ≤ x) :
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id > 144*y-12 := by
  obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hx_distinct⟩ : ∃ x₁ x₂ x₃ : ℕ,
      x₁ ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ∧ x₂ ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ∧
      x₃ ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ∧ x₁ < x₂ ∧ x₂ < x₃ := by
    obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq hcard
    obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃⟩ : ∃ x₁ x₂ x₃,
        x₁ ∈ s ∧ x₂ ∈ s ∧ x₃ ∈ s ∧ x₁ < x₂ ∧ x₂ < x₃ := by
      rcases Finset.card_eq_three.mp hs.2 with ⟨x₁, x₂, x₃, h₁, h₂, h₃⟩
      cases lt_trichotomy x₁ x₂ <;> cases lt_trichotomy x₂ x₃ <;>
        cases lt_trichotomy x₁ x₃ <;> aesop
    exact ⟨x₁, x₂, x₃, hs.1 hx₁, hs.1 hx₂, hs.1 hx₃.1, hx₃.2.1, hx₃.2.2⟩
  have hx1_ge : 48*y-5 ≤ x₁ := hall x₁ hx₁
  have hx2_ge : 48*y-4 ≤ x₂ := by omega
  have hx3_ge : 48*y-2 ≤ x₃ := by
    by_contra h_contra
    exact (show x₃ = 48*y-3 by omega).symm ▸ freudSet_nmem_48_3 y hy <|
      Finset.mem_filter.mp hx₃ |>.1
  have h_sum_ge : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).sum id ≥ ({x₁, x₂, x₃} : Finset ℕ).sum id :=
    Finset.sum_le_sum_of_subset (Finset.insert_subset_iff.mpr
      ⟨hx₁, Finset.insert_subset_iff.mpr ⟨hx₂, Finset.singleton_subset_iff.mpr hx₃⟩⟩)
  grind

/-- A pair of adjacent elements from D sums to a value not in `freudSet y`. -/
lemma freudSet_adj_pair_ge48_sum (y : ℕ) (hy : 1 ≤ y) (x₁ x₂ : ℕ)
    (hx₁ : x₁ ∈ freudSet y) (hx₂ : x₂ ∈ freudSet y)
    (hge₁ : 48*y-5 ≤ x₁) (hlt : x₁ < x₂)
    (hadj : ∀ z ∈ freudSet y, x₁ < z → z < x₂ → False) :
    x₁ + x₂ ∈ ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·) ∪
      (Icc (128*y-10) (144*y-22)).filter (· % 4 = 2) ∪
      ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ)) ∨
    x₁ + x₂ > 144*y-12 := by
  by_cases hx1_B : x₁ ∈ (Icc (48*y-5) (54*y-7)).filter (fun k => ¬(3 ∣ k))
  · by_cases hx2_le : x₂ ≤ 54*y-7
    · have h_sum_div3 : 3 ∣ (x₁ + x₂) := by
        have : ¬(3 ∣ x₁) ∧ ¬(3 ∣ x₂) ∧ x₂ = x₁ + 1 ∨
            ¬(3 ∣ x₁) ∧ ¬(3 ∣ x₂) ∧ x₂ = x₁ + 2 := by
          have h_adj_B : x₂ ≤ x₁ + 2 := by
            contrapose! hadj
            use if x₁ + 1 ∈ (Icc (48*y-5) (54*y-7)).filter (fun k => ¬3 ∣ k)
              then x₁ + 1 else x₁ + 2
            grind +locals
          cases h_adj_B.eq_or_lt <;> simp_all +arith +decide
          · unfold freudSet at hx₂; simp_all +arith +decide; omega
          · exact Or.inl ⟨by unfold freudSet at hx₂; simp_all +arith +decide; omega, by linarith⟩
        grind +extAll
      simp +zetaDelta at *
      exact Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl ⟨⟨by omega, by omega⟩, h_sum_div3⟩
    · have hx2_eq : x₂ = 64*y-6 := by
        contrapose! hadj; use 64*y-6
        refine' ⟨_, _, _, trivial⟩
        · unfold freudSet; simp +decide [*]; exact Or.inr <| Or.inr <| Or.inl ⟨by omega, by omega⟩
        · simp +zetaDelta at *; omega
        · exact lt_of_le_of_ne (Nat.le_of_not_lt fun h => by
            have := freudSet_no_gap_BC y hy x₂ hx₂ (by omega) (by omega); contradiction)
            (Ne.symm hadj)
      have hx1_eq : x₁ = 54*y-7 := by
        contrapose! hadj; use 54*y-7; simp_all +decide [freudSet]; omega
      simp_all +decide [Nat.dvd_iff_mod_eq_zero]; omega
  · by_cases hx1_C : x₁ ∈ (Icc (64*y-6) (72*y-10)).filter (2 ∣ ·)
    · by_cases hx2_D : x₂ ≥ 72*y-6
      · by_cases hx2_C : x₂ ≤ 72*y-10
        · omega
        · have hx2_eq : x₂ = 72*y-6 := by
            contrapose! hadj; use 72*y-6
            unfold freudSet; simp_all +decide [Finset.mem_union, Finset.mem_Icc]; omega
          have hx1_eq : x₁ = 72*y-10 := by
            contrapose! hadj; use 72*y-10; simp_all +decide [freudSet]; omega
          simp_all +decide [Nat.dvd_iff_mod_eq_zero]; omega
      · have hx2_C : x₂ ∈ (Icc (64*y-6) (72*y-10)).filter (2 ∣ ·) := by
          unfold freudSet at hx₂; simp_all +decide; omega
        have hx2_eq_x1_plus_2 : x₂ = x₁ + 2 := by
          simp +zetaDelta at *
          exact le_antisymm (hadj (x₁ + 2)
            (by unfold freudSet; simp +decide [*]; omega) (by linarith)) (by omega)
        simp_all +decide [Nat.dvd_iff_mod_eq_zero]; omega
    · have hx1_D : x₁ ∈ Icc (72*y-6) (144*y-12) := by grind +locals
      exact Or.inr (by norm_num at *; omega)


/-- A pair of elements from D sums to a value not in `freudSet y`. -/
lemma freudSet_all_ge48_card2_sum (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card = 2)
    (hall : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), 48*y-5 ≤ x) :
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·) ∪ (Icc (128*y-10) (144*y-22)).filter (· % 4 = 2) ∪
       ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ)) ∨
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id > 144*y-12 := by
  obtain ⟨x₁, x₂, hne, heq⟩ := Finset.card_eq_two.mp hcard
  cases lt_or_gt_of_ne hne <;> simp_all +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
  · convert freudSet_adj_pair_ge48_sum y hy x₁ x₂ heq.2.1.1 heq.2.2.1
      (by omega) (by omega) _ using 1
    · rw [show (freudSet y |> Finset.filter fun x => a ≤ x ∧ x ≤ b) = {x₁, x₂} by ext; aesop]
      simp +decide [*]
    · rw [show (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) = {x₁, x₂} by aesop]
      simp +decide [*]
    · grind +ring
  · have h_adj : x₂ + x₁ ∈ ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·) ∪
        (Icc (128*y-10) (144*y-22)).filter (· % 4 = 2) ∪
        ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ)) ∨
        x₂ + x₁ > 144*y-12 := by
      apply freudSet_adj_pair_ge48_sum y hy x₂ x₁ <;> first | tauto | omega | grind
    rw [show (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) = {x₁, x₂} by ext; aesop]
    simp_all +decide [add_comm]

/-- A cross-block subsum of `≥ 4` elements spanning A and B exceeds the maximum of
`freudSet y`. -/
lemma freudSet_cross_AB_card4_sum_gt (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 4)
    (h36 : 36*y-4 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b))
    (h48 : 48*y-5 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)) :
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id > 144*y-12 := by
  have h_third : (36*y-5) ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ∨
      (48*y-4) ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} := by
    by_contra h_contra
    obtain ⟨x, hx⟩ : ∃ x ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b},
        x < 36*y-4 ∨ x > 48*y-5 := by
      by_cases h_cases : ∀ x ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b}, x = 36*y-4 ∨ x = 48*y-5
      · exact absurd (Finset.card_le_card (show {x ∈ freudSet y | a ≤ x ∧ x ≤ b} ⊆
            {36*y-4, 48*y-5} by intros x hx; simpa using h_cases x hx))
          (by rw [Finset.card_insert_of_notMem, Finset.card_singleton] <;> norm_num <;> omega)
      · push Not at h_cases; obtain ⟨x, hx₁, hx₂, hx₃⟩ := h_cases
        use x; simp_all +decide
        exact Classical.or_iff_not_imp_left.2 fun h =>
          lt_of_le_of_ne (le_of_not_gt fun h' => by
            have := freudSet_no_gap_AB y hy x hx₁.1 (by omega) (by omega); omega)
            (Ne.symm hx₃)
    cases hx.2 <;> simp_all +decide [Finset.mem_filter]
    · grind +locals
    · exact absurd (h_contra.2 (freudSet_mem_48_4 y hy) (by omega)) (by omega)
  obtain h | h := h_third
  · have h_three_elements : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b}).sum id ≥
        ({36*y-5, 36*y-4, 48*y-5} : Finset ℕ).sum id + 32*y-4 := by
      have h_sdiff_ge : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b} \
          {36*y-5, 36*y-4, 48*y-5}).sum id ≥ 32*y-4 := by
        have ⟨x, hx, hxge⟩ : ∃ x ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} \
            {36*y-5, 36*y-4, 48*y-5}, x ≥ 32*y-4 := by
          have : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b} \ {36*y-5, 36*y-4, 48*y-5}).card ≥ 1 := by
            grind
          exact Exists.elim (Finset.card_pos.mp this) fun x hx =>
            ⟨x, hx, freudSet_min_elem y hy x (Finset.mem_sdiff.mp hx |>.1 |>
              Finset.mem_filter.mp |>.1)⟩
        exact le_trans hxge (Finset.single_le_sum (fun x _ => Nat.zero_le x) hx)
      rw [← Finset.sum_sdiff (show {36*y-5, 36*y-4, 48*y-5} ⊆
          {x ∈ freudSet y | a ≤ x ∧ x ≤ b} from by aesop_cat)]
      grind
    grind +qlia
  · obtain ⟨u, hu⟩ : ∃ u ∈ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} \
        ({36*y-4, 48*y-5, 48*y-4} : Finset ℕ), True := by
      have : ({x ∈ freudSet y | a ≤ x ∧ x ≤ b} \
          ({36*y-4, 48*y-5, 48*y-4} : Finset ℕ)).card ≥ 1 := by grind
      exact Exists.elim (Finset.card_pos.mp this) fun x hx => ⟨x, hx, trivial⟩
    refine' lt_of_lt_of_le _ (Finset.sum_le_sum_of_subset <|
      show {36*y-4, 48*y-5, 48*y-4, u} ⊆ {x ∈ freudSet y | a ≤ x ∧ x ≤ b} from _)
    · rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert] <;> simp +arith +decide at *
      · have := freudSet_min_elem y hy u hu.1.1; omega
      · tauto
      · omega
      · omega
    · simp_all +decide [Finset.subset_iff]

/-- A cross-block subsum of 3 elements spanning A and B lands in the
gap between C and D. -/
lemma freudSet_cross_AB_card3_sum_in_del (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card = 3)
    (h36 : 36*y-4 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b))
    (h48 : 48*y-5 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)) :
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ) := by
  have h_third : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b),
      x = 36*y-4 ∨ x = 48*y-5 ∨ x = 36*y-5 ∨ x = 48*y-4 := by
    intro x hx
    by_cases hx_lower : x < 36*y-4
    · by_cases hx_lower : x < 36*y-5
      · have h_contradiction :
            ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 4 := by
          refine' le_trans _ (Finset.card_mono <|
            show {x, 36*y-5, 36*y-4, 48*y-5} ⊆
              (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) from _)
          · grind
          · simp_all +decide [Finset.insert_subset_iff]
            unfold freudSet; simp +decide; omega
        linarith
      · omega
    · by_cases hx_upper : x > 48*y-5
      · have h_adjacent : ∀ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b),
            x > 48*y-5 → x = 48*y-4 ∨ x > 48*y-4 := by
          intros x _ hx_upper; contrapose! hx_upper; omega
        contrapose! hcard
        refine' ne_of_gt (lt_of_lt_of_le _ (Finset.card_mono <|
          show {36*y-4, 48*y-5, x, 48*y-4} ⊆
            {x ∈ freudSet y | a ≤ x ∧ x ≤ b} from _))
        · grind
        · simp_all +decide [Finset.insert_subset_iff]
          exact ⟨freudSet_mem_48_4 y hy, by omega, by omega⟩
      · contrapose! hx_upper; simp_all +decide [freudSet]; omega
  rw [Finset.card_eq_three] at hcard
  obtain ⟨x, y, z, hxy, hxz, hyz, h⟩ := hcard
  simp_all +decide [Finset.ext_iff]
  rw [show (freudSet _).filter (fun x => a ≤ x ∧ x ≤ b) = {x, y, z} by ext; aesop]
  simp +decide [*, Finset.sum_singleton]; omega

/-- A cross-block pair from A and B sums to a value not in `freudSet y`. -/
lemma freudSet_cross_AB_card2_sum_in_del (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card = 2)
    (h36 : 36*y-4 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b))
    (h48 : 48*y-5 ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)) :
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ) := by
  rw [Finset.card_eq_two] at hcard; grind

/-- Any contiguous subsum whose elements span blocks A–B or lie
entirely in D does not land in `freudSet y`. -/
lemma freudSet_interval_sum_cross_AB_or_all_ge_48 (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2)
    (hhi : ∃ x ∈ (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b), 48*y-5 ≤ x)
    (hs_in_D : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      Finset.Icc (72*y-6) (144*y-12))
    (hs_not_del : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∉
      ((Finset.Icc (96*y-9) (108*y-15)).filter (fun k => 3 ∣ k) ∪
       (Finset.Icc (128*y-10) (144*y-22)).filter (fun k => k % 4 = 2) ∪
       ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ))) :
    False := by
  obtain ⟨z, hz, hzge⟩ := hhi
  have hz_mem := Finset.filter_subset _ _ hz
  have hs_le := (Finset.mem_Icc.mp hs_in_D).2
  set T := (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b) with hT
  by_cases hall : ∀ x ∈ T, 48*y-5 ≤ x
  · by_cases h3 : T.card ≥ 3
    · exact absurd hs_le (not_le.mpr (freudSet_all_ge48_card3_sum_gt y hy a b h3 hall))
    · have hcard2 : T.card = 2 := by omega
      rcases freudSet_all_ge48_card2_sum y hy a b hcard2 hall with hdel | hgt
      · exact hs_not_del hdel
      · exact absurd hs_le (not_le.mpr hgt)
  · push Not at hall; obtain ⟨w, hw, hwlt⟩ := hall
    have hw_mem := Finset.filter_subset _ _ hw
    have hwle : w ≤ 36*y-4 := by
      by_contra h; push Not at h
      exact freudSet_no_gap_AB y hy w hw_mem (by omega) (by omega)
    have hab_w := (Finset.mem_filter.mp hw).2
    have hab_z := (Finset.mem_filter.mp hz).2
    have h36 : 36*y-4 ∈ T :=
      Finset.mem_filter.mpr ⟨freudSet_mem_36 y hy, by omega, by omega⟩
    have h48 : 48*y-5 ∈ T :=
      Finset.mem_filter.mpr ⟨freudSet_mem_48 y hy, by omega, by omega⟩
    by_cases h4 : T.card ≥ 4
    · exact absurd hs_le (not_le.mpr (freudSet_cross_AB_card4_sum_gt y hy a b h4 h36 h48))
    · by_cases h3 : T.card ≥ 3
      · have hcard3 : T.card = 3 := by omega
        exact hs_not_del (Finset.mem_union_right _ <|
          freudSet_cross_AB_card3_sum_in_del y hy a b hcard3 h36 h48)
      · have hcard2 : T.card = 2 := by omega
        exact hs_not_del (Finset.mem_union_right _ <|
          freudSet_cross_AB_card2_sum_in_del y hy a b hcard2 h36 h48)

/-- No contiguous subsum of `freudSet y` lands in block D. -/
lemma freudSet_interval_sum_not_in_D (y : ℕ) (hy : 1 ≤ y) (a b : ℕ)
    (hcard : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2)
    (hs_in_D : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      Finset.Icc (72*y-6) (144*y-12))
    (hs_not_del : ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∉
      ((Finset.Icc (96*y-9) (108*y-15)).filter (fun k => 3 ∣ k) ∪
       (Finset.Icc (128*y-10) (144*y-22)).filter (fun k => k % 4 = 2) ∪
       ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ))) :
    False := by
  set T := (freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)
  by_cases h : ∀ x ∈ T, x ≤ 36*y-4
  · exact freudSet_interval_sum_all_in_A y hy a b hcard h hs_in_D hs_not_del
  · push Not at h; obtain ⟨z, hz, hzge⟩ := h
    have hzge' : 48*y-5 ≤ z := by
      have := (Finset.mem_filter.mp hz).1
      by_contra hlt; push Not at hlt
      exact freudSet_no_gap_AB y hy z this (by omega) (by omega)
    exact freudSet_interval_sum_cross_AB_or_all_ge_48
      y hy a b hcard ⟨z, hz, hzge'⟩ hs_in_D hs_not_del

/-- No contiguous subsum of `freudSet y` lands in `freudSet y`:
combines the block-by-block analysis (A, B, C, D). -/
lemma freudSet_no_interval_sum (y : ℕ) (hy : 1 ≤ y) :
    ∀ a b : ℕ,
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).card ≥ 2 →
    ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∉ freudSet y := by
  intros a b hcard
  have hsum_ge := freudSet_interval_sum_lb y hy a b hcard
  contrapose! hsum_ge; revert hsum_ge; intro hsum_in_set
  have hsum_in_parts :
      ((freudSet y).filter (fun x => a ≤ x ∧ x ≤ b)).sum id ∈
      Icc (32*y-4) (36*y-4) ∪ (Icc (48*y-5) (54*y-7)).filter (fun k => ¬3 ∣ k) ∪
      (Icc (64*y-6) (72*y-10)).filter (2 ∣ ·) ∪ (Icc (72*y-6) (144*y-12)) \
        ((Icc (96*y-9) (108*y-15)).filter (3 ∣ ·) ∪
         (Icc (128*y-10) (144*y-22)).filter (· % 4 = 2) ∪
         ({84*y-9, 120*y-14, 132*y-13, 118*y-13, 144*y-16} : Finset ℕ)) :=
    mem_def.mpr hsum_in_set
  simp +zetaDelta at *
  rcases hsum_in_parts with h | h | h | h
  · omega
  · omega
  · have := freudSet_interval_sum_not_in_C y hy a b hcard
    simp_all +decide [Nat.dvd_iff_mod_eq_zero]
  · have := freudSet_interval_sum_not_in_D y hy a b hcard
    simp_all +decide [Finset.sum_filter]

lemma freudSet_csf (y : ℕ) (hy : 1 ≤ y) :
    ConsecutiveSumFree (freudSet y) :=
  csf_of_no_interval_sum _ (freudSet_no_interval_sum y hy)

/-- **Main Construction (19/36).** For all sufficiently large `n`, there exists a CSF subset
of `{1, …, n}` with at least `⌊19n/36⌋ - C` elements. -/
theorem construction_19_36 :
    ∃ C : ℕ, ∀ n : ℕ, 144 ≤ n → ∃ S : Finset ℕ,
    S ⊆ Icc 1 n ∧ ConsecutiveSumFree S ∧ 36 * S.card + C ≥ 19 * n := by
  refine ⟨2741, fun n hn => ⟨freudSet ((n + 12) / 144), ?_, ?_, ?_⟩⟩
  · exact (freudSet_subset _ (by omega)).trans (Icc_subset_Icc_right (by omega))
  · exact freudSet_csf _ (by omega)
  · rw [freudSet_card _ (by omega)]; omega

/-! ## The N/2 + O(1) bound is false -/

/-- **Erdős Problem 867 (disproof).** It is false that every CSF subset of
`{1, …, N}` satisfies `|A| ≤ N/2 + O(1)`. Freud's construction achieves
density `19/36 > 1/2`. -/
theorem csf_exceeds_half_plus_constant :
    ¬∃ C : ℕ, ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ Icc 1 n → ConsecutiveSumFree S → 2 * S.card ≤ n + C := by
  push Not; intro C
  obtain ⟨C', hC'⟩ := construction_19_36
  obtain ⟨S, hS⟩ := hC' (36 * (C + C' + 1) + 144) (by linarith)
  exact ⟨_, S, hS.1, hS.2.1, by linarith⟩

end Erdos867

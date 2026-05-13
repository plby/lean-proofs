import Mathlib

open scoped BigOperators

/-!
This file only reintroduces the pieces of `src/for_mathlib/misc.lean` that are not already
available in Mathlib4 under the same names.

In particular, Mathlib4 already provides results such as:
* `Rat.cast_sum`
* `Finset.filter_comm`
* `Finset.one_le_prod`
* `Real.finset_prod_rpow`
* `Real.self_le_rpow_of_one_le`
* `Real.self_le_rpow_of_le_one`
* the add-one interval lemmas in `Finset` and `Set`
-/

namespace Int

lemma Ico_succ_right {a b : ℤ} : Finset.Ico a (b + 1) = Finset.Icc a b := by
  simpa using (Finset.Ico_add_one_right_eq_Icc a b)

lemma Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
  simpa [eq_comm] using (Finset.insert_Ioc_right_eq_Ioc_add_one (a := a) (b := b) h)

lemma insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
    insert (a + 1) (Finset.Ioc (a + 1) b) = Finset.Ioc a b := by
  simpa using (Finset.insert_Ioc_add_one_left_eq_Ioc (a := a) (b := b) h)

lemma Ioc_succ_left {a b : ℤ} (h : a < b) :
    Finset.Ioc (a + 1) b = (Finset.Ioc a b).erase (a + 1) := by
  have hnot : a + 1 ∉ Finset.Ioc (a + 1) b := by simp
  rw [← insert_Ioc_succ_left h, Finset.erase_insert hnot]

lemma Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc (a + 1) (b + 1) = (insert (b + 1) (Finset.Ioc a b)).erase (a + 1) := by
  have hab : a < b + 1 := h.trans_lt (lt_add_of_pos_right b zero_lt_one)
  rw [Ioc_succ_left hab, Ioc_succ_right h]

end Int

namespace Finset

lemma Icc_subset_range_add_one {x y : ℕ} : Icc x y ⊆ range (y + 1) := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  exact Finset.Icc_subset_Icc_left (b := y) (Nat.zero_le x)

lemma Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Ico x y ∪ Icc y z = Icc x z := by
  rw [← Finset.coe_inj, Finset.coe_union, Finset.coe_Ico, Finset.coe_Icc, Finset.coe_Icc,
    Set.Ico_union_Icc_eq_Icc h₁ h₂]

lemma Icc_sdiff_Icc_right {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Icc x z \ Icc y z = Ico x y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma Icc_sdiff_Icc_left {x y z : ℕ} (h₁ : z ≤ y) (h₂ : x ≤ z) :
    Icc x y \ Icc x z = Ioc z y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma prod_rpow {ι : Type*} {s : Finset ι} {f : ι → ℝ} (c : ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∏ i ∈ s, f i) ^ c = ∏ i ∈ s, (f i ^ c) := by
  simpa [eq_comm] using (Real.finset_prod_rpow s f hf c)

end Finset

@[simp] theorem Ico_inter_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Finset.Ico a b ∩ Finset.Icc b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem Ico_disjoint_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Disjoint (Finset.Ico a b) (Finset.Icc b c) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem range_sdiff_Icc {x y : ℕ} (h : x ≤ y) :
    Finset.range (y + 1) \ Finset.Icc x y = Finset.Ico 0 x := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_sdiff_Icc_right (Nat.zero_le _) h]

theorem Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ici a \ Set.Icc a b = Set.Ioi b := by
  ext x
  simp only [Set.mem_diff, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · intro hx
    exact lt_of_not_ge fun hxb => hx.2 ⟨hx.1, hxb⟩
  · intro hbx
    exact ⟨hab.trans hbx.le, fun hx => (not_lt_of_ge hx.2) hbx⟩

theorem Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ioi a \ Set.Ioc a b = Set.Ioi b := by
  rw [Set.Ioi_diff_Ioc, max_eq_right hab]

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod (s := s) (f := f) h1)

namespace Real

lemma le_rpow_self_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    x ≤ x ^ r :=
  self_le_rpow_of_one_le hx hr

lemma le_rpow_self_of {x r : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (h_one_le : r ≤ 1) :
    x ≤ x ^ r :=
  self_le_rpow_of_le_one hx₀ hx₁ h_one_le

end Real

@[to_additive]
theorem prod_powerset_compl {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Finset α) (f : Finset α → β) :
    (∏ x ∈ s.powerset, f (s \ x)) = ∏ x ∈ s.powerset, f x := by
  refine Finset.prod_bij' (fun x _ ↦ s \ x) (fun x _ ↦ s \ x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    rfl

import Mathlib

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Left compressions for finite uniform set systems

This file supplies the elementary compression machinery used in the proof of
Erdős Problem 83.  Families are represented by finite sets of finite subsets
of `Fin N`.
-/

open scoped BigOperators
open Finset

namespace Erdos83

variable {N k : ℕ}

/-- Every member of `𝒻` has cardinality `k`. -/
def Uniform (k : ℕ) (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒻 → A.card = k

/-- Any two (not necessarily distinct) members meet in at least two points. -/
def TwoIntersecting (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ ⦃A B⦄, A ∈ 𝒻 → B ∈ 𝒻 → 2 ≤ (A ∩ B).card

/-- Apply the transposition `(i j)` to every element of a finite set. -/
def setTranspose (i j : Fin N) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map (Equiv.swap i j).toEmbedding

@[simp]
theorem mem_setTranspose {i j x : Fin N} {A : Finset (Fin N)} :
    x ∈ setTranspose i j A ↔ Equiv.swap i j x ∈ A := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, hxy⟩
    subst x
    simpa using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨Equiv.swap i j x, hx, by simp⟩

@[simp]
theorem card_setTranspose (i j : Fin N) (A : Finset (Fin N)) :
    (setTranspose i j A).card = A.card := by
  simp [setTranspose]

@[simp]
theorem setTranspose_involutive (i j : Fin N) (A : Finset (Fin N)) :
    setTranspose i j (setTranspose i j A) = A := by
  classical
  ext x
  simp

@[simp]
theorem setTranspose_inter (i j : Fin N) (A B : Finset (Fin N)) :
    setTranspose i j (A ∩ B) = setTranspose i j A ∩ setTranspose i j B := by
  classical
  ext x
  simp

/-- The singleton left shift `j → i`: replace `j` by `i` when possible. -/
def singletonLeftShift (i j : Fin N) (A : Finset (Fin N)) : Finset (Fin N) :=
  if j ∈ A ∧ i ∉ A then setTranspose i j A else A

theorem singletonLeftShift_eq_transpose {i j : Fin N} {A : Finset (Fin N)}
    (h : j ∈ A ∧ i ∉ A) :
    singletonLeftShift i j A = setTranspose i j A := by
  simp [singletonLeftShift, h]

theorem singletonLeftShift_eq_self {i j : Fin N} {A : Finset (Fin N)}
    (h : ¬ (j ∈ A ∧ i ∉ A)) : singletonLeftShift i j A = A := by
  simp [singletonLeftShift, h]

@[simp]
theorem card_singletonLeftShift (i j : Fin N) (A : Finset (Fin N)) :
    (singletonLeftShift i j A).card = A.card := by
  classical
  by_cases h : j ∈ A ∧ i ∉ A
  · simp [singletonLeftShift, h]
  · simp [singletonLeftShift, h]

theorem singletonLeftShift_ne_self_iff {i j : Fin N} {A : Finset (Fin N)} :
    singletonLeftShift i j A ≠ A ↔ j ∈ A ∧ i ∉ A := by
  classical
  constructor
  · intro h
    by_contra hc
    exact h (singletonLeftShift_eq_self hc)
  · rintro hij hEq
    have hj : j ∈ setTranspose i j A := by
      rw [← singletonLeftShift_eq_transpose hij, hEq]
      exact hij.1
    have hi : i ∈ A := by
      simpa using hj
    exact hij.2 hi

/-- The member map underlying the cardinality-preserving family shift.

If the shifted set is already in the family, the original member is retained;
otherwise it is replaced by its singleton left shift.
-/
def familyShiftMember (𝒻 : Finset (Finset (Fin N))) (i j : Fin N)
    (A : Finset (Fin N)) : Finset (Fin N) :=
  if singletonLeftShift i j A ∈ 𝒻 then A else singletonLeftShift i j A

/-- Collision-protected singleton left shift of a finite family. -/
def familyShift (i j : Fin N) (𝒻 : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  𝒻.image (familyShiftMember 𝒻 i j)

theorem familyShiftMember_injective_on (𝒻 : Finset (Finset (Fin N))) (i j : Fin N) :
    Set.InjOn (familyShiftMember 𝒻 i j) 𝒻 := by
  classical
  intro A hA B hB hEq
  by_cases hAs : singletonLeftShift i j A ∈ 𝒻
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using hEq
    · have : A = singletonLeftShift i j B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      exact (hBs (this ▸ hA)).elim
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · have : singletonLeftShift i j A = B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      exact (hAs (this.symm ▸ hB)).elim
    · have hsEq : singletonLeftShift i j A = singletonLeftShift i j B := by
        simpa [familyShiftMember, hAs, hBs] using hEq
      have hAne : singletonLeftShift i j A ≠ A := by
        intro h
        exact hAs (h.symm ▸ hA)
      have hBne : singletonLeftShift i j B ≠ B := by
        intro h
        exact hBs (h.symm ▸ hB)
      have hAc := singletonLeftShift_ne_self_iff.mp hAne
      have hBc := singletonLeftShift_ne_self_iff.mp hBne
      rw [singletonLeftShift_eq_transpose hAc,
        singletonLeftShift_eq_transpose hBc] at hsEq
      have := congrArg (setTranspose i j) hsEq
      simpa using this

@[simp]
theorem card_familyShift (i j : Fin N) (𝒻 : Finset (Finset (Fin N))) :
    (familyShift i j 𝒻).card = 𝒻.card := by
  classical
  exact Finset.card_image_iff.mpr (familyShiftMember_injective_on 𝒻 i j)

theorem Uniform.familyShift {k : ℕ} {𝒻 : Finset (Finset (Fin N))}
    (h : Uniform k 𝒻) (i j : Fin N) : Uniform k (familyShift i j 𝒻) := by
  classical
  intro C hC
  rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
  by_cases hs : singletonLeftShift i j A ∈ 𝒻
  · simpa [familyShiftMember, hs] using h hA
  · simpa [familyShiftMember, hs] using h hA

theorem card_inter_transpose_cross (i j : Fin N) (A B : Finset (Fin N)) :
    (setTranspose i j A ∩ B).card = (A ∩ setTranspose i j B).card := by
  classical
  rw [← card_setTranspose i j (setTranspose i j A ∩ B), setTranspose_inter]
  simp

theorem inter_subset_inter_transpose_right {i j : Fin N} {A B : Finset (Fin N)}
    (hA : j ∈ A ∧ i ∉ A) (hB : ¬ (j ∈ B ∧ i ∉ B)) :
    A ∩ B ⊆ A ∩ setTranspose i j B := by
  classical
  intro x hx
  have hxA : x ∈ A := Finset.mem_inter.mp hx |>.1
  have hxB : x ∈ B := Finset.mem_inter.mp hx |>.2
  refine Finset.mem_inter.mpr ⟨hxA, ?_⟩
  rw [mem_setTranspose]
  by_cases hxi : x = i
  · subst x
    exact (hA.2 hxA).elim
  by_cases hxj : x = j
  · subst x
    have hiB : i ∈ B := by
      by_contra hi
      exact hB ⟨hxB, hi⟩
    simpa using hiB
  · simpa [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hxB

private theorem twoInter_of_left_moved
    {𝒻 : Finset (Finset (Fin N))} (h : TwoIntersecting 𝒻)
    {i j : Fin N} {A B : Finset (Fin N)}
    (hA : A ∈ 𝒻) (hB : B ∈ 𝒻)
    (hAs : singletonLeftShift i j A ∉ 𝒻)
    (hBs : singletonLeftShift i j B ∈ 𝒻) :
    2 ≤ (singletonLeftShift i j A ∩ B).card := by
  classical
  have hAne : singletonLeftShift i j A ≠ A := by
    intro hEq
    exact hAs (hEq.symm ▸ hA)
  have hAc : j ∈ A ∧ i ∉ A := singletonLeftShift_ne_self_iff.mp hAne
  rw [singletonLeftShift_eq_transpose hAc]
  by_cases hBc : j ∈ B ∧ i ∉ B
  · have hBt : setTranspose i j B ∈ 𝒻 := by
      simpa [singletonLeftShift_eq_transpose hBc] using hBs
    rw [card_inter_transpose_cross]
    exact h hA hBt
  · rw [card_inter_transpose_cross]
    exact le_trans (h hA hB) (Finset.card_le_card (inter_subset_inter_transpose_right hAc hBc))

theorem TwoIntersecting.familyShift {𝒻 : Finset (Finset (Fin N))}
    (h : TwoIntersecting 𝒻) (i j : Fin N) : TwoIntersecting (familyShift i j 𝒻) := by
  classical
  intro C D hC hD
  rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
  rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
  by_cases hAs : singletonLeftShift i j A ∈ 𝒻
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using h hA hB
    · have hm := twoInter_of_left_moved h hB hA hBs hAs
      simpa [familyShiftMember, hAs, hBs, Finset.inter_comm] using hm
  · by_cases hBs : singletonLeftShift i j B ∈ 𝒻
    · simpa [familyShiftMember, hAs, hBs] using
        (twoInter_of_left_moved h hA hB hAs hBs)
    · have hAne : singletonLeftShift i j A ≠ A := by
        intro hEq
        exact hAs (hEq.symm ▸ hA)
      have hBne : singletonLeftShift i j B ≠ B := by
        intro hEq
        exact hBs (hEq.symm ▸ hB)
      have hAc := singletonLeftShift_ne_self_iff.mp hAne
      have hBc := singletonLeftShift_ne_self_iff.mp hBne
      simp only [familyShiftMember, hAs, hBs, if_false]
      rw [singletonLeftShift_eq_transpose hAc,
        singletonLeftShift_eq_transpose hBc]
      have hc := h hA hB
      rw [← card_setTranspose i j (A ∩ B), setTranspose_inter] at hc
      exact hc

/-- Sum of the numeric labels in a set. -/
def setWeight (A : Finset (Fin N)) : ℕ :=
  ∑ x ∈ A, x.val

/-- Total weight of all members of a family. -/
def familyWeight (𝒻 : Finset (Finset (Fin N))) : ℕ :=
  ∑ A ∈ 𝒻, setWeight A

theorem setTranspose_eq_insert_erase {i j : Fin N} {A : Finset (Fin N)}
    (h : j ∈ A ∧ i ∉ A) : setTranspose i j A = insert i (A.erase j) := by
  classical
  ext x
  rw [mem_setTranspose]
  by_cases hxi : x = i
  · subst x
    simp [h.1, h.2]
  by_cases hxj : x = j
  · subst x
    simp [h.2, hxi]
  · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]

theorem setWeight_singletonLeftShift_lt {i j : Fin N} {A : Finset (Fin N)}
    (hij : i < j) (hne : singletonLeftShift i j A ≠ A) :
    setWeight (singletonLeftShift i j A) < setWeight A := by
  classical
  have hc : j ∈ A ∧ i ∉ A := singletonLeftShift_ne_self_iff.mp hne
  have hiErase : i ∉ A.erase j := by simp [hc.2]
  have hjErase : j ∉ A.erase j := by simp
  rw [singletonLeftShift_eq_transpose hc, setTranspose_eq_insert_erase hc]
  have hshiftWeight :
      setWeight (insert i (A.erase j)) = i.val + setWeight (A.erase j) := by
    simp [setWeight, hiErase]
  have hAWeight : setWeight A = j.val + setWeight (A.erase j) := by
    calc
      setWeight A = setWeight (insert j (A.erase j)) := by
        rw [Finset.insert_erase hc.1]
      _ = j.val + setWeight (A.erase j) := by
        simp [setWeight, hjErase]
  rw [hshiftWeight, hAWeight]
  exact Nat.add_lt_add_right (show i.val < j.val from hij) (setWeight (A.erase j))

private theorem familyShiftMember_weight_le
    (𝒻 : Finset (Finset (Fin N))) {i j : Fin N} (hij : i < j)
    (A : Finset (Fin N)) (hA : A ∈ 𝒻) :
    setWeight (familyShiftMember 𝒻 i j A) ≤ setWeight A := by
  classical
  by_cases hs : singletonLeftShift i j A ∈ 𝒻
  · simp [familyShiftMember, hs]
  · simp only [familyShiftMember, hs, if_false]
    have hne : singletonLeftShift i j A ≠ A := by
      intro hEq
      exact hs (hEq.symm ▸ hA)
    exact (setWeight_singletonLeftShift_lt hij hne).le

theorem familyWeight_familyShift_lt
    {𝒻 : Finset (Finset (Fin N))} {i j : Fin N}
    (hij : i < j) (hne : familyShift i j 𝒻 ≠ 𝒻) :
    familyWeight (familyShift i j 𝒻) < familyWeight 𝒻 := by
  classical
  have hmove : ∃ A ∈ 𝒻, familyShiftMember 𝒻 i j A ≠ A := by
    by_contra h
    push_neg at h
    apply hne
    ext A
    simp only [familyShift, mem_image]
    constructor
    · rintro ⟨B, hB, rfl⟩
      simpa [h B hB] using hB
    · intro hA
      exact ⟨A, hA, h A hA⟩
  rcases hmove with ⟨A, hA, hAmove⟩
  have hinj := familyShiftMember_injective_on 𝒻 i j
  rw [familyWeight, familyShift, Finset.sum_image hinj]
  apply Finset.sum_lt_sum
  · intro B hB
    exact familyShiftMember_weight_le 𝒻 hij B hB
  · refine ⟨A, hA, ?_⟩
    by_cases hs : singletonLeftShift i j A ∈ 𝒻
    · simp [familyShiftMember, hs] at hAmove
    · simp only [familyShiftMember, hs, if_false] at hAmove ⊢
      exact setWeight_singletonLeftShift_lt hij hAmove

/-- A family fixed by every singleton shift from a larger to a smaller label. -/
def LeftCompressed (𝒻 : Finset (Finset (Fin N))) : Prop :=
  ∀ (i j : Fin N), i < j → familyShift i j 𝒻 = 𝒻

/-- In a left-compressed family, every available left shift of a member is
again a member. -/
theorem LeftCompressed.shifted_mem {𝒻 : Finset (Finset (Fin N))}
    (h : LeftCompressed 𝒻) {i j : Fin N} (hij : i < j)
    {A : Finset (Fin N)} (hA : A ∈ 𝒻) (hj : j ∈ A) (hi : i ∉ A) :
    singletonLeftShift i j A ∈ 𝒻 := by
  classical
  by_contra hs
  have hm : singletonLeftShift i j A ∈ familyShift i j 𝒻 := by
    apply Finset.mem_image.mpr
    refine ⟨A, hA, ?_⟩
    simp [familyShiftMember, hs]
  rw [h i j hij] at hm
  exact hs hm

end Erdos83

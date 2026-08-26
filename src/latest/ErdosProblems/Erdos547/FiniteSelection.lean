import Mathlib.Tactic

/-!
# Selecting a controlled number of vertices from small pieces
-/

namespace Erdos547

open Finset

open scoped Classical in
/-- From a family of sets of size at most `b`, select a subfamily whose union
reaches a target `a` without exceeding `a+b`. Disjointness is not needed. -/
theorem exists_bounded_subfamily {U : Type*} (F : Finset (Finset U)) (a b : ℕ)
    (hsmall : ∀ B ∈ F, B.card ≤ b) (henough : a ≤ (F.biUnion id).card) :
    ∃ C ⊆ F, a ≤ (C.biUnion id).card ∧ (C.biUnion id).card ≤ a + b := by
  classical
  let candidates := F.powerset.filter fun C ↦ a ≤ (C.biUnion id).card
  have hstart : F ∈ candidates := by simp [candidates, henough]
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨F, hstart⟩
  obtain ⟨hCF, htarget⟩ := Finset.mem_filter.mp hC
  have hsub : C ⊆ F := Finset.mem_powerset.mp hCF
  refine ⟨C, hsub, htarget, ?_⟩
  by_cases hCempty : C = ∅
  · simp [hCempty]
  obtain ⟨B, hBC⟩ := Finset.nonempty_iff_ne_empty.mpr hCempty
  have hprevious : ((C.erase B).biUnion id).card < a := by
    by_contra h
    have hlarge : a ≤ ((C.erase B).biUnion id).card := by omega
    have hmem : C.erase B ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub), hlarge⟩
    have hcard := hmin _ hmem
    have herase := Finset.card_erase_add_one hBC
    omega
  have hunion : C.biUnion id = B ∪ (C.erase B).biUnion id := by
    calc
      _ = (insert B (C.erase B)).biUnion id :=
        congrArg (fun D : Finset (Finset U) ↦ D.biUnion id) (Finset.insert_erase hBC).symm
      _ = _ := by rw [Finset.biUnion_insert]; rfl
  rw [hunion]
  have hcard := Finset.card_union_le B ((C.erase B).biUnion id)
  have hB := hsmall B (hsub hBC)
  omega

open scoped Classical in
/-- If a set fits into three parts of size `q`, one such part carries at least
one third of any real-valued total weight. -/
theorem exists_small_large_weight_subset {U : Type*} (F : Finset U) (w : U → ℝ)
    (q : ℕ) (hsize : F.card ≤ 3 * q) :
    ∃ P ⊆ F, P.card ≤ q ∧ (∑ x ∈ F, w x) ≤ 3 * ∑ x ∈ P, w x := by
  classical
  obtain ⟨P₀, hP₀, hcard₀⟩ := Finset.exists_subset_card_eq (min_le_right q F.card)
  let F₁ := F \ P₀
  obtain ⟨P₁, hP₁, hcard₁⟩ := Finset.exists_subset_card_eq (min_le_right q F₁.card)
  let P₂ := F₁ \ P₁
  have hP₂ : P₂ ⊆ F := Finset.sdiff_subset.trans Finset.sdiff_subset
  have hP₁F : P₁ ⊆ F := hP₁.trans Finset.sdiff_subset
  have hF₁card : F₁.card = F.card - P₀.card := Finset.card_sdiff_of_subset hP₀
  have hP₂card : P₂.card = F₁.card - P₁.card := Finset.card_sdiff_of_subset hP₁
  have hsmall₀ : P₀.card ≤ q := by omega
  have hsmall₁ : P₁.card ≤ q := by omega
  have hsmall₂ : P₂.card ≤ q := by omega
  have hsum₀ : (∑ x ∈ F₁, w x) + ∑ x ∈ P₀, w x = ∑ x ∈ F, w x :=
    Finset.sum_sdiff hP₀
  have hsum₁ : (∑ x ∈ P₂, w x) + ∑ x ∈ P₁, w x = ∑ x ∈ F₁, w x :=
    Finset.sum_sdiff hP₁
  by_cases hzero : (∑ x ∈ F, w x) ≤ 3 * ∑ x ∈ P₀, w x
  · exact ⟨P₀, hP₀, hsmall₀, hzero⟩
  by_cases hone : (∑ x ∈ F, w x) ≤ 3 * ∑ x ∈ P₁, w x
  · exact ⟨P₁, hP₁F, hsmall₁, hone⟩
  exact ⟨P₂, hP₂, hsmall₂, by linarith⟩

open scoped Classical in
/-- A square total-weight budget bounds the number of entries larger than
the square-root threshold, in an integer form with no rounding ambiguity. -/
theorem card_filter_gt_le_of_sum_le_square {U : Type*} (F : Finset U) (w : U → ℕ)
    (t : ℕ) (hbudget : (∑ x ∈ F, w x) ≤ t ^ 2) :
    (F.filter fun x ↦ t < w x).card ≤ t := by
  classical
  let Z := F.filter fun x ↦ t < w x
  have hmass : (t + 1) * Z.card ≤ ∑ x ∈ F, w x := by
    calc
      _ = ∑ _x ∈ Z, (t + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ Z, w x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change Z.card ≤ t
  by_contra h
  have hlarge : t + 1 ≤ Z.card := by omega
  nlinarith

end Erdos547

#print axioms Erdos547.exists_bounded_subfamily
#print axioms Erdos547.exists_small_large_weight_subset

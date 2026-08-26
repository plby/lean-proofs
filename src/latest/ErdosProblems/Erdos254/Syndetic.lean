/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped BigOperators

noncomputable def initialSegment (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∈ A)

@[simp] lemma mem_initialSegment {A : Set ℕ} {N n : ℕ} :
    n ∈ initialSegment A N ↔ n < N ∧ n ∈ A := by classical simp [initialSegment]

/-- A natural bound for Fan's defect `a - ∑ b < a, b`.
Using a natural bound is equivalent to the finiteness of the real supremum. -/
def HasBoundedDefect (A : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ a ∈ A, a ≤ (∑ b ∈ initialSegment A a, b) + C

def IsSyndetic (S : Set ℕ) : Prop := ∃ C : ℕ, ∀ n, ∃ m ∈ S, n ≤ m ∧ m ≤ n + C

def IsThick (S : Set ℕ) : Prop := ∀ L : ℕ, ∃ n : ℕ, ∀ k ≤ L, n + k ∈ S

private lemma initialSegment_succ {A : Set ℕ} {N : ℕ} (hN : N ∈ A) :
    initialSegment A (N + 1) = insert N (initialSegment A N) := by
  classical
  ext k
  simp only [mem_initialSegment, Finset.mem_insert]
  constructor
  · rintro ⟨hk, hA⟩
    by_cases h : k = N
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hA⟩
  · rintro (rfl | ⟨hk, hA⟩)
    · exact ⟨by omega, hN⟩
    · exact ⟨by omega, hA⟩

private lemma initialSegment_succ_of_not_mem {A : Set ℕ} {N : ℕ} (hN : N ∉ A) :
    initialSegment A (N + 1) = initialSegment A N := by
  ext k
  simp only [mem_initialSegment]
  constructor
  · rintro ⟨hk, hA⟩
    refine ⟨?_, hA⟩
    by_contra h
    have heq : k = N := by omega
    exact hN (heq ▸ hA)
  · rintro ⟨hk, hA⟩
    exact ⟨by omega, hA⟩

/-- The bounded-gap subset-sum induction, before taking an infinite limit. -/
lemma initialSegment_sum_cover {A : Set ℕ} {C : ℕ}
    (hC : ∀ a ∈ A, a ≤ (∑ b ∈ initialSegment A a, b) + C) (N : ℕ) :
    ∀ n ≤ ∑ b ∈ initialSegment A N, b,
      ∃ F ⊆ initialSegment A N, n ≤ ∑ x ∈ F, x ∧ (∑ x ∈ F, x) ≤ n + C := by
  classical
  induction N with
  | zero =>
      intro n hn
      have : n = 0 := by simpa [initialSegment] using hn
      subst n
      exact ⟨∅, Finset.empty_subset _, by simp⟩
  | succ N ih =>
      by_cases hN : N ∈ A
      · rw [initialSegment_succ hN]
        have hnot : N ∉ initialSegment A N := by simp
        rw [Finset.sum_insert hnot]
        intro n hn
        by_cases hsmall : n ≤ ∑ b ∈ initialSegment A N, b
        · obtain ⟨F, hF, hlo, hhi⟩ := ih n hsmall
          exact ⟨F, hF.trans (Finset.subset_insert _ _), hlo, hhi⟩
        · by_cases hless : n < N
          · refine ⟨{N}, by simp, by simpa using hless.le, ?_⟩
            have := hC N hN
            simp only [Finset.sum_singleton]
            omega
          · obtain ⟨F, hF, hlo, hhi⟩ := ih (n - N) (by omega)
            have hNF : N ∉ F := fun h ↦ hnot (hF h)
            refine ⟨insert N F, Finset.insert_subset_insert N hF, ?_, ?_⟩
            · rw [Finset.sum_insert hNF]; omega
            · rw [Finset.sum_insert hNF]; omega
      · rw [initialSegment_succ_of_not_mem hN]
        exact ih

/-- Burr–Erdős's bounded-defect criterion (Fan, Lemma 2.1). -/
theorem syndetic_subsetSums {A : Set ℕ} (hA : A.Infinite) (hdef : HasBoundedDefect A) :
    IsSyndetic (subsetSums A) := by
  obtain ⟨C, hC⟩ := hdef
  refine ⟨C, ?_⟩
  intro n
  obtain ⟨a, ha, hna⟩ := hA.exists_gt n
  have hmem : a ∈ initialSegment A (a + 1) := mem_initialSegment.mpr ⟨by omega, ha⟩
  have hsum : a ≤ ∑ b ∈ initialSegment A (a + 1), b :=
    Finset.single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _) hmem
  obtain ⟨F, hF, hlo, hhi⟩ := initialSegment_sum_cover hC (a + 1) n (hna.le.trans hsum)
  refine ⟨∑ x ∈ F, x, ⟨F, ?_, rfl⟩, hlo, hhi⟩
  intro x hx
  exact (mem_initialSegment.mp (hF hx)).2

/-- A thick summand fills the bounded gaps of a syndetic summand. -/
theorem syndetic_add_thick {S T : Set ℕ} (hS : IsSyndetic S) (hT : IsThick T) :
    ∀ᶠ n in atTop, ∃ s ∈ S, ∃ t ∈ T, s + t = n := by
  obtain ⟨C, hC⟩ := hS
  obtain ⟨a, ha⟩ := hT C
  filter_upwards [eventually_ge_atTop (a + C)] with n hn
  obtain ⟨s, hs, hlo, hhi⟩ := hC (n - (a + C))
  refine ⟨s, hs, n - s, ?_, by omega⟩
  have hs' : s ≤ n := by omega
  have hk : n - s - a ≤ C := by omega
  have heq : a + (n - s - a) = n - s := by omega
  simpa only [heq] using ha (n - s - a) hk

/-- Finite deletion preserves bounded defect (Fan's inequality (2.1)). -/
lemma HasBoundedDefect.sdiff_finset {A : Set ℕ} (hA : HasBoundedDefect A)
    (D : Finset ℕ) : HasBoundedDefect (A \ (D : Set ℕ)) := by
  classical
  obtain ⟨C, hC⟩ := hA
  refine ⟨C + ∑ d ∈ D, d, ?_⟩
  intro a ha
  have heq : initialSegment (A \ (D : Set ℕ)) a = initialSegment A a \ D := by
    ext b
    simp only [mem_initialSegment, Set.mem_sdiff, Finset.mem_coe, Finset.mem_sdiff]
    tauto
  have hsum := Finset.sum_inter_add_sum_sdiff (initialSegment A a) D (fun x ↦ x)
  have hle : (∑ b ∈ initialSegment A a ∩ D, b) ≤ ∑ d ∈ D, d :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hCa := hC a ha.1
  rw [heq]
  omega

lemma complete_union_of_syndetic_thick {A B : Set ℕ} (hAB : Disjoint A B)
    (hA : IsSyndetic (subsetSums A)) (hB : IsThick (subsetSums B)) :
    IsComplete (A ∪ B) := by
  filter_upwards [syndetic_add_thick hA hB] with n hn
  rcases hn with ⟨s, hs, t, ht, rfl⟩
  exact IsSumOfDistinct.add hAB hs ht

end Erdos254

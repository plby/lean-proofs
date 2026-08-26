/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

def blockUnion (F : ℕ → Finset ℕ) : Set ℕ := {a | ∃ k, a ∈ F k}

/-- A disjoint family of finite blocks identifies its union with a sigma type. -/
noncomputable def blockEquiv (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    (Σ k, ↥(F k)) ≃ ↥(blockUnion F) :=
  Equiv.ofBijective (fun p ↦ ⟨p.2.1, p.1, p.2.2⟩) (by
    constructor
    · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
      have hxy : x = y := congrArg (fun z : blockUnion F ↦ (z : ℕ)) h
      subst y
      have hij : i = j := by
        by_contra hij
        exact Finset.disjoint_left.mp (hF hij) hx hy
      subst j
      rfl
    · rintro ⟨x, k, hx⟩
      exact ⟨⟨k, x, hx⟩, rfl⟩)

lemma summable_blockUnion_iff (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (f : ℕ → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    Summable (fun a : blockUnion F ↦ f a) ↔ Summable (fun k ↦ ∑ a ∈ F k, f a) := by
  classical
  rw [← (blockEquiv F hF).summable_iff]
  change Summable (fun p : Σ k, ↥(F k) ↦ f p.2) ↔ _
  rw [summable_sigma_of_nonneg (f := fun p : Σ k, ↥(F k) ↦ f p.2) (fun p ↦ hf p.2)]
  simp only [Summable.of_finite, forall_const, true_and, tsum_fintype, Finset.sum_coe_sort]

lemma summable_on_subset {A B : Set ℕ} (hAB : A ⊆ B) {f : ℕ → ℝ}
    (hf : Summable (fun a : B ↦ f a)) : Summable (fun a : A ↦ f a) := by
  let i : A → B := fun a ↦ ⟨a.1, hAB a.2⟩
  have hi : Function.Injective i := fun a b h ↦
    Subtype.ext (congrArg (fun z : B ↦ (z : ℕ)) h)
  exact Summable.comp_injective (f := fun a : B ↦ f a) (i := i) hf hi

lemma blockUnion_mono {F G : ℕ → Finset ℕ} (h : ∀ k, F k ⊆ G k) :
    blockUnion F ⊆ blockUnion G := by
  rintro a ⟨k, hk⟩
  exact ⟨k, h k hk⟩

lemma disjoint_blockUnion {F G X : ℕ → Finset ℕ}
    (hX : Pairwise (fun i j ↦ Disjoint (X i) (X j)))
    (hF : ∀ k, F k ⊆ X k) (hG : ∀ k, G k ⊆ X k)
    (hFG : ∀ k, Disjoint (F k) (G k)) : Disjoint (blockUnion F) (blockUnion G) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨i, hi⟩ ⟨j, hj⟩
  by_cases h : i = j
  · subst j
    exact Finset.disjoint_left.mp (hFG i) hi hj
  · exact Finset.disjoint_left.mp (hX h) (hF i hi) (hG j hj)

lemma blockUnion_inter_block {F X : ℕ → Finset ℕ}
    (hX : Pairwise (fun i j ↦ Disjoint (X i) (X j)))
    (hF : ∀ k, F k ⊆ X k) (k : ℕ) :
    blockUnion F ∩ (X k : Set ℕ) = (F k : Set ℕ) := by
  ext a
  constructor
  · rintro ⟨⟨i, hi⟩, ha⟩
    by_cases h : i = k
    · simpa only [h, Finset.mem_coe] using hi
    · exact (Finset.disjoint_left.mp (hX h) (hF i hi) ha).elim
  · intro ha
    exact ⟨⟨k, ha⟩, hF k ha⟩

end Erdos254

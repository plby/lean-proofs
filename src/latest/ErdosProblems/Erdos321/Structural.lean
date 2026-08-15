import ErdosProblems.Erdos321.Basic

namespace Erdos321

/-- A collision can always be reduced to two disjoint, not-both-empty subsets. -/
def HasDisjointCollision (A : Finset ℕ) : Prop :=
  ∃ S ∈ A.powerset, ∃ T ∈ A.powerset,
    Disjoint S T ∧ (S.Nonempty ∨ T.Nonempty) ∧
      reciprocalSubsetSum S = reciprocalSubsetSum T

private theorem reciprocalSubsetSum_sdiff_eq
    {S T : Finset ℕ}
    (h : reciprocalSubsetSum S = reciprocalSubsetSum T) :
    reciprocalSubsetSum (S \ T) = reciprocalSubsetSum (T \ S) := by
  have hS := Finset.sum_sdiff (f := fun n : ℕ => ((n : ℚ)⁻¹))
    (Finset.inter_subset_left : S ∩ T ⊆ S)
  have hT := Finset.sum_sdiff (f := fun n : ℕ => ((n : ℚ)⁻¹))
    (Finset.inter_subset_left : T ∩ S ⊆ T)
  simp only [Finset.sdiff_inter_self_left] at hS hT
  rw [Finset.inter_comm T S] at hT
  dsimp [reciprocalSubsetSum] at h ⊢
  linarith

/-- Pairwise distinct subset sums are equivalent to the absence of a nontrivial
signed relation after cancelling the common part of the two subsets. -/
theorem valid_iff_no_disjoint_collision (A : Finset ℕ) :
    Valid A ↔ ¬ HasDisjointCollision A := by
  classical
  constructor
  · intro hValid hCollision
    obtain ⟨S, hS, T, hT, hDisjoint, hNonempty, hEq⟩ := hCollision
    have hST : S = T := hValid S hS T hT hEq
    subst T
    have hEmpty : S = ∅ := by
      have hInter : S ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjoint
      simpa using hInter
    simp [hEmpty] at hNonempty
  · intro hNoCollision S hS T hT hEq
    by_contra hNe
    apply hNoCollision
    refine ⟨S \ T, ?_, T \ S, ?_, ?_, ?_, reciprocalSubsetSum_sdiff_eq hEq⟩
    · exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset.trans (Finset.mem_powerset.mp hS))
    · exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset.trans (Finset.mem_powerset.mp hT))
    · rw [Finset.disjoint_left]
      intro a haS haT
      exact (Finset.mem_sdiff.mp haS).2 (Finset.mem_sdiff.mp haT).1
    · by_cases hSub : S ⊆ T
      · right
        exact Finset.sdiff_nonempty.mpr
          (fun hTS => hNe (Finset.Subset.antisymm hSub hTS))
      · left
        exact Finset.sdiff_nonempty.mpr hSub

/-- Zero cannot occur in a valid denominator set: its reciprocal contributes
nothing and collides with the empty subset. -/
theorem Valid.zero_not_mem {A : Finset ℕ} (hA : Valid A) : 0 ∉ A := by
  intro h0
  have hEmpty : (∅ : Finset ℕ) ∈ A.powerset := by simp
  have hZero : ({0} : Finset ℕ) ∈ A.powerset := by simp [h0]
  have hEq : reciprocalSubsetSum ∅ = reciprocalSubsetSum {0} := by
    simp [reciprocalSubsetSum]
  have := hA ∅ hEmpty {0} hZero hEq
  simp at this

/-- Every subset of a valid denominator set is valid. -/
theorem Valid.mono {A B : Finset ℕ} (hA : Valid A) (hBA : B ⊆ A) : Valid B := by
  intro S hS T hT hEq
  apply hA S (Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS).trans hBA))
    T (Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hT).trans hBA)) hEq

/-- The elementary identity `1/(2k) = 1/(3k) + 1/(6k)` gives a forbidden
configuration in every valid set. -/
theorem not_valid_of_scaled_236 {A : Finset ℕ} {k : ℕ} (hk : k ≠ 0)
    (h2 : 2 * k ∈ A) (h3 : 3 * k ∈ A) (h6 : 6 * k ∈ A) : ¬ Valid A := by
  intro hValid
  have h36 : 3 * k ≠ 6 * k := by omega
  have hEq : reciprocalSubsetSum {2 * k} =
      reciprocalSubsetSum {3 * k, 6 * k} := by
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    simp [reciprocalSubsetSum, h36, Nat.cast_mul]
    field_simp
    norm_num
  have hLeft : ({2 * k} : Finset ℕ) ∈ A.powerset := by
    simp [h2]
  have hRight : ({3 * k, 6 * k} : Finset ℕ) ∈ A.powerset := by
    rw [Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h3
    · exact h6
  have hSets : ({2 * k} : Finset ℕ) = {3 * k, 6 * k} :=
    hValid {2 * k} hLeft {3 * k, 6 * k} hRight hEq
  have hMem : 2 * k ∈ ({3 * k, 6 * k} : Finset ℕ) := by
    rw [← hSets]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  omega

end Erdos321

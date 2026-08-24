import ErdosProblems.Erdos587.FiniteStructure

/-! Faithful casting of distinct subset sums and their ambient upper bound. -/

open scoped BigOperators

namespace Erdos587

theorem sum_natToIntFinset (A : Finset ℕ) :
    (∑ z ∈ natToIntFinset A, z) = ((∑ a ∈ A, a : ℕ) : ℤ) := by
  simp [natToIntFinset, Finset.sum_image]

theorem subsetSum_natToIntFinset (A : Finset ℕ) :
    (natToIntFinset A).subsetSum = natToIntFinset A.subsetSum := by
  ext z
  constructor
  · intro hz
    obtain ⟨V, hV, rfl⟩ := Finset.mem_subsetSum_iff.mp hz
    obtain ⟨U, hUA, rfl⟩ := exists_subset_natToIntFinset_eq hV
    rw [sum_natToIntFinset, natCast_mem_natToIntFinset]
    exact Finset.mem_subsetSum_iff.mpr ⟨U, hUA, rfl⟩
  · intro hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨U, hUA, rfl⟩ := Finset.mem_subsetSum_iff.mp hn
    apply Finset.mem_subsetSum_iff.mpr
    exact ⟨natToIntFinset U, Finset.image_mono _ hUA, sum_natToIntFinset U⟩

theorem natToIntFinset_subset_Icc {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) : natToIntFinset A ⊆ Finset.Icc 0 (N : ℤ) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  have hi := Finset.mem_Icc.mp (hA ha)
  apply Finset.mem_Icc.mpr
  change 0 ≤ (a : ℤ) ∧ (a : ℤ) ≤ N
  exact ⟨by positivity, by exact_mod_cast hi.2⟩

theorem GeneralizedAP.upperEndpoint_le_interval_budget
    (Q : GeneralizedAP) (W : Finset ℤ) (N R : ℕ)
    (hW : W ⊆ Finset.Icc 0 (N : ℤ)) (hcard : W.card ≤ R)
    (hQ : Q.carrier ⊆ W.subsetSum) : Q.upperEndpoint ≤ ((R * N : ℕ) : ℤ) := by
  obtain ⟨U, hUW, hsum⟩ := Finset.mem_subsetSum_iff.mp (hQ Q.upperEndpoint_mem)
  calc
    Q.upperEndpoint = ∑ x ∈ U, x := hsum.symm
    _ ≤ ∑ _x ∈ U, (N : ℤ) := Finset.sum_le_sum
      (fun x hx => (Finset.mem_Icc.mp (hW (hUW hx))).2)
    _ = (U.card : ℤ) * N := by simp
    _ ≤ (R : ℤ) * N := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card hUW).trans hcard) (Nat.cast_nonneg _)
    _ = ((R * N : ℕ) : ℤ) := by push_cast; rfl

end Erdos587

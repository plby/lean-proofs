import Mathlib

/-!
# An exact averaging lemma for the heaviest colours

If `T` colours are chosen among `D` colours so that their total weight is
maximal, their total weight is at least the corresponding `T / D` fraction
of the weight of all colours.  The formulation over `Nat` avoids division.
-/

open scoped Classical

namespace Erdos182

/-- Among `D` nonnegative integral weights, some `T` weights carry at least
the `T / D` fraction of the total weight. -/
theorem exists_top_colors {β : Type*} [Fintype β] (w : β → ℕ) (T : ℕ)
    (hT : T ≤ Fintype.card β) :
    ∃ A : Finset β, A.card = T ∧
      T * (∑ i, w i) ≤ Fintype.card β * (∑ i ∈ A, w i) := by
  classical
  let family : Finset (Finset β) := Finset.univ.powersetCard T
  have hfamily : family.Nonempty := by
    change (Finset.univ.powersetCard T).Nonempty
    rw [Finset.powersetCard_nonempty]
    simpa using hT
  obtain ⟨A, hAfamily, hmax⟩ :=
    Finset.exists_max_image family (fun s ↦ ∑ i ∈ s, w i) hfamily
  have hAsub : A ⊆ Finset.univ :=
    (Finset.mem_powersetCard.mp hAfamily).1
  have hAcard : A.card = T :=
    (Finset.mem_powersetCard.mp hAfamily).2
  have houtside : ∀ i ∈ Finset.univ \ A, T * w i ≤ ∑ j ∈ A, w j := by
    intro i hi
    have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
    rw [← hAcard]
    exact Finset.card_nsmul_le_sum A w (w i) fun j hj ↦ by
      have hswap_mem : insert i (A.erase j) ∈ family := by
        change insert i (A.erase j) ∈ Finset.univ.powersetCard T
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_erase_of_mem hj, hAcard]
          have hTpos : 0 < T := by
            rw [← hAcard, Finset.card_pos]
            exact ⟨j, hj⟩
          omega
        · simp [hiA]
      have hswap := hmax (insert i (A.erase j)) hswap_mem
      have hsumA : ∑ x ∈ A, w x = w j + ∑ x ∈ A.erase j, w x := by
        rw [← Finset.sum_erase_add _ _ hj, Nat.add_comm]
      have hsumSwap : ∑ x ∈ insert i (A.erase j), w x =
          w i + ∑ x ∈ A.erase j, w x := by
        rw [Finset.sum_insert]
        simp [hiA]
      rw [hsumSwap, hsumA] at hswap
      exact Nat.le_of_add_le_add_right hswap
  refine ⟨A, hAcard, ?_⟩
  have hsum_out :
      T * (∑ i ∈ Finset.univ \ A, w i) ≤
        (Finset.univ \ A).card * (∑ j ∈ A, w j) := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ Finset.univ \ A, T * w i ≤
          ∑ _i ∈ Finset.univ \ A, ∑ j ∈ A, w j := by
            exact Finset.sum_le_sum fun i hi ↦ houtside i hi
      _ = (Finset.univ \ A).card * (∑ j ∈ A, w j) := by simp
  have hcard_out : (Finset.univ \ A).card + T = Fintype.card β := by
    calc
      (Finset.univ \ A).card + T = (Finset.univ \ A).card + A.card := by
        rw [hAcard]
      _ = Finset.univ.card := Finset.card_sdiff_add_card_eq_card hAsub
      _ = Fintype.card β := Finset.card_univ
  have hsum_split :
      (∑ i, w i) = (∑ i ∈ A, w i) + ∑ i ∈ Finset.univ \ A, w i := by
    rw [← Finset.sum_union]
    · congr 1
      exact (Finset.union_sdiff_of_subset hAsub).symm
    · exact Finset.disjoint_sdiff
  rw [hsum_split, Nat.mul_add, ← hcard_out, Nat.add_mul]
  simpa [Nat.add_comm] using
    Nat.add_le_add_left hsum_out (T * (∑ i ∈ A, w i))

end Erdos182

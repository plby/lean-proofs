import ErdosProblems.Erdos964.ScalarCandidateSums

/-!
# Extracting two simultaneous events from a positive weighted excess
-/

namespace Erdos964

open scoped Classical in
theorem exists_two_of_sum_filtered_weights_gt (S : Finset ℕ) (w : ℕ → ℝ)
    (P : Fin 3 → ℕ → Prop) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hbig : (∑ n ∈ S, w n) < ∑ i : Fin 3, ∑ n ∈ S.filter (P i), w n) :
    ∃ n ∈ S, ∃ i j : Fin 3, i < j ∧ P i n ∧ P j n := by
  classical
  by_contra hnone
  have hsingle (n : ℕ) (hn : n ∈ S) (i j : Fin 3) (hi : P i n) (hj : P j n) : i = j := by
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hnone ⟨n, hn, i, j, hij, hi, hj⟩
    · exact hnone ⟨n, hn, j, i, hji, hj, hi⟩
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (∑ i : Fin 3, if P i n then w n else 0) ≤ w n := by
    let I := (Finset.univ : Finset (Fin 3)).filter (fun i => P i n)
    have hcard : I.card ≤ 1 := Finset.card_le_one.mpr (by
      intro i hi j hj
      exact hsingle n hn i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    calc
      _ = ∑ _i ∈ I, w n := by simp only [I, Finset.sum_filter]
      _ = (I.card : ℝ) * w n := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * w n := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hw n hn)
      _ = w n := one_mul _
  have hle : (∑ i : Fin 3, ∑ n ∈ S.filter (P i), w n) ≤ ∑ n ∈ S, w n := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum hpoint
  exact (not_lt_of_ge hle) hbig

theorem exists_infinite_pair_of_unbounded (P : Fin 3 → ℕ → Prop)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ i j : Fin 3, i < j ∧ P i n ∧ P j n) :
    ∃ i j : Fin 3, i < j ∧ {n : ℕ | P i n ∧ P j n}.Infinite := by
  classical
  let S : Fin 3 × Fin 3 → Set ℕ := fun ij => {n | ij.1 < ij.2 ∧ P ij.1 n ∧ P ij.2 n}
  have hinf : (⋃ ij, S ij).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨n, hBn, i, j, hij, hi, hj⟩ := h B
    exact ⟨n, Set.mem_iUnion.mpr ⟨(i, j), hij, hi, hj⟩, hBn⟩
  by_contra hnone
  have hfinite (ij : Fin 3 × Fin 3) : (S ij).Finite := by
    by_cases hij : ij.1 < ij.2
    · have hpair : ¬ {n : ℕ | P ij.1 n ∧ P ij.2 n}.Infinite :=
        fun hi => hnone ⟨ij.1, ij.2, hij, hi⟩
      exact (Set.not_infinite.mp hpair).subset (fun n hn => hn.2)
    · have hz : S ij = ∅ := by
        ext n
        simp only [S, Set.mem_ofPred_eq, hij, false_and, Set.mem_empty_iff_false]
      rw [hz]
      exact Set.finite_empty
  exact hinf (Set.finite_iUnion hfinite)

end Erdos964

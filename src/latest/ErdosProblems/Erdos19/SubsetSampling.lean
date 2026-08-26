import ErdosProblems.Erdos19.LocalConcentration

/-! # Simultaneous subset sampling with different error tolerances -/

namespace Erdos19

open Finset

theorem bin_count_deviation_cardRatio_le_of_card_le
    {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [Nonempty K]
    [DecidableEq K] (S : Finset V) (a : K) (t L : ℝ)
    (ht : 0 < t) (hL : 0 < L) (hsize : (S.card : ℝ) ≤ L) :
    (({z : V → K | t ≤ |uniformBinCount S a z - (S.card : ℝ) / Fintype.card K|} :
      Set (V → K)).ncard : ℝ) / Fintype.card (V → K) ≤
        2 * Real.exp (-t ^ 2 / (2 * L)) := by
  classical
  by_cases hS : S.Nonempty
  · apply (bin_count_deviation_cardRatio_le S hS a t ht.le).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hm := mul_le_mul_of_nonneg_left hsize (sq_nonneg t)
    nlinarith only [hm]
  · have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    have hbad : {z : V → K | t ≤ |uniformBinCount S a z -
        (S.card : ℝ) / Fintype.card K|} = ∅ := by
      ext z
      simp only [hSempty, uniformBinCount, sum_empty, card_empty, Nat.cast_zero,
        zero_div, sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      exact not_le.mpr ht
    rw [hbad, Set.ncard_empty, Nat.cast_zero, zero_div]
    positivity

theorem exists_uniform_bin_sample_close
    {V K I : Type*} [Fintype V] [DecidableEq V] [Fintype K] [Nonempty K]
    [DecidableEq K] [Fintype I] (S : I → Finset V) (a : K)
    (t L : I → ℝ) (ht : ∀ i, 0 < t i) (hL : ∀ i, 0 < L i)
    (hsize : ∀ i, ((S i).card : ℝ) ≤ L i)
    (hprob : (∑ i, 2 * Real.exp (-(t i) ^ 2 / (2 * L i))) < 1) :
    ∃ z : V → K, ∀ i,
      |uniformBinCount (S i) a z - ((S i).card : ℝ) / Fintype.card K| < t i := by
  classical
  let bad : I → Set (V → K) := fun i ↦
    {z | t i ≤ |uniformBinCount (S i) a z - ((S i).card : ℝ) / Fintype.card K|}
  let q : ℝ := Fintype.card (V → K)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos
  have hbad : ∀ i, ((bad i).ncard : ℝ) ≤
      (2 * Real.exp (-(t i) ^ 2 / (2 * L i))) * q := by
    intro i
    exact (div_le_iff₀ hq).mp
      (bin_count_deviation_cardRatio_le_of_card_le (S i) a (t i) (L i)
        (ht i) (hL i) (hsize i))
  have hsum : (∑ i, ((bad i).ncard : ℝ)) < q := by
    calc
      (∑ i, ((bad i).ncard : ℝ)) ≤
          ∑ i, (2 * Real.exp (-(t i) ^ 2 / (2 * L i))) * q :=
        sum_le_sum (fun i _ ↦ hbad i)
      _ = (∑ i, 2 * Real.exp (-(t i) ^ 2 / (2 * L i))) * q := (sum_mul _ _ _).symm
      _ < q := by simpa only [one_mul] using mul_lt_mul_of_pos_right hprob hq
  have hcount : (∑ i, (bad i).ncard) < Fintype.card (V → K) := by
    dsimp only [q] at hsum
    exact_mod_cast hsum
  obtain ⟨z, hz⟩ := exists_avoiding_of_sum_ncard_lt_card bad hcount
  exact ⟨z, fun i ↦ lt_of_not_ge (hz i)⟩

theorem exists_subset_with_simultaneous_counts
    {V K I : Type*} [Fintype V] [DecidableEq V] [Fintype K] [Nonempty K]
    [DecidableEq K] [Fintype I] (U : Finset V) (S : I → Finset V)
    (hSU : ∀ i, S i ⊆ U) (a : K) (t L : I → ℝ)
    (ht : ∀ i, 0 < t i) (hL : ∀ i, 0 < L i)
    (hsize : ∀ i, ((S i).card : ℝ) ≤ L i)
    (hprob : (∑ i, 2 * Real.exp (-(t i) ^ 2 / (2 * L i))) < 1) :
    ∃ R : Finset V, R ⊆ U ∧ ∀ i,
      |((S i ∩ R).card : ℝ) - ((S i).card : ℝ) / Fintype.card K| < t i := by
  classical
  obtain ⟨z, hz⟩ := exists_uniform_bin_sample_close S a t L ht hL hsize hprob
  let R := U.filter fun v ↦ z v = a
  refine ⟨R, filter_subset _ _, ?_⟩
  intro i
  have hinter : S i ∩ R = (S i).filter fun v ↦ z v = a := by
    ext v
    simp only [R, mem_inter, mem_filter]
    constructor
    · exact fun hv ↦ ⟨hv.1, hv.2.2⟩
    · exact fun hv ↦ ⟨hv.1, hSU i hv.1, hv.2⟩
  rw [hinter]
  simpa only [uniformBinCount_eq_card] using hz i

#print axioms exists_subset_with_simultaneous_counts

end Erdos19

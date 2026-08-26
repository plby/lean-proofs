import ErdosProblems.Erdos19.Core

/-! # Simultaneous concentration on a finite uniform product space -/

namespace Erdos19

open Finset

theorem uniform_abs_deviation_cardRatio_le
    {K : Type*} [Fintype K] [Nonempty K]
    (n : ℕ) (hn : 0 < n) (F : (Fin n → K) → ℝ)
    (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hLip : RealCoordinateLipschitzFin F c) :
    (({z : Fin n → K | t ≤ |F z - finiteAverage F|} : Set (Fin n → K)).ncard : ℝ) /
        Fintype.card (Fin n → K) ≤ 2 * Real.exp (-t ^ 2 / (2 * n * c ^ 2)) := by
  classical
  let L := finiteLowerTail F t
  let U := finiteLowerTail (fun z ↦ -F z) t
  let p := Real.exp (-t ^ 2 / (2 * n * c ^ 2))
  let q : ℝ := Fintype.card (Fin n → K)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos
  have hneg : RealCoordinateLipschitzFin (fun z ↦ -F z) c := by
    intro x y i hxy
    simpa only [neg_sub_neg, abs_sub_comm] using hLip x y i hxy
  have hL : (L.card : ℝ) ≤ p * q :=
    (div_le_iff₀ hq).mp (finite_boundedDifferences_lowerTail n F hc ht hn hLip)
  have hU : (U.card : ℝ) ≤ p * q :=
    (div_le_iff₀ hq).mp (finite_boundedDifferences_lowerTail n (fun z ↦ -F z) hc ht hn hneg)
  have hsub : {z : Fin n → K | t ≤ |F z - finiteAverage F|} ⊆
      (L : Set (Fin n → K)) ∪ (U : Set (Fin n → K)) := by
    intro z hz
    change t ≤ |F z - finiteAverage F| at hz
    rcases le_abs.mp hz with hz | hz
    · right
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      simpa only [finiteAverage_neg, sub_neg_eq_add, sub_eq_add_neg, add_comm, neg_neg] using hz
    · left
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      linarith
  have hcard : ({z : Fin n → K | t ≤ |F z - finiteAverage F|} : Set (Fin n → K)).ncard ≤
      L.card + U.card := by
    exact (Set.ncard_le_ncard hsub).trans (by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_union_le (L : Set (Fin n → K)) (U : Set (Fin n → K)))
  apply (div_le_iff₀ hq).2
  have hcardR : (({z : Fin n → K | t ≤ |F z - finiteAverage F|} : Set (Fin n → K)).ncard : ℝ) ≤
      L.card + U.card := by exact_mod_cast hcard
  change _ ≤ (2 * p) * q
  linarith

theorem exists_uniform_sample_close_means
    {K I : Type*} [Fintype K] [Nonempty K] [Fintype I]
    (n : ℕ) (hn : 0 < n) (F : I → (Fin n → K) → ℝ)
    (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hLip : ∀ i, RealCoordinateLipschitzFin (F i) c)
    (hprob : 2 * Fintype.card I * Real.exp (-t ^ 2 / (2 * n * c ^ 2)) < 1) :
    ∃ z : Fin n → K, ∀ i, |F i z - finiteAverage (F i)| < t := by
  classical
  let G : I × Bool → (Fin n → K) → ℝ := fun i ↦
    if i.2 then F i.1 else fun z ↦ -F i.1 z
  let bad : I × Bool → Set (Fin n → K) := fun i ↦ ↑(finiteLowerTail (G i) t)
  let p := Real.exp (-t ^ 2 / (2 * n * c ^ 2))
  let q : ℝ := Fintype.card (Fin n → K)
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast Fintype.card_pos
  have hGLip : ∀ i, RealCoordinateLipschitzFin (G i) c := by
    rintro ⟨i, b⟩
    cases b
    · intro x y j hxy
      simpa only [G, Bool.false_eq_true, ↓reduceIte, neg_sub_neg, abs_sub_comm] using
        hLip i x y j hxy
    · simpa only [G, ↓reduceIte] using hLip i
  have hbad : ∀ i, ((bad i).ncard : ℝ) ≤ p * q := by
    intro i
    have htail := finite_boundedDifferences_lowerTail n (G i) hc ht hn (hGLip i)
    have hmul := (div_le_iff₀ hq).mp htail
    simpa only [bad, Set.ncard_coe_finset] using hmul
  have hsum : (∑ i : I × Bool, ((bad i).ncard : ℝ)) ≤
      (2 * Fintype.card I * p) * q := by
    calc
      (∑ i : I × Bool, ((bad i).ncard : ℝ)) ≤ ∑ _i : I × Bool, p * q :=
        sum_le_sum (fun i _ ↦ hbad i)
      _ = (2 * Fintype.card I * p) * q := by
        simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have htotal : (∑ i : I × Bool, (bad i).ncard) < Fintype.card (Fin n → K) := by
    have hstrict : (∑ i : I × Bool, ((bad i).ncard : ℝ)) < q := by
      exact hsum.trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right hprob hq)
    dsimp only [q] at hstrict
    exact_mod_cast hstrict
  obtain ⟨z, hz⟩ := exists_avoiding_of_sum_ncard_lt_card bad htotal
  refine ⟨z, ?_⟩
  intro i
  have hlo : finiteAverage (F i) - F i z < t := by
    have h := hz (i, true)
    simpa only [bad, mem_coe, finiteLowerTail, mem_filter, mem_univ, true_and,
      G, ↓reduceIte, not_le] using h
  have hhi : F i z - finiteAverage (F i) < t := by
    have h := hz (i, false)
    simpa only [bad, mem_coe, finiteLowerTail, mem_filter, mem_univ, true_and,
      G, Bool.false_eq_true, ↓reduceIte, finiteAverage_neg, sub_neg_eq_add, not_le,
      sub_eq_add_neg, add_comm, neg_neg] using h
  exact abs_lt.mpr ⟨by linarith, hhi⟩

#print axioms exists_uniform_sample_close_means
#print axioms uniform_abs_deviation_cardRatio_le

end Erdos19

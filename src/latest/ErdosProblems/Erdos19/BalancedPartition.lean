import ErdosProblems.Erdos19.UniformConcentration

/-! # Simultaneously balancing a finite family across blocks -/

namespace Erdos19

open Finset

theorem finiteAverage_finset_sum {Ω I : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset I) (F : I → Ω → ℝ) :
    finiteAverage (fun z ↦ ∑ i ∈ S, F i z) = ∑ i ∈ S, finiteAverage (F i) := by
  unfold finiteAverage
  rw [sum_comm, sum_div]

theorem finiteAverage_eval_indicator {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]
    [Nonempty K] [DecidableEq K] (v : V) (a : K) :
    finiteAverage (fun z : V → K ↦ if z v = a then (1 : ℝ) else 0) =
      1 / Fintype.card K := by
  classical
  let E := Equiv.funSplitAt v K
  have h := finiteAverage_comp_equiv E
    (fun p : K × ({w : V // w ≠ v} → K) ↦ if p.1 = a then (1 : ℝ) else 0)
  change finiteAverage (fun z : V → K ↦ if z v = a then (1 : ℝ) else 0) = _ at h
  rw [h]
  have hrest : (Fintype.card ({w : V // w ≠ v} → K) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ({w : V // w ≠ v} → K) ≠ 0)
  have hinner (x : K) :
      (∑ _z : ({w : V // w ≠ v} → K), if x = a then (1 : ℝ) else 0) =
        if x = a then (Fintype.card ({w : V // w ≠ v} → K) : ℝ) else 0 := by
    by_cases hxa : x = a <;> simp only [hxa, ↓reduceIte, sum_const,
      card_univ, nsmul_eq_mul, mul_one, mul_zero]
  have hsum : (∑ p : K × ({w : V // w ≠ v} → K), if p.1 = a then (1 : ℝ) else 0) =
      (Fintype.card ({w : V // w ≠ v} → K) : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hinner]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  rw [finiteAverage, hsum, Fintype.card_prod, Nat.cast_mul]
  field_simp

def uniformBinCount {V K : Type*} [DecidableEq K]
    (S : Finset V) (a : K) (z : V → K) : ℝ :=
  ∑ v ∈ S, if z v = a then 1 else 0

theorem uniformBinCount_eq_card {V K : Type*} [DecidableEq K]
    (S : Finset V) (a : K) (z : V → K) :
    uniformBinCount S a z = ((S.filter fun v ↦ z v = a).card : ℝ) := by
  simp [uniformBinCount]

theorem finiteAverage_uniformBinCount {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]
    [Nonempty K] [DecidableEq K] (S : Finset V) (a : K) :
    finiteAverage (uniformBinCount S a) = (S.card : ℝ) / Fintype.card K := by
  change finiteAverage (fun z : V → K ↦ ∑ v ∈ S, if z v = a then (1 : ℝ) else 0) = _
  rw [finiteAverage_finset_sum]
  simp only [finiteAverage_eval_indicator, sum_const, nsmul_eq_mul]
  ring

theorem uniformBinCount_coordinate_bound {V K : Type*} [DecidableEq K]
    (S : Finset V) (a : K) :
    ∀ x y : V → K, ∀ i : V, (∀ j, j ≠ i → x j = y j) →
      |uniformBinCount S a x - uniformBinCount S a y| ≤ 1 := by
  classical
  intro x y i hxy
  by_cases hi : i ∈ S
  · have heq : (∑ j ∈ S.erase i, if x j = a then (1 : ℝ) else 0) =
        ∑ j ∈ S.erase i, if y j = a then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [hxy j (mem_erase.mp hj).1]
    unfold uniformBinCount
    rw [← S.sum_erase_add (fun j ↦ if x j = a then (1 : ℝ) else 0) hi,
      ← S.sum_erase_add (fun j ↦ if y j = a then (1 : ℝ) else 0) hi, heq]
    by_cases hx : x i = a <;> by_cases hy : y i = a <;> simp [hx, hy]
  · have heq : uniformBinCount S a x = uniformBinCount S a y := by
      apply sum_congr rfl
      intro j hj
      rw [hxy j (fun hji ↦ hi (hji ▸ hj))]
    simp only [heq, sub_self, abs_zero]
    norm_num

theorem uniformBinCount_lipschitz {K : Type*} [DecidableEq K]
    {n : ℕ} (S : Finset (Fin n)) (a : K) :
    RealCoordinateLipschitzFin (uniformBinCount S a) 1 :=
  uniformBinCount_coordinate_bound S a

theorem exists_balanced_partition {I K : Type*} [Fintype I] [Fintype K]
    [Nonempty K] [DecidableEq K] (n : ℕ) (hn : 0 < n)
    (S : I → Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t)
    (hprob : 2 * Fintype.card I * Fintype.card K * Real.exp (-t ^ 2 / (2 * n)) < 1) :
    ∃ z : Fin n → K, ∀ i a,
      |(((S i).filter fun v ↦ z v = a).card : ℝ) -
          (S i).card / Fintype.card K| < t := by
  classical
  obtain ⟨z, hz⟩ := exists_uniform_sample_close_means n hn
    (fun i : I × K ↦ uniformBinCount (S i.1) i.2) 1 t (by norm_num) ht
    (fun i ↦ uniformBinCount_lipschitz _ _) (by
      simpa only [Fintype.card_prod, Nat.cast_mul, one_pow, mul_one, mul_assoc] using hprob)
  refine ⟨z, ?_⟩
  intro i a
  simpa only [uniformBinCount_eq_card, finiteAverage_uniformBinCount] using hz (i, a)

#print axioms finiteAverage_eval_indicator
#print axioms exists_balanced_partition

end Erdos19

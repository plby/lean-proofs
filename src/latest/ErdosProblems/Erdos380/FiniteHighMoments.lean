import ErdosProblems.Erdos380.FiniteProbability
import ErdosProblems.Erdos380.AntiSieve

/-!
# High moments from bounded-order joint event estimates

Only intersections of at most `k` events are used to bound the `k`th moment.
No assertion of independence or unrestricted exponential-moment estimate
is made.
-/

open scoped BigOperators Classical

namespace Erdos380

theorem sum_pow_le_pow_mul_smallSubsets_prod_of_tuple_extension
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℝ) (J : Finset I) (k : ℕ)
    (hw : ∀ i, 0 ≤ w i)
    (hextend : ∀ p ∈ Fintype.piFinset (fun _ : Fin k => J),
      ∃ U ∈ ((Finset.univ : Finset I).powerset.filter fun U => U.card ≤ k),
        (∀ j, p j ∈ U) ∧ (∏ j, w (p j)) ≤ ∏ i ∈ U, w i) :
    (∑ i ∈ J, w i) ^ k ≤
      (k : ℝ) ^ k *
        ∑ U ∈ ((Finset.univ : Finset I).powerset.filter fun U => U.card ≤ k),
          ∏ i ∈ U, w i := by
  classical
  let P := Fintype.piFinset (fun _ : Fin k => J)
  let K := ((Finset.univ : Finset I).powerset.filter fun U => U.card ≤ k)
  rw [Finset.sum_pow']
  calc
    (∑ p ∈ P, ∏ j, w (p j)) ≤
        ∑ p ∈ P, ∑ U ∈ K,
          if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨U, hUK, hpU, hpWeight⟩ := hextend p (by simpa [P] using hp)
      calc
        (∏ j, w (p j)) ≤ ∏ i ∈ U, w i := hpWeight
        _ = if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
          simp [hpU]
        _ ≤ ∑ V ∈ K,
            if ∀ j, p j ∈ V then ∏ i ∈ V, w i else 0 := by
          exact Finset.single_le_sum
            (s := K)
            (f := fun V =>
              if ∀ j, p j ∈ V then (∏ i ∈ V, w i) else (0 : ℝ))
            (fun V _hV => by
              by_cases hpV : ∀ j, p j ∈ V
              · simp [hpV, Finset.prod_nonneg fun i _ => hw i]
              · simp [hpV])
            (by simpa [K] using hUK)
    _ = ∑ U ∈ K, ∑ p ∈ P,
          if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ U ∈ K, (k : ℝ) ^ k * ∏ i ∈ U, w i := by
      apply Finset.sum_le_sum
      intro U hUK
      have hUcard : U.card ≤ k := (Finset.mem_filter.mp hUK).2
      let good := P.filter fun p => ∀ j, p j ∈ U
      have hgoodSubset : good ⊆ Fintype.piFinset (fun _ : Fin k => U) := by
        intro p hp
        have hpU : ∀ j, p j ∈ U := (Finset.mem_filter.mp hp).2
        exact Fintype.mem_piFinset.mpr hpU
      have hgoodCard : good.card ≤ k ^ k := by
        calc
          good.card ≤ (Fintype.piFinset (fun _ : Fin k => U)).card :=
            Finset.card_le_card hgoodSubset
          _ = U.card ^ k := Fintype.card_piFinset_const U k
          _ ≤ k ^ k := Nat.pow_le_pow_left hUcard k
      calc
        (∑ p ∈ P,
            if ∀ j, p j ∈ U then ∏ i ∈ U, w i else 0) =
            (good.card : ℝ) * ∏ i ∈ U, w i := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k ^ k : ℕ) : ℝ) * ∏ i ∈ U, w i := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgoodCard)
            (Finset.prod_nonneg fun i _ => hw i)
        _ = (k : ℝ) ^ k * ∏ i ∈ U, w i := by
          norm_num
    _ = (k : ℝ) ^ k *
        ∑ U ∈ K, ∏ i ∈ U, w i := by
      rw [Finset.mul_sum]


lemma prod_comp_le_prod_image_of_le_one
    {I J : Type*} [DecidableEq I] (s : Finset J) (f : J → I) (w : I → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) :
    (∏ j ∈ s, w (f j)) ≤ ∏ i ∈ s.image f, w i := by
  classical
  rw [Finset.prod_comp]
  apply Finset.prod_le_prod
  · intro i _
    exact pow_nonneg (hw0 i) _
  · intro i hi
    apply pow_le_of_le_one (hw0 i) (hw1 i)
    apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hji⟩⟩

/-- A deterministic inequality that uses only products of at most `k`
distinct factors. -/
theorem sum_pow_le_smallSubsets
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℝ) (k : ℕ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) :
    (∑ i, w i) ^ k ≤ (k : ℝ) ^ k *
      ∑ U ∈ ((Finset.univ : Finset I).powerset.filter fun U => U.card ≤ k),
        ∏ i ∈ U, w i := by
  apply sum_pow_le_pow_mul_smallSubsets_prod_of_tuple_extension w Finset.univ k hw0
  intro p _hp
  let U : Finset I := Finset.univ.image p
  refine ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩,
    fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · exact prod_comp_le_prod_image_of_le_one Finset.univ p w hw0 hw1

lemma sum_powerset_prod_le_exp {I : Type*} (s : Finset I) (b : I → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ U ∈ s.powerset, ∏ i ∈ U, b i) ≤ Real.exp (∑ i ∈ s, b i) := by
  rw [← Finset.prod_one_add, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [hb i hi]
  · intro i _hi
    simpa only [add_comm] using Real.add_one_le_exp (b i)

/-- A finite high-moment inequality from joint-event bounds through order
`k`.  Higher-order intersections are not hypotheses. -/
theorem finite_high_moment_from_joint_bounds
    {I Ω : Type*} [Fintype I] [DecidableEq I]
    (s : Finset Ω) (w b : I → ℝ) (E : I → Ω → Prop) (k : ℕ) (C : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hb : ∀ i, 0 ≤ b i) (hC : 0 ≤ C)
    (hjoint : ∀ U : Finset I, U.card ≤ k →
      (𝔼 ω ∈ s, ∏ i ∈ U, if E i ω then (1 : ℝ) else 0) ≤ C * ∏ i ∈ U, b i) :
    (𝔼 ω ∈ s, (∑ i, w i * if E i ω then (1 : ℝ) else 0) ^ k) ≤
      C * (k : ℝ) ^ k * Real.exp (∑ i, w i * b i) := by
  classical
  let K := (Finset.univ : Finset I).powerset.filter fun U => U.card ≤ k
  have hpoint (ω : Ω) :
      (∑ i, w i * if E i ω then (1 : ℝ) else 0) ^ k ≤
        (k : ℝ) ^ k * ∑ U ∈ K, ∏ i ∈ U, w i * if E i ω then (1 : ℝ) else 0 := by
    apply sum_pow_le_smallSubsets (fun i => w i * if E i ω then (1 : ℝ) else 0) k
    · intro i
      split_ifs <;> simp [hw0 i]
    · intro i
      split_ifs <;> simp [hw1 i]
  have hsubset (U : Finset I) (hU : U ∈ K) :
      (𝔼 ω ∈ s, ∏ i ∈ U, w i * if E i ω then (1 : ℝ) else 0) ≤
        C * ∏ i ∈ U, w i * b i := by
    simp_rw [Finset.prod_mul_distrib, ← Finset.mul_expect]
    calc
      _ ≤ (∏ i ∈ U, w i) * (C * ∏ i ∈ U, b i) :=
        mul_le_mul_of_nonneg_left (hjoint U (Finset.mem_filter.mp hU).2)
          (Finset.prod_nonneg fun i _ => hw0 i)
      _ = _ := by ring
  calc
    _ ≤ 𝔼 ω ∈ s, (k : ℝ) ^ k *
        ∑ U ∈ K, ∏ i ∈ U, w i * if E i ω then (1 : ℝ) else 0 :=
      Finset.expect_le_expect fun ω _ => hpoint ω
    _ = (k : ℝ) ^ k * ∑ U ∈ K,
        𝔼 ω ∈ s, ∏ i ∈ U, w i * if E i ω then (1 : ℝ) else 0 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ (k : ℝ) ^ k * ∑ U ∈ K, C * ∏ i ∈ U, w i * b i :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsubset) (by positivity)
    _ = C * (k : ℝ) ^ k * ∑ U ∈ K, ∏ i ∈ U, w i * b i := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ C * (k : ℝ) ^ k *
        ∑ U ∈ (Finset.univ : Finset I).powerset, ∏ i ∈ U, w i * b i := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun U _ _ => Finset.prod_nonneg fun i _ => mul_nonneg (hw0 i) (hb i))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_powerset_prod_le_exp Finset.univ (fun i => w i * b i)
        (fun i _ => mul_nonneg (hw0 i) (hb i))) (by positivity)

lemma finite_expect_le_of_nonneg {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ ω ∈ s, f ω ≤ C) : (𝔼 ω ∈ s, f ω) ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  · exact Finset.expect_le hs hf

lemma finite_sum_fiftieth_moment_le {I Ω : Type*} (J : Finset I) (s : Finset Ω)
    (f : I → Ω → ℝ) (K : ℝ)
    (hf : ∀ i ∈ J, ∀ ω ∈ s, 0 ≤ f i ω)
    (hmoment : ∀ i ∈ J, (𝔼 ω ∈ s, f i ω ^ 50) ≤ K) :
    (𝔼 ω ∈ s, (∑ i ∈ J, f i ω) ^ 50) ≤ (J.card : ℝ) ^ 50 * K := by
  have hpoint (ω : Ω) (hω : ω ∈ s) :
      (∑ i ∈ J, f i ω) ^ 50 ≤ (J.card : ℝ) ^ 49 * ∑ i ∈ J, f i ω ^ 50 := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J (f := fun i => f i ω)
      (by norm_num : (1 : ℝ) ≤ 50) (fun i hi => hf i hi ω hω)
    norm_num only [show (50 : ℝ) - 1 = 49 by norm_num, Real.rpow_ofNat] at h
    exact h
  calc
    _ ≤ 𝔼 ω ∈ s, (J.card : ℝ) ^ 49 * ∑ i ∈ J, f i ω ^ 50 :=
      Finset.expect_le_expect hpoint
    _ = (J.card : ℝ) ^ 49 * ∑ i ∈ J, 𝔼 ω ∈ s, f i ω ^ 50 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ (J.card : ℝ) ^ 49 * ∑ _i ∈ J, K :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmoment) (by positivity)
    _ = _ := by simp [pow_succ, mul_assoc]

theorem finite_markov_pow {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ)
    (k : ℕ) {U : ℝ} (hU : 0 < U) (hf : ∀ ω ∈ s, 0 ≤ f ω) :
    ((s.filter fun ω => U ≤ f ω).card : ℝ) / (s.card : ℝ) ≤
      (𝔼 ω ∈ s, f ω ^ k) / U ^ k := by
  classical
  have hcount : ((s.filter fun ω => U ≤ f ω).card : ℝ) * U ^ k ≤ ∑ ω ∈ s, f ω ^ k := by
    calc
      _ = ∑ _ω ∈ s.filter (fun ω => U ≤ f ω), U ^ k := by simp
      _ ≤ ∑ ω ∈ s.filter (fun ω => U ≤ f ω), f ω ^ k :=
        Finset.sum_le_sum fun ω hω => pow_le_pow_left₀ hU.le (Finset.mem_filter.mp hω).2 k
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω hω _ => pow_nonneg (hf ω hω) _)
  apply (le_div_iff₀ (pow_pos hU k)).mpr
  rw [Finset.expect_eq_sum_div_card]
  have hdiv := div_le_div_of_nonneg_right hcount (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
  convert hdiv using 1 <;> ring

theorem finite_sum_fiftieth_tail_le {I Ω : Type*} (J : Finset I) (hJ : J.Nonempty)
    (s : Finset Ω) (f : I → Ω → ℝ) (K : ℝ)
    (hf : ∀ i ∈ J, ∀ ω ∈ s, 0 ≤ f i ω)
    (hmoment : ∀ i ∈ J, (𝔼 ω ∈ s, f i ω ^ 50) ≤ K)
    {U : ℝ} (hU : 0 < U) :
    ((s.filter fun ω => (J.card : ℝ) * U ≤ ∑ i ∈ J, f i ω).card : ℝ) / (s.card : ℝ) ≤
      K / U ^ 50 := by
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have hm := finite_markov_pow s (fun ω => ∑ i ∈ J, f i ω) 50 (mul_pos hJpos hU)
    (fun ω hω => Finset.sum_nonneg fun i hi => hf i hi ω hω)
  have hbound := finite_sum_fiftieth_moment_le J s f K hf hmoment
  apply hm.trans
  calc
    _ ≤ ((J.card : ℝ) ^ 50 * K) / ((J.card : ℝ) * U) ^ 50 :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

end Erdos380

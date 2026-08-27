import ErdosProblems.Erdos587.HooleyDivisorCounting
import ErdosProblems.Erdos587.HooleyTotientRatio
import ErdosProblems.Erdos402.SieveDenominator

/-!
# The single log-log cost of the nonzero error gcds

The exact positive-error divisor count loses no additive divisor term.
An Euler-product bound and the maximal-order totient estimate then
give the seventh log-log power in the quadratic counting application.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_sum_divisor_reciprocal_le_totient {q : ℕ} (hq : 0 < q) :
    (∑ d ∈ q.divisors, (1 : ℝ) / d) ≤ (q : ℝ) / q.totient := by
  apply Erdos402.Sieve.sum_factored_inv_le hq q.divisors
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  apply Nat.mem_factoredNumbers_of_primeFactors_subset hd0
  exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hq.ne'

theorem exists_delta_gcd_divisor_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q T : ℕ, 0 < q →
      (∑ t ∈ Finset.Ioc 0 T, ((q.gcd t).divisors.card : ℝ)) ≤
        C * T * max 1 (Real.log (Real.log (q : ℝ))) := by
  obtain ⟨C, hC, hratio⟩ := exists_delta_totient_ratio_bound
  refine ⟨C, hC, ?_⟩
  intro q T hq
  calc
    _ ≤ (T : ℝ) * ∑ d ∈ q.divisors, (1 : ℝ) / d :=
      sum_Ioc_card_divisors_gcd_le hq.ne' T
    _ ≤ (T : ℝ) * ((q : ℝ) / q.totient) :=
      mul_le_mul_of_nonneg_left (delta_sum_divisor_reciprocal_le_totient hq) (by positivity)
    _ ≤ (T : ℝ) * (C * max 1 (Real.log (Real.log (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hratio q q hq le_rfl) (by positivity)
    _ = _ := by ring

lemma delta_sum_natAbs_le_twice (S : Finset ℤ) (T : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hzero : ∀ t ∈ S, t ≠ 0)
    (hbound : ∀ t ∈ S, t.natAbs ≤ T) :
    (∑ t ∈ S, f t.natAbs) ≤ 2 * ∑ n ∈ Finset.Ioc 0 T, f n := by
  classical
  let P : Finset ℤ := (Finset.Ioc 0 T).image (fun n : ℕ => (n : ℤ))
  let M : Finset ℤ := (Finset.Ioc 0 T).image (fun n : ℕ => -(n : ℤ))
  have hsub : S ⊆ P ∪ M := by
    intro t ht
    have hn : t.natAbs ∈ Finset.Ioc 0 T :=
      Finset.mem_Ioc.mpr ⟨Int.natAbs_pos.mpr (hzero t ht), hbound t ht⟩
    rcases Int.natAbs_eq t with hp | hm
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨t.natAbs, hn, hp.symm⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨t.natAbs, hn, by omega⟩))
  have hdisjoint : Disjoint P M := by
    apply Finset.disjoint_left.mpr
    intro t htP htM
    obtain ⟨p, hp, hpEq⟩ := Finset.mem_image.mp htP
    obtain ⟨m, hm, hmEq⟩ := Finset.mem_image.mp htM
    have hp0 := (Finset.mem_Ioc.mp hp).1
    have hm0 := (Finset.mem_Ioc.mp hm).1
    omega
  have hP : (∑ t ∈ P, f t.natAbs) = ∑ n ∈ Finset.Ioc 0 T, f n := by
    rw [Finset.sum_image]
    · simp only [Int.natAbs_natCast]
    · intro x hx y hy hxy
      change (x : ℤ) = (y : ℤ) at hxy
      exact_mod_cast hxy
  have hM : (∑ t ∈ M, f t.natAbs) = ∑ n ∈ Finset.Ioc 0 T, f n := by
    rw [Finset.sum_image]
    · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    · intro x hx y hy hxy
      change -(x : ℤ) = -(y : ℤ) at hxy
      have hcast := neg_injective hxy
      exact_mod_cast hcast
  calc
    _ ≤ ∑ t ∈ P ∪ M, f t.natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hf t.natAbs)
    _ = (∑ t ∈ P, f t.natAbs) + ∑ t ∈ M, f t.natAbs := Finset.sum_union hdisjoint
    _ = _ := by rw [hP, hM]; ring

/-- The real tolerance may be less than one. Nonzero errors are excluded
before rounding, so there is no additive `τ(q)` term. -/
theorem exists_delta_signed_gcd_divisor_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ T : ℝ, 0 ≤ T →
      ∀ S : Finset ℤ, (∀ t ∈ S, t ≠ 0) → (∀ t ∈ S, (t.natAbs : ℝ) ≤ T) →
      (∑ t ∈ S, ((q.gcd t.natAbs).divisors.card : ℝ)) ≤
        C * T * max 1 (Real.log (Real.log (q : ℝ))) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_gcd_divisor_mean_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hq T hT S hzero hbound
  have hnat : ∀ t ∈ S, t.natAbs ≤ Nat.floor T := fun t ht => Nat.le_floor (hbound t ht)
  calc
    _ ≤ 2 * ∑ n ∈ Finset.Ioc 0 (Nat.floor T), ((q.gcd n).divisors.card : ℝ) :=
      delta_sum_natAbs_le_twice S _ _ (fun _ => by positivity) hzero hnat
    _ ≤ 2 * (C * (Nat.floor T : ℝ) * max 1 (Real.log (Real.log (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hmean q (Nat.floor T) hq) (by norm_num)
    _ ≤ 2 * (C * T * max 1 (Real.log (Real.log (q : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le hT) hC.le) (by positivity)
    _ = _ := by ring

end Erdos587

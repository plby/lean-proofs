import ErdosProblems.Erdos587.HooleySmoothNumbers
import ErdosProblems.Erdos587.HooleyVolterra
import ErdosProblems.Erdos587.HooleyMertens

/-!
# The restricted harmonic moment recurrence

Largest-prime decomposition and the exact local moment recurrence give
the finite Volterra inequality. The error term contains only the mixed
moments whose prime averages are controlled in `HooleyPrimeMean`.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def harmonicDeltaMoment (n q : ℕ) : ℝ :=
  (deltaMoment n q / n.divisors.card) / n

lemma harmonicDeltaMoment_nonneg (n q : ℕ) : 0 ≤ harmonicDeltaMoment n q :=
  div_nonneg (div_nonneg (deltaMoment_nonneg n q) (by positivity)) (by positivity)

@[simp] lemma harmonicDeltaMoment_one {q : ℕ} (hq : q ≠ 0) :
    harmonicDeltaMoment 1 q = 1 := by simp [harmonicDeltaMoment, deltaMoment_at_one hq]

noncomputable def deltaPrimeIncrement (n p q : ℕ) : ℝ :=
  (∑ b ∈ Finset.Icc 1 (q / 2),
    (q.choose b : ℝ) * deltaMixedMoment n (q - b) b (Real.log p)) /
      ((n.divisors.card : ℝ) * n * p)

lemma deltaPrimeIncrement_nonneg (n p q : ℕ) : 0 ≤ deltaPrimeIncrement n p q := by
  unfold deltaPrimeIncrement
  apply div_nonneg
  · exact Finset.sum_nonneg (fun b _ => mul_nonneg (by positivity)
      (deltaMixedMoment_nonneg n (q - b) b (Real.log p)))
  · positivity

lemma harmonicDeltaMoment_prime_mul_le {p n q : ℕ}
    (hp : p.Prime) (hn : n ∈ deltaSmoothNumbers p) (hq : q ≠ 0) :
    harmonicDeltaMoment (p * n) q ≤ harmonicDeltaMoment n q / p + deltaPrimeIncrement n p q := by
  have hpn := prime_not_dvd_of_mem_deltaSmoothNumbers hp hn
  have h := div_le_div_of_nonneg_right (normalized_deltaMoment_prime_mul_le hp hpn hq)
    (show (0 : ℝ) ≤ (p * n : ℕ) by positivity)
  calc
    harmonicDeltaMoment (p * n) q ≤
        (deltaMoment n q / n.divisors.card +
          (∑ b ∈ Finset.Icc 1 (q / 2),
            (q.choose b : ℝ) * deltaMixedMoment n (q - b) b (Real.log p)) / n.divisors.card) /
              (p * n : ℕ) := h
    _ = _ := by
      unfold harmonicDeltaMoment deltaPrimeIncrement
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring

noncomputable def restrictedHarmonicDeltaMoment (G : ℕ → Prop) [DecidablePred G]
    (q x : ℕ) : ℝ := ∑ n ∈ (deltaSmoothNumbers x).filter G, harmonicDeltaMoment n q

noncomputable def restrictedDeltaPrimeError (G : ℕ → Prop) [DecidablePred G]
    (q x : ℕ) : ℝ :=
  ∑ p ∈ x.primesBelow, ∑ n ∈ (deltaSmoothNumbers p).filter G, deltaPrimeIncrement n p q

lemma restrictedDeltaPrimeError_nonneg (G : ℕ → Prop) [DecidablePred G] (q x : ℕ) :
    0 ≤ restrictedDeltaPrimeError G q x :=
  Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun n _ => deltaPrimeIncrement_nonneg n p q))

/-- The largest-prime recurrence, valid for every downward-closed
restriction on squarefree integers. -/
theorem restrictedHarmonicDeltaMoment_recurrence (G : ℕ → Prop) [DecidablePred G]
    (hG1 : G 1) (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    {q : ℕ} (hq : q ≠ 0) (x : ℕ) :
    restrictedHarmonicDeltaMoment G q x ≤
      1 + (∑ p ∈ x.primesBelow, restrictedHarmonicDeltaMoment G q p / p) +
        restrictedDeltaPrimeError G q x := by
  have hdecomp := sum_deltaSmoothNumbers_filter_le_prime_decomposition x G hG1 hGdiv
    (fun n => harmonicDeltaMoment n q) (fun n => harmonicDeltaMoment_nonneg n q)
  rw [harmonicDeltaMoment_one hq] at hdecomp
  calc
    restrictedHarmonicDeltaMoment G q x ≤ 1 +
        ∑ p ∈ x.primesBelow, ∑ n ∈ (deltaSmoothNumbers p).filter G,
          harmonicDeltaMoment (p * n) q := hdecomp
    _ ≤ 1 + ∑ p ∈ x.primesBelow, ∑ n ∈ (deltaSmoothNumbers p).filter G,
        (harmonicDeltaMoment n q / p + deltaPrimeIncrement n p q) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro n hn
      exact harmonicDeltaMoment_prime_mul_le (Nat.mem_primesBelow.mp hp).2
        (Finset.mem_filter.mp hn).1 hq
    _ = _ := by
      have hinner (p : ℕ) :
          (∑ n ∈ (deltaSmoothNumbers p).filter G,
            (harmonicDeltaMoment n q / p + deltaPrimeIncrement n p q)) =
          restrictedHarmonicDeltaMoment G q p / p +
            ∑ n ∈ (deltaSmoothNumbers p).filter G, deltaPrimeIncrement n p q := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div]
        rfl
      simp_rw [hinner]
      rw [Finset.sum_add_distrib]
      unfold restrictedDeltaPrimeError
      ring

theorem restrictedHarmonicDeltaMoment_iterated (G : ℕ → Prop) [DecidablePred G]
    (hG1 : G 1) (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    {q : ℕ} (hq : q ≠ 0) (x : ℕ) :
    restrictedHarmonicDeltaMoment G q x ≤
      (1 + restrictedDeltaPrimeError G q x) +
        ∑ p ∈ x.primesBelow, ((1 + restrictedDeltaPrimeError G q p) / p) *
          ∏ r ∈ (Finset.Ioo p x).filter Nat.Prime, (1 + (1 : ℝ) / r) := by
  classical
  let T := restrictedHarmonicDeltaMoment G q
  let Q := fun n => 1 + restrictedDeltaPrimeError G q n
  let a := fun p : ℕ => if p.Prime then (1 : ℝ) / p else 0
  have hprimes (n : ℕ) : n.primesBelow = (Finset.range n).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_range]
  have hsum (n : ℕ) : (∑ p ∈ n.primesBelow, T p / p) =
      ∑ p ∈ Finset.range n, a p * T p := by
    rw [hprimes, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime <;> simp [a, hpp, div_eq_mul_inv, mul_comm]
  have hrec (n : ℕ) : T n ≤ Q n + ∑ p ∈ Finset.range n, a p * T p := by
    rw [← hsum]
    have h := restrictedHarmonicDeltaMoment_recurrence G hG1 hGdiv hq n
    dsimp only [T, Q]
    linarith
  have hprod (p : ℕ) : (∏ r ∈ Finset.Ico (p + 1) x, (1 + a r)) =
      ∏ r ∈ (Finset.Ioo p x).filter Nat.Prime, (1 + (1 : ℝ) / r) := by
    rw [Finset.Ico_add_one_left_eq_Ioo, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro r hr
    by_cases hp : r.Prime <;> simp [a, hp]
  have ha (p : ℕ) : 0 ≤ a p := by
    dsimp only [a]
    split_ifs <;> positivity
  have hbound := hooley_volterra_bound T Q a ha hrec x
  apply hbound.trans_eq
  change Q x + _ = Q x + _
  congr 1
  rw [hprimes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hprod]
  by_cases hpp : p.Prime <;> simp [a, Q, hpp, div_eq_mul_inv, mul_comm]

/-- Mertens bounds the tail Euler products with one absolute constant,
uniformly over the moment order and the downward-closed restriction. -/
theorem restrictedHarmonicDeltaMoment_mertens_bound (G : ℕ → Prop) [DecidablePred G]
    (hG1 : G 1) (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    {q : ℕ} (hq : q ≠ 0) (x : ℕ) :
    restrictedHarmonicDeltaMoment G q x ≤
      (1 + restrictedDeltaPrimeError G q x) + deltaTailEulerConstant * Real.log (x : ℝ) *
        ∑ p ∈ x.primesBelow, (1 + restrictedDeltaPrimeError G q p) /
          ((p : ℝ) * Real.log (p : ℝ)) := by
  apply (restrictedHarmonicDeltaMoment_iterated G hG1 hGdiv hq x).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ p ∈ x.primesBelow, ((1 + restrictedDeltaPrimeError G q p) / p) *
        (deltaTailEulerConstant * (Real.log (x : ℝ) / Real.log (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (delta_prime_tail_euler_bound (Nat.mem_primesBelow.mp hp).2 (Nat.mem_primesBelow.mp hp).1)
        (div_nonneg (add_nonneg zero_le_one (restrictedDeltaPrimeError_nonneg G q p))
          (by positivity))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end Erdos587

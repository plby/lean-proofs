import ErdosProblems.Erdos394.GeneralRootSieve
import ErdosProblems.Erdos394.GlobalMediumSieve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Medium-prime decomposition for a general block length
-/

open Nat Finset

namespace Erdos394

/-- The general-`K` fixed-modulus indicator mass is the sum over admissible
medium-prime quotient starts. -/
theorem tKMulCoprimeSiftedMass_eq_sum_admissible
    (K : ℕ) (P : Finset ℕ) (X : ℕ) (T : Finset ℕ) :
    tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T) (primeProduct T) =
      ∑ m ∈ admissibleMediumStarts P X T,
        (t K (m * primeProduct T) : ℝ) := by
  unfold tKMulCoprimeSiftedMass admissibleMediumStarts
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmpos : 0 < m
  · rw [dif_pos hmpos]
    by_cases hcop : m.Coprime (primeProduct T)
    · rw [dif_pos hcop]
      by_cases hsift : badPrimeSet (P \ T) m = ∅
      · simp [hmpos, hcop, hsift]
      · simp [hmpos, hcop, hsift]
    · simp [hcop]
  · simp [hmpos]

/-- Each good fiber is bounded by its general-`K` fixed-subset sifted mass. -/
theorem sum_tK_goodMediumFiber_le_tKMul
    (K : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    (∑ n ∈ goodMediumFiber P X Q T, (t K n : ℝ)) ≤
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
        (primeProduct T) := by
  classical
  rw [tKMulCoprimeSiftedMass_eq_sum_admissible]
  let f : ℕ → ℕ := fun n ↦ n / primeProduct T
  have hinj : Set.InjOn f (↑(goodMediumFiber P X Q T)) :=
    div_primeProduct_injective_goodFiber P hprime
  have hsub : (goodMediumFiber P X Q T).image f ⊆
      admissibleMediumStarts P X T :=
    div_primePart_image_goodFiber_subset P hprime
  calc
    (∑ n ∈ goodMediumFiber P X Q T, (t K n : ℝ)) =
        ∑ m ∈ (goodMediumFiber P X Q T).image f,
          (t K (m * primeProduct T) : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hT : badPrimeSet P n = T := hn'.2
      have hrec := div_primePart_mul_primePart P hprime n
      rw [primePart_eq_primeProduct, hT] at hrec
      rw [hrec]
    _ ≤ ∑ m ∈ admissibleMediumStarts P X T,
          (t K (m * primeProduct T) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      positivity

/-- The good set is exactly partitioned by its selected-prime subset for an
arbitrary block length. -/
theorem sum_tK_goodMediumNumbers_eq_sum_fibers
    (K : ℕ) (P : Finset ℕ) (X Q : ℕ) :
    (∑ n ∈ goodMediumNumbers P X Q, (t K n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t K n : ℝ) := by
  classical
  symm
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t K n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumNumbers P X Q,
          if badPrimeSet P n = T then (t K n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      unfold goodMediumFiber
      rw [Finset.sum_filter]
    _ = ∑ n ∈ goodMediumNumbers P X Q,
        ∑ T ∈ smallPrimeSubsets P Q,
          if badPrimeSet P n = T then (t K n : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ goodMediumNumbers P X Q, (t K n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ∈ Finset.range (X + 1) ∧
          (n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q) := by
        simpa [goodMediumNumbers] using hn
      have hbadSmall : badPrimeSet P n ∈ smallPrimeSubsets P Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (badPrimeSet_subset P n), ?_⟩
        simpa [primePart_eq_primeProduct] using hn'.2.2.2
      rw [Finset.sum_eq_single (badPrimeSet P n)]
      · simp
      · intro T hT hTne
        rw [if_neg]
        exact fun h ↦ hTne h.symm
      · exact fun hnot ↦ (hnot hbadSmall).elim

/-- The total good contribution is bounded by the sum of general-`K`
fixed-subset masses. -/
theorem sum_tK_goodMediumNumbers_le_sum_tKMul
    (K : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {X Q : ℕ} :
    (∑ n ∈ goodMediumNumbers P X Q, (t K n : ℝ)) ≤
      ∑ T ∈ smallPrimeSubsets P Q,
        tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  rw [sum_tK_goodMediumNumbers_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro T hT
  exact sum_tK_goodMediumFiber_le_tKMul K P hprime

/-- The trivial bound `t_K(n)≤n` controls squared-prime exceptions for every
positive block length. -/
theorem sum_tK_squaredPrimeException_le
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ) {X z y : ℕ}
    (hz : z ≠ 0) (hzy : z ≤ y)
    (hP : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) := by
  have hpoint : ∀ n ∈ squaredPrimeException P X, (t K n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self hK hnpos).trans hnX
  have hcard := card_squaredPrimeException_le P (X := X) hz hzy hP
  calc
    (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) ≤
        ∑ _n ∈ squaredPrimeException P X, (X : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) * (squaredPrimeException P X).card := by simp [mul_comm]
    _ ≤ (X : ℝ) * ((X : ℝ) / (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 / (z : ℝ) := by ring

/-- The trivial bound also controls the large-selected-prime-part tail for
every positive block length. -/
theorem sum_tK_largePrimePart_le_factorial_tail
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    {R X y : ℕ} (hy : 0 < y) (hPy : ∀ p ∈ P, p ≤ y) :
    (∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by
  have hpoint : ∀ n ∈ largePrimePart P R X y,
      (t K n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self hK hnpos).trans hnX
  have hsum : (∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) ≤
      (X : ℝ) * (largePrimePart P R X y).card := by
    calc
      (∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) ≤
          ∑ _n ∈ largePrimePart P R X y, (X : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (X : ℝ) * (largePrimePart P R X y).card := by
        simp [mul_comm]
  have hcard := card_largePrimePart_le_factorial_tail P hprime
    (R := R) (X := X) (y := y) hy hPy
  calc
    (∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) ≤
        (X : ℝ) * (largePrimePart P R X y).card := hsum
    _ ≤ (X : ℝ) * ((X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by ring

/-- The total general-`K` sum is bounded by the squared, large-prime-part, and
good pieces. -/
theorem sum_tK_le_three_pieces
    (K : ℕ) (P : Finset ℕ) (R X y : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) ≤
      (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
      (∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) +
      (∑ n ∈ goodMediumNumbers P X (y ^ R), (t K n : ℝ)) := by
  classical
  rw [← positiveNumbersUpTo_eq_Icc]
  have hcover := positiveNumbersUpTo_subset_exceptions_union_good P R X y
  calc
    (∑ n ∈ positiveNumbersUpTo X, (t K n : ℝ)) ≤
        ∑ n ∈ squaredPrimeException P X ∪
          (largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R)),
            (t K n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcover
      intro n hn hnot
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
        ∑ n ∈ largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R),
          (t K n : ℝ) := by
      apply sum_union_le_add
      intro n hn
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
        ((∑ n ∈ largePrimePart P R X y, (t K n : ℝ)) +
          ∑ n ∈ goodMediumNumbers P X (y ^ R), (t K n : ℝ)) := by
      apply _root_.add_le_add_right
      apply sum_union_le_add
      intro n hn
      positivity
    _ = _ := by ring

/-- Finite reduction of the full general-`K` sum to fixed selected-prime
masses, before estimating those masses. -/
theorem finite_general_medium_decomposition
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    {X R y z : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) +
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) +
      ∑ T ∈ smallPrimeSubsets P (y ^ R),
        tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  have hpieces := sum_tK_le_three_pieces K P R X y
  have hsquare := sum_tK_squaredPrimeException_le K hK P
    (X := X) hz hzy hPinterval
  have hlarge := sum_tK_largePrimePart_le_factorial_tail K hK P hprime
    (R := R) (X := X) (y := y) (by omega)
      (fun p hp ↦ (hPinterval p hp).2)
  have hgood := sum_tK_goodMediumNumbers_le_sum_tKMul K P hprime
    (X := X) (Q := y ^ R)
  linarith

end Erdos394

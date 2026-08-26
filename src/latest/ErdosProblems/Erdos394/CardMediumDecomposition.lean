import ErdosProblems.Erdos394.GeneralMediumDecomposition

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cardinality-truncated medium-prime decomposition

The root-box hypotheses depend on the number of selected primes, so this
version truncates that cardinality directly instead of only truncating their
product.
-/

open Nat Finset

namespace Erdos394

/-- Prime subsets of cardinality at most `S`. -/
def boundedPrimeSubsets (P : Finset ℕ) (S : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun T ↦ T.card ≤ S)

/-- Good integers have no squared selected prime and at most `S` distinct
selected prime divisors. -/
noncomputable def cardGoodMediumNumbers
    (P : Finset ℕ) (X S : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n ↦
    n ≠ 0 ∧ noSquaredPrime P n ∧ (badPrimeSet P n).card ≤ S)

/-- Fiber of cardinality-truncated good integers with selected-prime set `T`. -/
noncomputable def cardGoodMediumFiber
    (P : Finset ℕ) (X S : ℕ) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact (cardGoodMediumNumbers P X S).filter (fun n ↦ badPrimeSet P n = T)

/-- Quotients from a fixed cardinality-truncated fiber are admissible starts. -/
theorem div_primeProduct_image_cardGoodFiber_subset
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X S : ℕ} {T : Finset ℕ} :
    (cardGoodMediumFiber P X S T).image (fun n ↦ n / primeProduct T) ⊆
      admissibleMediumStarts P X T := by
  classical
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hnf := Finset.mem_filter.mp hn
  have hng : n ∈ Finset.range (X + 1) ∧
      (n ≠ 0 ∧ noSquaredPrime P n ∧ (badPrimeSet P n).card ≤ S) := by
    simpa [cardGoodMediumNumbers] using hnf.1
  have hnpos : 0 < n := Nat.pos_of_ne_zero hng.2.1
  have hT : badPrimeSet P n = T := hnf.2
  have hdecomp := mediumPrime_decomposition P hprime hnpos hng.2.2.1
  dsimp at hdecomp
  have hqeq : primePart P n = primeProduct T := by
    rw [primePart_eq_primeProduct, hT]
  unfold admissibleMediumStarts
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · apply Nat.lt_succ_iff.mpr
    apply Nat.div_le_div_right
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hng.1)
  rw [← hqeq]
  exact ⟨hdecomp.2.2.1, hdecomp.2.2.2.2.1,
    by simpa [hT] using hdecomp.2.2.2.2.2⟩

/-- Quotienting is injective on a fixed cardinality-truncated fiber. -/
theorem div_primeProduct_injective_cardGoodFiber
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X S : ℕ} {T : Finset ℕ} :
    Set.InjOn (fun n ↦ n / primeProduct T)
      (↑(cardGoodMediumFiber P X S T)) := by
  classical
  intro n hn r hr heq
  have hn' := Finset.mem_filter.mp hn
  have hr' := Finset.mem_filter.mp hr
  have hTn : badPrimeSet P n = T := hn'.2
  have hTr : badPrimeSet P r = T := hr'.2
  have hqn : primePart P n = primeProduct T := by
    rw [primePart_eq_primeProduct, hTn]
  have hqr : primePart P r = primeProduct T := by
    rw [primePart_eq_primeProduct, hTr]
  have hnrec := div_primePart_mul_primePart P hprime n
  have hrrec := div_primePart_mul_primePart P hprime r
  rw [hqn] at hnrec
  rw [hqr] at hrrec
  change n / primeProduct T = r / primeProduct T at heq
  calc
    n = (n / primeProduct T) * primeProduct T := hnrec.symm
    _ = (r / primeProduct T) * primeProduct T := by rw [heq]
    _ = r := hrrec

/-- A fixed good fiber is bounded by the corresponding general-`K` mass. -/
theorem sum_tK_cardGoodMediumFiber_le_tKMul
    (K : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X S : ℕ} {T : Finset ℕ} :
    (∑ n ∈ cardGoodMediumFiber P X S T, (t K n : ℝ)) ≤
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
        (primeProduct T) := by
  classical
  rw [tKMulCoprimeSiftedMass_eq_sum_admissible]
  let f : ℕ → ℕ := fun n ↦ n / primeProduct T
  have hinj : Set.InjOn f (↑(cardGoodMediumFiber P X S T)) :=
    div_primeProduct_injective_cardGoodFiber P hprime
  have hsub : (cardGoodMediumFiber P X S T).image f ⊆
      admissibleMediumStarts P X T :=
    div_primeProduct_image_cardGoodFiber_subset P hprime
  calc
    (∑ n ∈ cardGoodMediumFiber P X S T, (t K n : ℝ)) =
        ∑ m ∈ (cardGoodMediumFiber P X S T).image f,
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

/-- Exact partition of the cardinality-truncated good set. -/
theorem sum_tK_cardGoodMediumNumbers_eq_sum_fibers
    (K : ℕ) (P : Finset ℕ) (X S : ℕ) :
    (∑ n ∈ cardGoodMediumNumbers P X S, (t K n : ℝ)) =
      ∑ T ∈ boundedPrimeSubsets P S,
        ∑ n ∈ cardGoodMediumFiber P X S T, (t K n : ℝ) := by
  classical
  symm
  calc
    (∑ T ∈ boundedPrimeSubsets P S,
        ∑ n ∈ cardGoodMediumFiber P X S T, (t K n : ℝ)) =
      ∑ T ∈ boundedPrimeSubsets P S,
        ∑ n ∈ cardGoodMediumNumbers P X S,
          if badPrimeSet P n = T then (t K n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      unfold cardGoodMediumFiber
      rw [Finset.sum_filter]
    _ = ∑ n ∈ cardGoodMediumNumbers P X S,
        ∑ T ∈ boundedPrimeSubsets P S,
          if badPrimeSet P n = T then (t K n : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ cardGoodMediumNumbers P X S, (t K n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ∈ Finset.range (X + 1) ∧
          (n ≠ 0 ∧ noSquaredPrime P n ∧ (badPrimeSet P n).card ≤ S) := by
        simpa [cardGoodMediumNumbers] using hn
      have hbadBounded : badPrimeSet P n ∈ boundedPrimeSubsets P S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (badPrimeSet_subset P n), hn'.2.2.2⟩
      rw [Finset.sum_eq_single (badPrimeSet P n)]
      · simp
      · intro T hT hTne
        rw [if_neg]
        exact fun h ↦ hTne h.symm
      · exact fun hnot ↦ (hnot hbadBounded).elim

/-- Total cardinality-truncated good contribution is bounded by fixed-subset
masses. -/
theorem sum_tK_cardGoodMediumNumbers_le_sum_tKMul
    (K : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {X S : ℕ} :
    (∑ n ∈ cardGoodMediumNumbers P X S, (t K n : ℝ)) ≤
      ∑ T ∈ boundedPrimeSubsets P S,
        tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  rw [sum_tK_cardGoodMediumNumbers_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro T hT
  exact sum_tK_cardGoodMediumFiber_le_tKMul K P hprime

/-- The `t_K` mass of integers with at least `r` selected prime divisors is
bounded by the same factorial tail as their census. -/
theorem sum_tK_manyPrimeDivisors_le_factorial_tail
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    (∑ n ∈ manyPrimeDivisors P r X, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ r /
          (r.factorial : ℝ)) := by
  have hpoint : ∀ n ∈ manyPrimeDivisors P r X,
      (t K n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self hK hnpos).trans hnX
  have hcard := card_manyPrimeDivisors_le_factorial_tail P hprime r X
  calc
    (∑ n ∈ manyPrimeDivisors P r X, (t K n : ℝ)) ≤
        ∑ _n ∈ manyPrimeDivisors P r X, (X : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) * (manyPrimeDivisors P r X).card := by simp [mul_comm]
    _ ≤ (X : ℝ) * ((X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ r /
          (r.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ r /
          (r.factorial : ℝ)) := by ring

/-- Every positive integer is squared-exceptional, has at least `S+1`
selected prime divisors, or belongs to the cardinality-truncated good set. -/
theorem positiveNumbersUpTo_subset_square_union_many_union_cardGood
    (P : Finset ℕ) (S X : ℕ) :
    positiveNumbersUpTo X ⊆
      squaredPrimeException P X ∪
        (manyPrimeDivisors P (S + 1) X ∪ cardGoodMediumNumbers P X S) := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  by_cases hsq : ∃ p ∈ P, p * p ∣ n
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hsq⟩
  · apply Finset.mem_union_right
    by_cases hmany : S < (badPrimeSet P n).card
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, by omega⟩
    · apply Finset.mem_union_right
      have hno : noSquaredPrime P n := by
        intro p hp hdiv
        exact hsq ⟨p, hp, hdiv⟩
      exact Finset.mem_filter.mpr
        ⟨hn'.1, hn'.2, hno, Nat.le_of_not_gt hmany⟩

/-- Cardinality-truncated three-piece bound. -/
theorem sum_tK_le_card_three_pieces
    (K : ℕ) (P : Finset ℕ) (S X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) ≤
      (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
      (∑ n ∈ manyPrimeDivisors P (S + 1) X, (t K n : ℝ)) +
      (∑ n ∈ cardGoodMediumNumbers P X S, (t K n : ℝ)) := by
  classical
  rw [← positiveNumbersUpTo_eq_Icc]
  have hcover := positiveNumbersUpTo_subset_square_union_many_union_cardGood P S X
  calc
    (∑ n ∈ positiveNumbersUpTo X, (t K n : ℝ)) ≤
        ∑ n ∈ squaredPrimeException P X ∪
          (manyPrimeDivisors P (S + 1) X ∪ cardGoodMediumNumbers P X S),
            (t K n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcover
      intro n hn hnot
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
        ∑ n ∈ manyPrimeDivisors P (S + 1) X ∪
          cardGoodMediumNumbers P X S, (t K n : ℝ) := by
      apply sum_union_le_add
      intro n hn
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t K n : ℝ)) +
        ((∑ n ∈ manyPrimeDivisors P (S + 1) X, (t K n : ℝ)) +
          ∑ n ∈ cardGoodMediumNumbers P X S, (t K n : ℝ)) := by
      apply _root_.add_le_add_right
      apply sum_union_le_add
      intro n hn
      positivity
    _ = _ := by ring

/-- Finite reduction with a direct selected-prime-cardinality cutoff. -/
theorem finite_general_card_medium_decomposition
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    {X S y z : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y) :
    (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) +
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (S + 1) /
          ((S + 1).factorial : ℝ)) +
      ∑ T ∈ boundedPrimeSubsets P S,
        tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  have hpieces := sum_tK_le_card_three_pieces K P S X
  have hsquare := sum_tK_squaredPrimeException_le K hK P
    (X := X) hz hzy hPinterval
  have hmany := sum_tK_manyPrimeDivisors_le_factorial_tail
    K hK P hprime (S + 1) X
  have hgood := sum_tK_cardGoodMediumNumbers_le_sum_tKMul K P hprime
    (X := X) (S := S)
  linarith

end Erdos394

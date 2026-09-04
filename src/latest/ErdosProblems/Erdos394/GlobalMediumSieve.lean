import ErdosProblems.Erdos394.RootSieve
import ErdosProblems.Erdos394.MediumDecomposition
import ErdosProblems.Erdos394.PrimeSubset
import ErdosProblems.Erdos394.SquaredPrime

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Summing the fixed-modulus Brun bound over medium-prime subsets
-/

open Nat Finset

namespace Erdos394

/-- A prime outside `T` is coprime to the product of the primes in `T`. -/
theorem primeProduct_coprime_of_not_mem
    {P T : Finset ℕ} (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hpP : p ∈ P) (hpT : p ∉ T) :
    (primeProduct T).Coprime p := by
  have hp : p.Prime := hprime p hpP
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  have hqne : primeProduct T ≠ 0 := by
    unfold primeProduct
    exact Finset.prod_ne_zero_iff.mpr
      (fun r hr ↦ (hprime r (hTP hr)).ne_zero)
  have hpFac : p ∈ (primeProduct T).primeFactors :=
    hp.mem_primeFactors hdiv hqne
  rw [primeFactors_primeProduct T (fun r hr ↦ hprime r (hTP hr))] at hpFac
  exact hpT hpFac

/-- Starts represented by a fixed medium-prime subset. -/
def admissibleMediumStarts (P : Finset ℕ) (X : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (X / primeProduct T + 1)).filter (fun m ↦
    0 < m ∧ m.Coprime (primeProduct T) ∧ badPrimeSet (P \ T) m = ∅)

/-- The indicator definition of the fixed-modulus mass is exactly the sum over
admissible starts. -/
theorem tMulCoprimeSiftedMass_eq_sum_admissible
    (P : Finset ℕ) (X : ℕ) (T : Finset ℕ) :
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) =
      ∑ m ∈ admissibleMediumStarts P X T,
        (t 2 (m * primeProduct T) : ℝ) := by
  unfold tMulCoprimeSiftedMass admissibleMediumStarts
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

/-- Good integers for the medium-prime decomposition: no selected prime is
squared, and the selected prime product is at most `Q`. -/
noncomputable def goodMediumNumbers (P : Finset ℕ) (X Q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n ↦
    n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q)

/-- Fiber of good integers having exactly selected-prime set `T`. -/
noncomputable def goodMediumFiber (P : Finset ℕ) (X Q : ℕ) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact (goodMediumNumbers P X Q).filter (fun n ↦ badPrimeSet P n = T)

/-- A good fiber maps injectively into the admissible quotient starts. -/
theorem div_primePart_image_goodFiber_subset
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    (goodMediumFiber P X Q T).image (fun n ↦ n / primeProduct T) ⊆
      admissibleMediumStarts P X T := by
  classical
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hnf := Finset.mem_filter.mp hn
  have hng : n ∈ Finset.range (X + 1) ∧
      (n ≠ 0 ∧ noSquaredPrime P n ∧ primePart P n ≤ Q) := by
    simpa [goodMediumNumbers] using hnf.1
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
  exact ⟨hdecomp.2.2.1, hdecomp.2.2.2.2.1, by simpa [hT] using hdecomp.2.2.2.2.2⟩

/-- Quotienting by the selected prime product is injective on a fixed good
fiber. -/
theorem div_primeProduct_injective_goodFiber
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    Set.InjOn (fun n ↦ n / primeProduct T) (↑(goodMediumFiber P X Q T)) := by
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

/-- Each good fiber is bounded by its fixed-subset sifted mass. -/
theorem sum_t_goodMediumFiber_le_tMul
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X Q : ℕ} {T : Finset ℕ} :
    (∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) ≤
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T) := by
  classical
  rw [tMulCoprimeSiftedMass_eq_sum_admissible]
  let f : ℕ → ℕ := fun n ↦ n / primeProduct T
  have hinj : Set.InjOn f (↑(goodMediumFiber P X Q T)) :=
    div_primeProduct_injective_goodFiber P hprime
  have hsub : (goodMediumFiber P X Q T).image f ⊆
      admissibleMediumStarts P X T :=
    div_primePart_image_goodFiber_subset P hprime
  calc
    (∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) =
        ∑ m ∈ (goodMediumFiber P X Q T).image f,
          (t 2 (m * primeProduct T) : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hT : badPrimeSet P n = T := hn'.2
      have hrec := div_primePart_mul_primePart P hprime n
      rw [primePart_eq_primeProduct, hT] at hrec
      rw [hrec]
    _ ≤ ∑ m ∈ admissibleMediumStarts P X T,
          (t 2 (m * primeProduct T) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      positivity

/-- The good set is exactly partitioned by its selected-prime subset. -/
theorem sum_t_goodMediumNumbers_eq_sum_fibers
    (P : Finset ℕ) (X Q : ℕ) :
    (∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ) := by
  classical
  symm
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumFiber P X Q T, (t 2 n : ℝ)) =
      ∑ T ∈ smallPrimeSubsets P Q,
        ∑ n ∈ goodMediumNumbers P X Q,
          if badPrimeSet P n = T then (t 2 n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      unfold goodMediumFiber
      rw [Finset.sum_filter]
    _ = ∑ n ∈ goodMediumNumbers P X Q,
        ∑ T ∈ smallPrimeSubsets P Q,
          if badPrimeSet P n = T then (t 2 n : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ) := by
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

/-- The total good contribution is bounded by the sum of the fixed-subset
masses. -/
theorem sum_t_goodMediumNumbers_le_sum_tMul
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {X Q : ℕ} :
    (∑ n ∈ goodMediumNumbers P X Q, (t 2 n : ℝ)) ≤
      ∑ T ∈ smallPrimeSubsets P Q,
        tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
          (primeProduct T) := by
  rw [sum_t_goodMediumNumbers_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro T hT
  exact sum_t_goodMediumFiber_le_tMul P hprime

/-- Positive naturals not exceeding `X`. -/
def positiveNumbersUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n ↦ n ≠ 0)

/-- Positive naturals up to `X` agree with the closed interval `[1,X]`. -/
theorem positiveNumbersUpTo_eq_Icc (X : ℕ) :
    positiveNumbersUpTo X = Finset.Icc 1 X := by
  ext n
  simp [positiveNumbersUpTo]
  omega

/-- For nonnegative weights, the sum on a union is at most the sum of the two
separate sums. -/
theorem sum_union_le_add [DecidableEq α] {s u : Finset α} {f : α → ℝ}
    (hf : ∀ a ∈ u, 0 ≤ f a) :
    (∑ a ∈ s ∪ u, f a) ≤ (∑ a ∈ s, f a) + ∑ a ∈ u, f a := by
  have hd : Disjoint s (u \ s) := Finset.disjoint_sdiff
  have heq : s ∪ (u \ s) = s ∪ u := by
    ext a
    simp
  rw [← heq, Finset.sum_union hd]
  apply _root_.add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
  intro a ha hnot
  exact hf a ha

/-- Every positive `n≤X` is either a squared-prime exception, has large
selected prime part, or is good. -/
theorem positiveNumbersUpTo_subset_exceptions_union_good
    (P : Finset ℕ) (R X y : ℕ) :
    positiveNumbersUpTo X ⊆
      squaredPrimeException P X ∪
        (largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R)) := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  by_cases hsq : ∃ p ∈ P, p * p ∣ n
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hsq⟩
  · apply Finset.mem_union_right
    by_cases hlarge : y ^ R < primePart P n
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2, hlarge⟩
    · apply Finset.mem_union_right
      have hno : noSquaredPrime P n := by
        intro p hp hdiv
        exact hsq ⟨p, hp, hdiv⟩
      exact Finset.mem_filter.mpr
        ⟨hn'.1, hn'.2, hno, Nat.le_of_not_gt hlarge⟩

/-- The total `t₂` sum is bounded by the squared, large-prime-part, and good
pieces. -/
theorem sum_t_two_le_three_pieces
    (P : Finset ℕ) (R X y : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
      (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
      (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) +
      (∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) := by
  classical
  rw [← positiveNumbersUpTo_eq_Icc]
  have hcover := positiveNumbersUpTo_subset_exceptions_union_good P R X y
  calc
    (∑ n ∈ positiveNumbersUpTo X, (t 2 n : ℝ)) ≤
        ∑ n ∈ squaredPrimeException P X ∪
          (largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R)),
            (t 2 n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcover
      intro n hn hnot
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
        ∑ n ∈ largePrimePart P R X y ∪ goodMediumNumbers P X (y ^ R),
          (t 2 n : ℝ) := by
      apply sum_union_le_add
      intro n hn
      positivity
    _ ≤ (∑ n ∈ squaredPrimeException P X, (t 2 n : ℝ)) +
        ((∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) +
          ∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) := by
      apply _root_.add_le_add_right
      apply sum_union_le_add
      intro n hn
      positivity
    _ = _ := by ring

/-- The fixed-subset contribution has the desired Euler main term and a
uniformly bounded Brun error. -/
theorem tMul_primeSubset_le_main_add_error
    (P T : Finset ℕ) (hTP : T ⊆ P)
    (hprime : ∀ p ∈ P, p.Prime) (hne2 : ∀ p ∈ P, p ≠ 2)
    {X R y : ℕ} (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) := by
  let q := primeProduct T
  let M := X / q
  let Vc := localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))
  let Vt := localEulerProduct T (fun p ↦ 1 / (p : ℝ))
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let d : ℝ := ((2 ^ T.card : ℕ) : ℝ)
  let N : ℝ := ((truncatedSubsets (P \ T) R).card : ℝ)
  let Nmax : ℝ := (((R + 1) * y ^ R : ℕ) : ℝ)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ hprime p (hTP hp)
  have hcompPrime : ∀ p ∈ P \ T, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_sdiff.mp hp).1
  have hsq : Squarefree q := squarefree_primeProduct T hTprime
  have hodd : Odd q := odd_primeProduct T hTprime
    (fun p hp ↦ hne2 p (hTP hp))
  let : NeZero q := ⟨hodd.pos.ne'⟩
  have hcopComp : ∀ p ∈ P \ T, q.Coprime p := by
    intro p hp
    exact primeProduct_coprime_of_not_mem hTP hprime
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
  have htailComp := factorial_tail_le_localEulerProduct_sdiff
    P T hTP R htail hprime
  have hsieve := tMulCoprimeSiftedMass_le_brun
    (P \ T) hcompPrime (M := M) (q := q) (R := R)
    hsq hodd hcopComp hR htailComp
  have hfac : q.primeFactors.card = T.card := by
    rw [primeFactors_primeProduct T hTprime]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hodd.pos
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hM : (M : ℝ) ≤ (X : ℝ) / (q : ℝ) := by
    dsimp [M]
    exact Nat.cast_div_le
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ ((X : ℝ) / (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hM0 hM 2
  have hV0 : 0 ≤ V := by
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp
      positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hVsplit : Vt * Vc = V := by
    exact localEulerProduct_mul_sdiff P T hTP _
  have htot : ((q.totient : ℕ) : ℝ) = (q : ℝ) * Vt := by
    dsimp [q, Vt]
    exact totient_primeProduct_real T hTprime
  have hhalf : (∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      1 / ((q : ℝ) * d) := by
    dsimp [q, d]
    exact prod_half_prime_eq T hTprime
  have hNnat : (truncatedSubsets (P \ T) R).card ≤ (R + 1) * y ^ R := by
    apply card_truncatedSubsets_le (P \ T) R y hy
    exact (Finset.card_le_card Finset.sdiff_subset).trans hPy
  have hN : N ≤ Nmax := by
    dsimp [N, Nmax]
    exact_mod_cast hNnat
  have hMqNat : M * q ≤ X := by
    dsimp [M]
    exact Nat.div_mul_le_self X q
  have hMq : (M : ℝ) * (q : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hMqNat
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  have hmain :
      (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) *
          (((q : ℝ) * (q.totient : ℝ)) / d) ≤
        (X : ℝ) ^ 2 * V * (∏ p ∈ T, (1 / (2 * (p : ℝ)))) := by
    have hscale : 0 ≤ (q : ℝ) * V / d := by positivity
    calc
      (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) *
          (((q : ℝ) * (q.totient : ℝ)) / d) =
          (M : ℝ) ^ 2 * ((q : ℝ) * V / d) := by
        rw [htot]
        field_simp
        nlinarith [hVsplit]
      _ ≤ ((X : ℝ) / (q : ℝ)) ^ 2 * ((q : ℝ) * V / d) :=
        mul_le_mul_of_nonneg_right hM2 hscale
      _ = (X : ℝ) ^ 2 * V * (∏ p ∈ T, (1 / (2 * (p : ℝ)))) := by
        rw [hhalf]
        field_simp
  have herr :
      (N * (2 * (M : ℝ))) *
          (((q : ℝ) * (q.totient : ℝ)) / d) ≤
        2 * (X : ℝ) * Nmax * ((q.totient : ℝ) / d) := by
    have hNM : N * ((M : ℝ) * (q : ℝ)) ≤ Nmax * (X : ℝ) :=
      mul_le_mul hN hMq (by positivity) (by positivity)
    have hscale : 0 ≤ 2 * ((q.totient : ℝ) / d) := by positivity
    calc
      (N * (2 * (M : ℝ))) *
          (((q : ℝ) * (q.totient : ℝ)) / d) =
        (N * ((M : ℝ) * (q : ℝ))) *
          (2 * ((q.totient : ℝ) / d)) := by ring
      _ ≤ (Nmax * (X : ℝ)) * (2 * ((q.totient : ℝ) / d)) :=
        mul_le_mul_of_nonneg_right hNM hscale
      _ = 2 * (X : ℝ) * Nmax * ((q.totient : ℝ) / d) := by ring
  dsimp [q, M, Vc, Vt, V, d, N, Nmax] at hsieve ⊢
  rw [hfac] at hsieve
  calc
    tMulCoprimeSiftedMass (P \ T) (X / primeProduct T) (primeProduct T) ≤
      ((((X / primeProduct T : ℕ) : ℝ) ^ 2 / (primeProduct T : ℝ)) *
          localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) +
        ((truncatedSubsets (P \ T) R).card : ℝ) *
          (2 * ((X / primeProduct T : ℕ) : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) := hsieve
    _ = ((((X / primeProduct T : ℕ) : ℝ) ^ 2 / (primeProduct T : ℝ)) *
          localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) +
      (((truncatedSubsets (P \ T) R).card : ℝ) *
          (2 * ((X / primeProduct T : ℕ) : ℝ))) *
        (((primeProduct T : ℝ) * ((primeProduct T).totient : ℝ)) /
          ((2 ^ T.card : ℕ) : ℝ)) := by ring
    _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) :=
      add_le_add hmain herr

/-- Summing over all product-truncated prime subsets yields the combined Euler
main factor and a quadratic-in-`Q` Brun error. -/
theorem sum_smallPrimeSubsets_tMul_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hne2 : ∀ p ∈ P, p ≠ 2)
    {X R y Q : ℕ} (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        ((Q : ℝ) * (Q + 1 : ℕ)) := by
  have hterm : ∀ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
          (primeProduct T) ≤
        (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
            (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
          2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
            (((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ)) := by
    intro T hT
    have hTP : T ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact tMul_primeSubset_le_main_add_error P T hTP hprime hne2
      hy hPy hR htail
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
      tMulCoprimeSiftedMass (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      ∑ T ∈ smallPrimeSubsets P Q,
        ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
            (∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
          2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
            (((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ))) := Finset.sum_le_sum hterm
    _ = (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∑ T ∈ smallPrimeSubsets P Q,
            ∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (∑ T ∈ smallPrimeSubsets P Q,
            ((primeProduct T).totient : ℝ) /
              ((2 ^ T.card : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
      · rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∑ T ∈ P.powerset,
            ∏ p ∈ T, (1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          ((Q : ℝ) * (Q + 1 : ℕ)) := by
      apply _root_.add_le_add
      · apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro T hT hnot
            positivity
        · have hV0 : 0 ≤ localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
            apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
            · intro p hp
              positivity
            · intro p hp
              have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
              exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
          positivity
      · apply mul_le_mul_of_nonneg_left
          (sum_smallPrimeSubsets_totient_div_pow_le P hprime Q)
        positivity
    _ = (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        ((Q : ℝ) * (Q + 1 : ℕ)) := by
      rw [sum_powerset_half_prime_products]

/-- Fully finite medium-prime sieve bound, before choosing asymptotic
parameters. -/
theorem finite_medium_sieve_bound
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {X R y z : ℕ} (hz : z ≠ 0) (hzy : z ≤ y)
    (hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y)
    (hne2 : ∀ p ∈ P, p ≠ 2)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ n ∈ Finset.Icc 1 X, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) +
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) +
      ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ))) := by
  have hpieces := sum_t_two_le_three_pieces P R X y
  have hsquare := sum_t_two_squaredPrimeException_le
    P (X := X) hz hzy hPinterval
  have hlarge := sum_t_two_largePrimePart_le_factorial_tail
    P hprime (R := R) (X := X) (y := y) (by omega)
      (fun p hp ↦ (hPinterval p hp).2)
  have hgood :
      (∑ n ∈ goodMediumNumbers P X (y ^ R), (t 2 n : ℝ)) ≤
        (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (∏ p ∈ P, (1 + 1 / (2 * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ)) := by
    apply (sum_t_goodMediumNumbers_le_sum_tMul P hprime).trans
    exact sum_smallPrimeSubsets_tMul_le P hprime hne2 hy hPy hR htail
  linarith

end Erdos394

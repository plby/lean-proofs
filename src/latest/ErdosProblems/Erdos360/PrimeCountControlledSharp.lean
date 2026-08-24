/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeCountSharp

/-!
# A controlled-cap prime count for Erdős 360

The controlled extraction only needs a class cap `5n/(4y)`.  This permits
the direct-prime count to be compared with `V*y/12`, rather than the false
`V*y/8` comparison.  The key finite improvement is the elementary bound

`(1/2) * n/φ(n) ≤ ∑ d∣n 1/d`.

It follows by separating the prime `2` and indexing every odd prime as
`2j+1`: the odd reciprocal-square sum is at most the telescoping sum
`∑_{j≥1} 1/(4j(j+1)) = 1/4`.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

private lemma sum_Icc_one_div_four_mul_mul_succ (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K,
      (1 : ℝ) / (4 * (j : ℝ) * (j + 1))) =
        (K : ℝ) / (4 * (K + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
      push_cast
      field_simp
      ring

private lemma finset_sum_le_sum_of_inj
    {A B : Finset ℕ} {f g : ℕ → ℝ} (e : ℕ → ℕ)
    (hg : ∀ b ∈ B, 0 ≤ g b)
    (heB : ∀ a ∈ A, e a ∈ B)
    (heinj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, e a₁ = e a₂ → a₁ = a₂)
    (hfg : ∀ a ∈ A, f a ≤ g (e a)) :
    ∑ a ∈ A, f a ≤ ∑ b ∈ B, g b := by
  induction A using Finset.induction_on generalizing B with
  | empty =>
      simp only [Finset.sum_empty]
      exact Finset.sum_nonneg hg
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha]
      let B' := B.erase (e a)
      have hB : insert (e a) B' = B :=
        Finset.insert_erase (heB a (Finset.mem_insert_self a A))
      rw [← hB, Finset.sum_insert (Finset.notMem_erase _ _)]
      apply add_le_add (hfg a (Finset.mem_insert_self a A))
      apply ih
      · intro b hb
        exact hg b (Finset.mem_of_mem_erase hb)
      · intro x hx
        rw [Finset.mem_erase]
        refine ⟨?_, heB x (Finset.mem_insert_of_mem hx)⟩
        intro heq
        have : x = a := heinj x (Finset.mem_insert_of_mem hx)
          a (Finset.mem_insert_self a A) heq
        subst x
        exact ha hx
      · intro x hx z hz hxz
        exact heinj x (Finset.mem_insert_of_mem hx)
          z (Finset.mem_insert_of_mem hz) hxz
      · intro x hx
        exact hfg x (Finset.mem_insert_of_mem hx)

private lemma sum_prime_inv_sq_le_half
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, (((p : ℝ) ^ 2)⁻¹)) ≤ 1 / 2 := by
  let t := s.erase 2
  by_cases ht : t = ∅
  · have hs2 : s ⊆ {2} := by
      intro p hp
      simp only [Finset.mem_singleton]
      by_contra hp2
      have : p ∈ t := Finset.mem_erase.mpr ⟨hp2, hp⟩
      simpa [ht] using this
    calc
      (∑ p ∈ s, (((p : ℝ) ^ 2)⁻¹)) ≤
          ∑ p ∈ ({2} : Finset ℕ), (((p : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs2 (by
          intro p hp hps
          positivity)
      _ ≤ 1 / 2 := by norm_num
  · have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
    let K := t.max' htne / 2
    let B := Finset.Icc 1 K
    let f : ℕ → ℝ := fun p ↦ (((p : ℝ) ^ 2)⁻¹)
    let g : ℕ → ℝ := fun j ↦ (1 : ℝ) / (4 * j * (j + 1))
    have htPrime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hs p (Finset.mem_of_mem_erase hp)
    have htOdd : ∀ p ∈ t, Odd p := by
      intro p hp
      exact (htPrime p hp).odd_of_ne_two (Finset.mem_erase.mp hp).1
    have heB : ∀ p ∈ t, p / 2 ∈ B := by
      intro p hp
      have hp3 : 3 ≤ p := by
        have hp2 := (htPrime p hp).two_le
        have hpne := (Finset.mem_erase.mp hp).1
        omega
      have hpmax : p ≤ t.max' htne := Finset.le_max' t p hp
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hpmax⟩
    have heinj : ∀ p ∈ t, ∀ q ∈ t, p / 2 = q / 2 → p = q := by
      intro p hp q hq hpq
      have hpForm : 2 * (p / 2) + 1 = p :=
        Nat.two_mul_div_two_add_one_of_odd (htOdd p hp)
      have hqForm : 2 * (q / 2) + 1 = q :=
        Nat.two_mul_div_two_add_one_of_odd (htOdd q hq)
      omega
    have hterm : ∀ p ∈ t, f p ≤ g (p / 2) := by
      intro p hp
      let j := p / 2
      have hj : 0 < j := by
        dsimp [j]
        have hp3 : 3 ≤ p := by
          have hp2 := (htPrime p hp).two_le
          have hpne := (Finset.mem_erase.mp hp).1
          omega
        omega
      have hpForm : 2 * j + 1 = p := by
        dsimp [j]
        exact Nat.two_mul_div_two_add_one_of_odd (htOdd p hp)
      have hdenNat : 4 * j * (j + 1) ≤ p ^ 2 := by
        rw [← hpForm]
        ring_nf
        omega
      have hden : (4 : ℝ) * j * (j + 1) ≤ (p : ℝ) ^ 2 := by
        exact_mod_cast hdenNat
      have hleft : (0 : ℝ) < 4 * j * (j + 1) := by positivity
      have hright : (0 : ℝ) < (p : ℝ) ^ 2 := by
        exact sq_pos_of_pos (by exact_mod_cast (htPrime p hp).pos)
      have hinv : ((p : ℝ) ^ 2)⁻¹ ≤
          ((4 : ℝ) * j * (j + 1))⁻¹ :=
        (inv_le_inv₀ hright hleft).2 hden
      simpa [f, g, j, one_div] using hinv
    have hodd : (∑ p ∈ t, (((p : ℝ) ^ 2)⁻¹)) ≤ 1 / 4 := by
      calc
        (∑ p ∈ t, (((p : ℝ) ^ 2)⁻¹)) ≤
            ∑ j ∈ B, (1 : ℝ) / (4 * j * (j + 1)) := by
          exact finset_sum_le_sum_of_inj (fun p ↦ p / 2)
            (by
              intro j hj
              positivity) heB heinj hterm
        _ = (K : ℝ) / (4 * (K + 1)) := by
          exact sum_Icc_one_div_four_mul_mul_succ K
        _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (K + 1))
            (by norm_num : (0 : ℝ) < 4)]
          push_cast
          nlinarith
    by_cases htwo : 2 ∈ s
    · rw [← Finset.sum_erase_add _ _ htwo]
      change (∑ p ∈ t, (((p : ℝ) ^ 2)⁻¹)) + ((2 : ℝ) ^ 2)⁻¹ ≤ 1 / 2
      norm_num
      linarith
    · have : t = s := Finset.erase_eq_self.mpr htwo
      simpa [this] using hodd.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)

private lemma one_sub_sum_le_prod_one_sub
    {s : Finset ℕ} {a : ℕ → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hai0 := ha0 i (by simp)
      have hai1 := ha1 i (by simp)
      have hs0 : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg (fun j hj ↦ ha0 j (by simp [hj]))
      have hih := ih (fun j hj ↦ ha0 j (by simp [hj]))
        (fun j hj ↦ ha1 j (by simp [hj]))
      calc
        1 - (a i + ∑ j ∈ s, a j) ≤
            (1 - a i) * (1 - ∑ j ∈ s, a j) := by nlinarith
        _ ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hai1)

private lemma primeFactors_squareEulerProduct_half_lower (n : ℕ) :
    1 / 2 ≤ ∏ p ∈ n.primeFactors, (1 - (((p : ℝ) ^ 2)⁻¹)) := by
  have hsum := sum_prime_inv_sq_le_half n.primeFactors
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
  have hprod := one_sub_sum_le_prod_one_sub
    (s := n.primeFactors) (a := fun p ↦ (((p : ℝ) ^ 2)⁻¹))
    (by
      intro p hp
      positivity)
    (by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hp0 : (0 : ℝ) < p := by positivity
      rw [inv_le_one₀ (sq_pos_of_pos hp0)]
      nlinarith)
  linarith

private lemma prod_one_add_inv_eq_ratio_mul_squareEuler
    {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹)) =
      ((n : ℝ) / Nat.totient n) *
        ∏ p ∈ n.primeFactors, (1 - (((p : ℝ) ^ 2)⁻¹)) := by
  rw [Erdos4.cofactor_ratio_eq_primeFactors_product n hn.ne',
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hpPrime.ne_one)
  field_simp [hp0, hp1]
  ring

/-- The sharper reciprocal-divisor mass used by the controlled cap. -/
theorem totientRatio_half_le_sum_divisors_inv
    {n : ℕ} (hn : 0 < n) :
    (1 / 2 : ℝ) * ((n : ℝ) / Nat.totient n) ≤
      ∑ u ∈ n.divisors, (u : ℝ)⁻¹ := by
  let P := ∏ p ∈ n.primeFactors, p
  have hPdvd : P ∣ n := Nat.prod_primeFactors_dvd n
  have hP0 : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hPsq : Squarefree P := by
    dsimp [P]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      change IsRelPrime p q
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).squarefree
  have hPpf : P.primeFactors = n.primeFactors := by
    dsimp [P]
    exact Nat.primeFactors_prod
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
  have hEuler :
      (∑ d ∈ P.divisors, (d : ℝ)⁻¹) =
        ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) := by
    rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hPsq,
      Finset.sum_image (Erdos387.prod_primeFactorSubsets_injOn P),
      hPpf, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    push_cast
    exact (Finset.prod_inv_distrib (s := T) (fun p : ℕ ↦ (p : ℝ))).symm
  have hsub : P.divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn.ne' hPdvd
  have hsumle : (∑ d ∈ P.divisors, (d : ℝ)⁻¹) ≤
      ∑ d ∈ n.divisors, (d : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro d hd hnot
      positivity)
  rw [hEuler] at hsumle
  have hprod := primeFactors_squareEulerProduct_half_lower n
  have hratio0 : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  rw [prod_one_add_inv_eq_ratio_mul_squareEuler hn] at hsumle
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hprod hratio0).trans hsumle

/-- Retaining the elementary half of the reciprocal-divisor mass improves
the direct-prime count to two fifths of its natural main scale. -/
theorem two_fifths_ratio_y_div_log_le_primeStructuredTestSet_card
    {n y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (19 / 20 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 20 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (100 * Real.log (y : ℝ))) :
    (2 / 5 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
        Real.log (y : ℝ)) ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hratio0 : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  have hfull := totientRatio_half_le_sum_divisors_inv hn
  have hlarge := sum_large_divisors_inv_le n U
  rw [sum_divisors_inv_eq_bounded_add_large (U := U) hn.ne'] at hfull
  have hrecip :
      (12 / 25 : ℝ) * ((n : ℝ) / Nat.totient n) ≤
        ∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹ := by
    nlinarith
  have hfibre : ∀ u ∈ boundedTargetDivisors n U,
      (361 / 400 : ℝ) *
          (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) ≤
        ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := by
    intro u hu
    have hcomp := nineteen_twentieth_y_log_inv_le_dyadic_ratio
      (boundedTargetDivisor_pos hu) (hsmall u hu)
    have hp := hPNT _ (hscale u hu)
    calc
      (361 / 400 : ℝ) *
            (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) =
          (19 / 20 : ℝ) * ((19 / 20 : ℝ) *
            (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹)) := by ring
      _ ≤ (19 / 20 : ℝ) * (((y / u : ℕ) : ℝ) /
            Real.log ((y / u : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcomp (by norm_num)
      _ ≤ ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := hp
  have hmain :
      (41 / 100 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
          Real.log (y : ℝ)) ≤
        ∑ u ∈ boundedTargetDivisors n U,
          ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := by
    calc
      (41 / 100 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
            Real.log (y : ℝ)) ≤
          (361 / 400 : ℝ) * ((y : ℝ) / Real.log (y : ℝ)) *
            ((12 / 25 : ℝ) * ((n : ℝ) / Nat.totient n)) := by
        have hbase : 0 ≤ ((n : ℝ) / Nat.totient n) * (y : ℝ) /
            Real.log (y : ℝ) := by positivity
        calc
          (41 / 100 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
                Real.log (y : ℝ)) ≤
              ((361 / 400 : ℝ) * (12 / 25 : ℝ)) *
                (((n : ℝ) / Nat.totient n) * (y : ℝ) /
                  Real.log (y : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hbase
          _ = _ := by ring
      _ ≤ (361 / 400 : ℝ) * ((y : ℝ) / Real.log (y : ℝ)) *
            (∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ∑ u ∈ boundedTargetDivisors n U,
            (361 / 400 : ℝ) *
              (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) := by
        simp [Finset.mul_sum]
        ring
      _ ≤ ∑ u ∈ boundedTargetDivisors n U,
          ((Erdos446.dyadicPrimes (y / u)).card : ℝ) :=
        Finset.sum_le_sum fun u hu ↦ hfibre u hu
  have hsum :
      (∑ u ∈ boundedTargetDivisors n U,
        (((Erdos446.dyadicPrimes (y / u)).card : ℝ) -
          n.primeFactors.card)) ≤
        ((primeStructuredTestSet n y U).card : ℝ) := by
    rw [card_primeStructuredTestSet]
    push_cast
    apply Finset.sum_le_sum
    intro u hu
    exact dyadicPrimes_card_cast_sub_primeFactors_le_primeStructured n _
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have herr' : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      (1 / 100 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
        Real.log (y : ℝ)) := by
    convert herror using 1 <;> ring
  linarith

/-- Exact count interface for the smaller controlled cap. -/
theorem initialMissingEulerProduct_mul_y_div_twelve_le_primeStructuredTestSet_card
    {n h y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (19 / 20 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 20 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (100 * Real.log (y : ℝ)))
    (hMertensLog :
      5 * initialMissingEulerProduct n h * Real.log (y : ℝ) ≤
        24 * ((n : ℝ) / Nat.totient n)) :
    initialMissingEulerProduct n h * (y : ℝ) / 12 ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hcount := two_fifths_ratio_y_div_log_le_primeStructuredTestSet_card
    hn hU hPNT hscale hsmall htail herror
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hy0 : (0 : ℝ) ≤ y := by positivity
  calc
    initialMissingEulerProduct n h * (y : ℝ) / 12 ≤
        (2 / 5 : ℝ) * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
          Real.log (y : ℝ)) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 12)]
      rw [show (2 / 5 : ℝ) *
          (((n : ℝ) / Nat.totient n) * (y : ℝ) /
            Real.log (y : ℝ)) * 12 =
          (24 / 5 : ℝ) * ((n : ℝ) / Nat.totient n) *
            (y : ℝ) / Real.log (y : ℝ) by ring]
      rw [le_div_iff₀ hlogY]
      nlinarith [mul_le_mul_of_nonneg_right hMertensLog hy0]
    _ ≤ ((primeStructuredTestSet n y U).card : ℝ) := hcount

end Erdos360

#print axioms Erdos360.totientRatio_half_le_sum_divisors_inv
#print axioms Erdos360.two_fifths_ratio_y_div_log_le_primeStructuredTestSet_card
#print axioms Erdos360.initialMissingEulerProduct_mul_y_div_twelve_le_primeStructuredTestSet_card

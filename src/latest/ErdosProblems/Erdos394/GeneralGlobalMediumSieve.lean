import ErdosProblems.Erdos394.CardMediumDecomposition

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global finite medium-prime sieve for a general block length
-/

open Nat Finset

namespace Erdos394

/-- Explicit polynomial factor in the root-box least-hit mean. -/
def generalRootMeanFactor (K r : ℕ) : ℝ :=
  2 + (r : ℝ) *
    (2 + ((((80 : ℝ) * ((K * K - 1 : ℕ) : ℝ) +
      160 * (K : ℝ)) + 2) + 88) * ((K : ℝ) + 1))

lemma generalRootMeanFactor_nonneg (K r : ℕ) :
    0 ≤ generalRootMeanFactor K r := by
  unfold generalRootMeanFactor
  positivity

lemma generalRootMeanFactor_mono {K r s : ℕ} (hrs : r ≤ s) :
    generalRootMeanFactor K r ≤ generalRootMeanFactor K s := by
  unfold generalRootMeanFactor
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  gcongr

/-- Product form of the general root weight. -/
theorem prod_inv_K_prime_eq (K : ℕ) (T : Finset ℕ)
    (hK : 0 < K) (hprime : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) =
      1 / ((primeProduct T : ℝ) * ((K ^ T.card : ℕ) : ℝ)) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ z ∈ T, z.Prime := by
        intro z hz
        exact hprime z (Finset.mem_insert_of_mem hz)
      rw [Finset.prod_insert hpT, ih hTprime, primeProduct_insert hpT,
        Finset.card_insert_of_notMem hpT, pow_succ]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      have hqR : (primeProduct T : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr
          (fun z hz ↦ (hTprime z hz).ne_zero))
      push_cast
      field_simp

/-- If every selected prime exceeds `K`, the root count `K^|T|` does not
exceed their product. -/
theorem pow_card_le_primeProduct_of_le
    (K : ℕ) (T : Finset ℕ) (hKp : ∀ p ∈ T, K ≤ p) :
    K ^ T.card ≤ primeProduct T := by
  unfold primeProduct
  calc
    K ^ T.card = ∏ _p ∈ T, K := by simp
    _ ≤ ∏ p ∈ T, p := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · exact hKp

/-- For the empty selected subset, the universal bound `t_K(m)≤m` and the
ordinary Brun progression estimate replace the nonempty root-box theorem. -/
theorem tKMul_emptySelected_le_brun
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (M R : ℕ) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tKMulCoprimeSiftedMass K P M 1 ≤
      (M : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        (truncatedSubsets P R).card * (2 * (M : ℝ)) := by
  have hsieve := primeSiftedMass_le_two_product_add_error
    P hprime (M := M) (q := 1) (h := 0) (R := R)
    (by omega) (by omega) (fun p hp ↦ Nat.coprime_one_left p) hR htail
  have hmass : tKMulCoprimeSiftedMass K P M 1 ≤
      siftedMass (residueClassUpTo M 1 0)
        (fun m : ℕ ↦ (m : ℝ)) (badPrimeSet P) := by
    unfold tKMulCoprimeSiftedMass siftedMass residueClassUpTo
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro m hm
    by_cases hmpos : 0 < m
    · rw [dif_pos hmpos]
      have hcop : m.Coprime 1 := Nat.coprime_one_right m
      rw [dif_pos hcop]
      by_cases hsift : badPrimeSet P m = ∅
      · rw [if_pos hsift, if_pos hsift]
        simp only [Nat.mod_one, if_pos rfl, Nat.mul_one]
        exact_mod_cast t_le_self hK hmpos
      · rw [if_neg hsift, if_neg hsift]
        simp
    · rw [dif_neg hmpos]
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
      subst m
      simp
  apply hmass.trans
  exact hsieve.trans_eq (by ring)

/-- Fixed selected-subset estimate in the form needed for Euler summation.
The hypotheses are bounded globally by a cardinality cutoff `S`. -/
theorem tKMul_boundedPrimeSubset_le_main_add_error
    (K Z : ℕ) (P T : Finset ℕ) (S X R y : ℕ)
    (hK : 1 < K) (hZ : 1 ≤ Z) (hTP : T ⊆ P)
    (hTcard : T.card ≤ S)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P, 2 * S * K ^ S ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * S * K ≤ p - 1)
    (hZsize : 8 * S * (K * K - 1) ≤ Z)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
        (primeProduct T) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (generalRootMeanFactor K T.card *
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        (generalRootMeanFactor K T.card *
          (((primeProduct T).totient : ℝ) /
            ((K ^ T.card : ℕ) : ℝ))) := by
  let q := primeProduct T
  let M := X / q
  let Vc := localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))
  let Vt := localEulerProduct T (fun p ↦ 1 / (p : ℝ))
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let d : ℝ := ((K ^ T.card : ℕ) : ℝ)
  let W : ℝ := generalRootMeanFactor K T.card
  let N : ℝ := ((truncatedSubsets (P \ T) R).card : ℝ)
  let Nmax : ℝ := (((R + 1) * y ^ R : ℕ) : ℝ)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ hprime p (hTP hp)
  have hcompPrime : ∀ p ∈ P \ T, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_sdiff.mp hp).1
  have htailComp := factorial_tail_le_localEulerProduct_sdiff
    P T hTP R htail hprime
  have hNnat : (truncatedSubsets (P \ T) R).card ≤ (R + 1) * y ^ R := by
    apply card_truncatedSubsets_le (P \ T) R y hy
    exact (Finset.card_le_card Finset.sdiff_subset).trans hPy
  have hN : N ≤ Nmax := by
    dsimp [N, Nmax]
    exact_mod_cast hNnat
  have hW0 : 0 ≤ W := generalRootMeanFactor_nonneg K T.card
  have hV0 : 0 ≤ V := by
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  by_cases hTempty : T = ∅
  · subst T
    have hs := tKMul_emptySelected_le_brun K (by omega) P hprime X R hR htail
    have hNfull : ((truncatedSubsets P R).card : ℝ) ≤ Nmax := by
      dsimp [Nmax]
      exact_mod_cast card_truncatedSubsets_le P R y hy hPy
    calc
      tKMulCoprimeSiftedMass K (P \ ∅) (X / primeProduct ∅)
          (primeProduct ∅) = tKMulCoprimeSiftedMass K P X 1 := by simp
      _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
          (truncatedSubsets P R).card * (2 * (X : ℝ)) := hs
      _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (generalRootMeanFactor K (∅ : Finset ℕ).card *
            ∏ p ∈ (∅ : Finset ℕ), (1 / ((K : ℝ) * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (generalRootMeanFactor K (∅ : Finset ℕ).card *
            (((primeProduct (∅ : Finset ℕ)).totient : ℝ) /
              ((K ^ (∅ : Finset ℕ).card : ℕ) : ℝ))) := by
        simp only [Finset.card_empty, Finset.prod_empty, primeProduct_empty,
          Nat.totient_one, pow_zero, Nat.cast_one, div_one, mul_one]
        unfold generalRootMeanFactor
        norm_num
        dsimp [Nmax] at hNfull
        dsimp [V] at hV0
        have hA0 : 0 ≤ (X : ℝ) ^ 2 *
            localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by positivity
        have hE : ((truncatedSubsets P R).card : ℝ) * (2 * (X : ℝ)) ≤
            (((R + 1) * y ^ R : ℕ) : ℝ) * (2 * (X : ℝ)) :=
          mul_le_mul_of_nonneg_right hNfull (by positivity)
        have hE0 : 0 ≤ (((R + 1) * y ^ R : ℕ) : ℝ) *
            (2 * (X : ℝ)) := by positivity
        have hAle : (X : ℝ) ^ 2 *
            localEulerProduct P (fun p ↦ 1 / (p : ℝ)) ≤
          ((X : ℝ) ^ 2 *
            localEulerProduct P (fun p ↦ 1 / (p : ℝ))) * 2 := by
          nlinarith
        have hEle : (((R + 1) * y ^ R : ℕ) : ℝ) * (2 * (X : ℝ)) ≤
            2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) * 2 := by
          nlinarith
        simpa [one_div] using (_root_.add_le_add hAle (hE.trans hEle))
  · have hTpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTempty)
    have hqpos : 0 < q := by
      dsimp [q, primeProduct]
      exact Finset.prod_pos fun p hp ↦ (hTprime p hp).pos
    have hTarea : ∀ p ∈ T, 2 * T.card * K ^ T.card ≤ p - 1 := by
      intro p hp
      have hpow : K ^ T.card ≤ K ^ S := Nat.pow_le_pow_right (by omega) hTcard
      have hmul : 2 * T.card * K ^ T.card ≤ 2 * S * K ^ S := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hTcard) hpow
      exact hmul.trans (hareaSize p (hTP hp))
    have hTrat : ∀ p ∈ T, 4 * T.card * K ≤ p - 1 := by
      intro p hp
      exact (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 4 hTcard)).trans
        (hratSize p (hTP hp))
    have hTZ : 8 * T.card * (K * K - 1) ≤ Z :=
      (Nat.mul_le_mul_right (K * K - 1)
        (Nat.mul_le_mul_left 8 hTcard)).trans hZsize
    have hRq : K ^ T.card ≤ primeProduct T :=
      pow_card_le_primeProduct_of_le K T
        (fun p hp ↦ (hKp p (hTP hp)).le)
    have hcopComp : ∀ p ∈ P \ T, q.Coprime p := by
      intro p hp
      exact primeProduct_coprime_of_not_mem hTP hprime
        (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
    have hsieve := tKMulCoprimeSiftedMass_le_brun K Z (P \ T) T M R
      hK hZ hTpos hTprime
      (fun p hp ↦ hKp p (hTP hp))
      (fun p hp ↦ hK2p p (hTP hp))
      (fun p hp ↦ hlarge p (hTP hp))
      (fun p hp ↦ hZp p (hTP hp))
      (fun p hp ↦ hZ2p p (hTP hp))
      hTarea hTrat hTZ hRq hcompPrime hcopComp hR htailComp
    have htot : ((q.totient : ℕ) : ℝ) = (q : ℝ) * Vt := by
      dsimp [q, Vt]
      exact totient_primeProduct_real T hTprime
    have hprod : (∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) =
        1 / ((q : ℝ) * d) := by
      dsimp [q, d]
      exact prod_inv_K_prime_eq K T (by omega) hTprime
    have hM : (M : ℝ) ≤ (X : ℝ) / (q : ℝ) := by
      dsimp [M]
      exact Nat.cast_div_le
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hM2 : (M : ℝ) ^ 2 ≤ ((X : ℝ) / (q : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hM0 hM 2
    have hMq : (M : ℝ) * (q : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self X q)
    have hVsplit : Vt * Vc = V :=
      localEulerProduct_mul_sdiff P T hTP _
    have hdpos : 0 < d := by dsimp [d]; positivity
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hmain :
        (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) * (q.totient : ℝ) *
            (W * ((q : ℝ) / d)) ≤
          (X : ℝ) ^ 2 * V *
            (W * ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) := by
      have hscale : 0 ≤ V * W * (q : ℝ) / d := by positivity
      calc
        (((M : ℝ) ^ 2 / (q : ℝ)) * Vc) * (q.totient : ℝ) *
            (W * ((q : ℝ) / d)) =
            (M : ℝ) ^ 2 * (V * W * (q : ℝ) / d) := by
          rw [htot, ← hVsplit]
          field_simp
        _ ≤ ((X : ℝ) / (q : ℝ)) ^ 2 *
            (V * W * (q : ℝ) / d) :=
          mul_le_mul_of_nonneg_right hM2 hscale
        _ = (X : ℝ) ^ 2 * V *
            (W * ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) := by
          rw [hprod]
          field_simp
    have herr :
        (N * (2 * (M : ℝ))) * (q.totient : ℝ) *
            (W * ((q : ℝ) / d)) ≤
          2 * (X : ℝ) * Nmax *
            (W * ((q.totient : ℝ) / d)) := by
      have hNM : N * ((M : ℝ) * (q : ℝ)) ≤ Nmax * (X : ℝ) :=
        mul_le_mul hN hMq (by positivity) (by positivity)
      have hscale : 0 ≤ 2 * ((q.totient : ℝ) * W / d) := by positivity
      calc
        (N * (2 * (M : ℝ))) * (q.totient : ℝ) *
            (W * ((q : ℝ) / d)) =
          (N * ((M : ℝ) * (q : ℝ))) *
            (2 * ((q.totient : ℝ) * W / d)) := by ring
        _ ≤ (Nmax * (X : ℝ)) *
            (2 * ((q.totient : ℝ) * W / d)) :=
          mul_le_mul_of_nonneg_right hNM hscale
        _ = 2 * (X : ℝ) * Nmax *
            (W * ((q.totient : ℝ) / d)) := by ring
    rw [← totient_primeProduct_eq_primeUnitCount T hTprime] at hsieve
    dsimp [q, M, Vc, Vt, V, d, W, N, Nmax] at hsieve ⊢
    calc
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) ≤
        (((((X / primeProduct T : ℕ) : ℝ) ^ 2 /
            (primeProduct T : ℝ)) *
              localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) +
            ((truncatedSubsets (P \ T) R).card : ℝ) *
              (2 * ((X / primeProduct T : ℕ) : ℝ))) *
            ((primeProduct T).totient : ℝ)) *
          (generalRootMeanFactor K T.card *
            ((primeProduct T : ℝ) / ((K ^ T.card : ℕ) : ℝ))) := hsieve
      _ = (((((X / primeProduct T : ℕ) : ℝ) ^ 2 /
            (primeProduct T : ℝ)) *
              localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))) *
            ((primeProduct T).totient : ℝ) *
              (generalRootMeanFactor K T.card *
                ((primeProduct T : ℝ) / ((K ^ T.card : ℕ) : ℝ)))) +
          ((((truncatedSubsets (P \ T) R).card : ℝ) *
              (2 * ((X / primeProduct T : ℕ) : ℝ))) *
            ((primeProduct T).totient : ℝ) *
              (generalRootMeanFactor K T.card *
                ((primeProduct T : ℝ) / ((K ^ T.card : ℕ) : ℝ)))) := by ring
      _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (generalRootMeanFactor K T.card *
            ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (generalRootMeanFactor K T.card *
            (((primeProduct T).totient : ℝ) /
              ((K ^ T.card : ℕ) : ℝ))) :=
        add_le_add hmain herr

/-- Exact powerset expansion for the `1/(Kp)` root weights. -/
theorem sum_powerset_inv_K_prime_products (K : ℕ) (P : Finset ℕ) :
    (∑ T ∈ P.powerset,
      ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) =
      ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ))) :=
  sum_powerset_prod_eq_prod_one_add P
    (fun p ↦ 1 / ((K : ℝ) * (p : ℝ)))

/-- Summing the polynomial root factor over bounded-cardinality subsets costs
only its value at the cutoff. -/
theorem sum_bounded_root_main_weights_le
    (K : ℕ) (P : Finset ℕ) (S : ℕ) :
    (∑ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
        ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) ≤
      generalRootMeanFactor K S *
        ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ))) := by
  have hterm : ∀ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ))) ≤
        generalRootMeanFactor K S *
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ))) := by
    intro T hT
    apply mul_le_mul_of_nonneg_right
      (generalRootMeanFactor_mono (Finset.mem_filter.mp hT).2)
    positivity
  calc
    (∑ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
        ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) ≤
      ∑ T ∈ boundedPrimeSubsets P S,
        generalRootMeanFactor K S *
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ))) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ T ∈ P.powerset,
        generalRootMeanFactor K S *
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro T hT hnot
      exact mul_nonneg (generalRootMeanFactor_nonneg K S) (by positivity)
    _ = generalRootMeanFactor K S *
        ∑ T ∈ P.powerset,
          ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ))) := by
      rw [Finset.mul_sum]
    _ = generalRootMeanFactor K S *
        ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ))) := by
      rw [sum_powerset_inv_K_prime_products]

/-- A bounded-cardinality prime subset has product at most `y^S`. -/
theorem boundedPrimeSubsets_subset_smallPrimeSubsets
    (P : Finset ℕ) (S y : ℕ) (hy : 1 ≤ y)
    (hPy : ∀ p ∈ P, p ≤ y) :
    boundedPrimeSubsets P S ⊆ smallPrimeSubsets P (y ^ S) := by
  intro T hT
  have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hcard := (Finset.mem_filter.mp hT).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr hTP, ?_⟩
  exact (primeProduct_le_pow_card T (fun p hp ↦ hPy p (hTP hp))).trans
    (Nat.pow_le_pow_right (by omega) hcard)

/-- Crude but uniform sum of the root-weighted totients over all selected
subsets of cardinality at most `S`. -/
theorem sum_bounded_root_error_weights_le
    (K : ℕ) (hK : 0 < K) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (S y : ℕ) (hy : 1 ≤ y)
    (hPy : ∀ p ∈ P, p ≤ y) :
    (∑ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
        (((primeProduct T).totient : ℝ) /
          ((K ^ T.card : ℕ) : ℝ))) ≤
      generalRootMeanFactor K S *
        ((y ^ S : ℕ) : ℝ) * ((y ^ S + 1 : ℕ) : ℝ) := by
  let Q := y ^ S
  have hsub : boundedPrimeSubsets P S ⊆ smallPrimeSubsets P Q :=
    boundedPrimeSubsets_subset_smallPrimeSubsets P S y hy hPy
  have hcardNat : (boundedPrimeSubsets P S).card ≤ Q + 1 :=
    (Finset.card_le_card hsub).trans (card_smallPrimeSubsets_le P hprime Q)
  have hterm : ∀ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
          (((primeProduct T).totient : ℝ) /
            ((K ^ T.card : ℕ) : ℝ)) ≤
        generalRootMeanFactor K S * (Q : ℝ) := by
    intro T hT
    have hWS := generalRootMeanFactor_mono (K := K)
      (Finset.mem_filter.mp hT).2
    have hqQ : primeProduct T ≤ Q :=
      (Finset.mem_filter.mp (hsub hT)).2
    have hphi : (primeProduct T).totient ≤ primeProduct T := Nat.totient_le _
    have hden : (1 : ℝ) ≤ ((K ^ T.card : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow T.card K hK
    have hfrac : (((primeProduct T).totient : ℝ) /
        ((K ^ T.card : ℕ) : ℝ)) ≤ (Q : ℝ) := by
      have hdenpos : (0 : ℝ) < ((K ^ T.card : ℕ) : ℝ) := by positivity
      have hphiQ : ((primeProduct T).totient : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast hphi.trans hqQ
      have hphi0 : (0 : ℝ) ≤ (primeProduct T).totient := by positivity
      calc
        ((primeProduct T).totient : ℝ) /
            ((K ^ T.card : ℕ) : ℝ) ≤
          ((primeProduct T).totient : ℝ) := by
            apply (div_le_iff₀ hdenpos).2
            nlinarith
        _ ≤ (Q : ℝ) := hphiQ
    exact mul_le_mul hWS hfrac (by positivity)
      (generalRootMeanFactor_nonneg K S)
  calc
    (∑ T ∈ boundedPrimeSubsets P S,
      generalRootMeanFactor K T.card *
        (((primeProduct T).totient : ℝ) /
          ((K ^ T.card : ℕ) : ℝ))) ≤
      ∑ _T ∈ boundedPrimeSubsets P S,
        generalRootMeanFactor K S * (Q : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (generalRootMeanFactor K S * (Q : ℝ)) *
        (boundedPrimeSubsets P S).card := by simp [mul_comm]
    _ ≤ (generalRootMeanFactor K S * (Q : ℝ)) * (Q + 1 : ℕ) := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hcardNat
      · exact mul_nonneg (generalRootMeanFactor_nonneg K S) (by positivity)
    _ = generalRootMeanFactor K S *
        ((y ^ S : ℕ) : ℝ) * ((y ^ S + 1 : ℕ) : ℝ) := by
      rfl

/-- Sum the fixed-subset root-box/Brun estimate over all selected subsets with
cardinality at most `S`. -/
theorem sum_boundedPrimeSubsets_tKMul_le
    (K Z : ℕ) (P : Finset ℕ) (S X R y : ℕ)
    (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P, 2 * S * K ^ S ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * S * K ≤ p - 1)
    (hZsize : 8 * S * (K * K - 1) ≤ Z)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) (hPupper : ∀ p ∈ P, p ≤ y)
    (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ T ∈ boundedPrimeSubsets P S,
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (generalRootMeanFactor K S *
          ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        (generalRootMeanFactor K S * ((y ^ S : ℕ) : ℝ) *
          ((y ^ S + 1 : ℕ) : ℝ)) := by
  have hterm : ∀ T ∈ boundedPrimeSubsets P S,
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
          (primeProduct T) ≤
        (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (generalRootMeanFactor K T.card *
            ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (generalRootMeanFactor K T.card *
            (((primeProduct T).totient : ℝ) /
              ((K ^ T.card : ℕ) : ℝ))) := by
    intro T hT
    have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hTcard := (Finset.mem_filter.mp hT).2
    exact tKMul_boundedPrimeSubset_le_main_add_error K Z P T S X R y
      hK hZ hTP hTcard hprime hKp hK2p hlarge hZp hZ2p
      hareaSize hratSize hZsize hy hPy hR htail
  calc
    (∑ T ∈ boundedPrimeSubsets P S,
      tKMulCoprimeSiftedMass K (P \ T) (X / primeProduct T)
        (primeProduct T)) ≤
      ∑ T ∈ boundedPrimeSubsets P S,
        ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
          (generalRootMeanFactor K T.card *
            ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) +
        2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
          (generalRootMeanFactor K T.card *
            (((primeProduct T).totient : ℝ) /
              ((K ^ T.card : ℕ) : ℝ)))) := Finset.sum_le_sum hterm
    _ = (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (∑ T ∈ boundedPrimeSubsets P S,
          generalRootMeanFactor K T.card *
            ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        (∑ T ∈ boundedPrimeSubsets P S,
          generalRootMeanFactor K T.card *
            (((primeProduct T).totient : ℝ) /
              ((K ^ T.card : ℕ) : ℝ))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (generalRootMeanFactor K S *
          ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        (generalRootMeanFactor K S * ((y ^ S : ℕ) : ℝ) *
          ((y ^ S + 1 : ℕ) : ℝ)) := by
      apply _root_.add_le_add
      · apply mul_le_mul_of_nonneg_left
          (sum_bounded_root_main_weights_le K P S)
        have hV0 : 0 ≤ localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
          apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
          · intro p hp; positivity
          · intro p hp
            have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
            exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
        positivity
      · apply mul_le_mul_of_nonneg_left
          (sum_bounded_root_error_weights_le K (by omega) P hprime S y hy hPupper)
        positivity

/-- Fully finite cardinality-truncated medium-prime sieve for a general block
length. -/
theorem finite_general_card_medium_sieve_bound
    (K Z : ℕ) (P : Finset ℕ) (S X R y z : ℕ)
    (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : z ≠ 0) (hzy : z ≤ y)
    (hPinterval : ∀ p ∈ P, z < p ∧ p ≤ y)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p)
    (hareaSize : ∀ p ∈ P, 2 * S * K ^ S ≤ p - 1)
    (hratSize : ∀ p ∈ P, 4 * S * K ≤ p - 1)
    (hZsize : 8 * S * (K * K - 1) ≤ Z)
    (hy : 1 ≤ y) (hPy : P.card ≤ y) (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ))) :
    (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) ≤
      (X : ℝ) ^ 2 / (z : ℝ) +
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (S + 1) /
          ((S + 1).factorial : ℝ)) +
      ((X : ℝ) ^ 2 * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) *
        (generalRootMeanFactor K S *
          ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) +
      2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
        (generalRootMeanFactor K S * ((y ^ S : ℕ) : ℝ) *
          ((y ^ S + 1 : ℕ) : ℝ))) := by
  have hdecomp := finite_general_card_medium_decomposition
    K (by omega) P hprime (X := X) (S := S) (y := y) (z := z)
      hz hzy hPinterval
  have hfixed := sum_boundedPrimeSubsets_tKMul_le K Z P S X R y
    hK hZ hprime hKp hK2p hlarge hZp hZ2p hareaSize hratSize hZsize
    hy hPy (fun p hp ↦ (hPinterval p hp).2) hR htail
  linarith

end Erdos394

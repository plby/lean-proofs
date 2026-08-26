import ErdosProblems.Erdos380.SmallPrimeMoments

/-!
# Small-prime tails on the original prime-tuple space

One prime coordinate is averaged first, with the other coordinates frozen.
The bound remains uniform in their product and in the external coefficient.
-/

open scoped BigOperators Classical

namespace Erdos380

lemma finite_expect_subtype {Ω : Type*} (s : Finset Ω) (F : Ω → ℝ) :
    (𝔼 r : s, F r.1) = 𝔼 r ∈ s, F r := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
  rw [Finset.sum_coe_sort s F]

lemma tupleNaturalProduct_cons {k : ℕ} (s : Fin (k + 1) → Finset ℕ)
    (r : s 0) (f : ∀ i : Fin k, s i.succ) :
    tupleNaturalProduct s (Fin.cons r f) = r.1 * ∏ i, (f i).1 := by
  simp [tupleNaturalProduct, Fin.prod_univ_succ]

lemma primeTuple_expect_le_of_one_coordinate {k : ℕ}
    (s : Fin (k + 1) → Finset ℕ) (F : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hfirst : ∀ v : ℕ, (𝔼 r ∈ s 0, F (r * v)) ≤ K) :
    (𝔼 f : ∀ i, s i, F (tupleNaturalProduct s f)) ≤ K := by
  classical
  let e := Fin.consEquiv (fun i => s i)
  have heq : (𝔼 f : ∀ i, s i, F (tupleNaturalProduct s f)) =
      𝔼 rf : s 0 × (∀ i : Fin k, s i.succ), F (tupleNaturalProduct s (e rf)) :=
    (Fintype.expect_equiv e
      (fun rf => F (tupleNaturalProduct s (e rf)))
      (fun f => F (tupleNaturalProduct s f)) (fun _ => rfl)).symm
  rw [heq]
  have hprod (rf : s 0 × (∀ i : Fin k, s i.succ)) :
      tupleNaturalProduct s (e rf) = rf.1.1 * ∏ i, (rf.2 i).1 :=
    tupleNaturalProduct_cons s rf.1 rf.2
  simp_rw [hprod]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply finite_expect_le_of_nonneg _ _ hK
  intro f _
  change (𝔼 r : s 0, F (r.1 * ∏ i, (f i).1)) ≤ K
  rw [finite_expect_subtype (s 0) (fun r => F (r * ∏ i, (f i).1))]
  exact hfirst (∏ i, (f i).1)

lemma normalizedSmallPrimeMass_nonneg (t : Finset ℕ) {T : ℕ} (hT : 2 ≤ T)
    (c : ℕ) (h : ℤ) (r : ℕ) : 0 ≤ normalizedSmallPrimeMass t T c h r := by
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) hlogT.le)
  split_ifs <;> norm_num

lemma normalizedSmallPrimeMass_mul (t : Finset ℕ) (T c v r : ℕ) (h : ℤ) :
    normalizedSmallPrimeMass t T c h (r * v) =
      normalizedSmallPrimeMass t T (c * v) h r := by
  unfold normalizedSmallPrimeMass smallPrimeDivisibilityEvent
  rw [show c * (r * v) = c * v * r by ring]

theorem exists_uniform_smallPrime_tuple_moment :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ N : Fin 10 → ℕ,
      (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) →
      ∀ c : ℕ, ∀ h : ℤ, ∀ t : Finset ℕ,
      t ⊆ Nat.primesLE T → (∀ p ∈ t, ¬ (p : ℤ) ∣ h) →
      (𝔼 f : ∀ i, dyadicPrimes (N i),
        normalizedSmallPrimeMass t T c h (tupleNaturalProduct (fun i => dyadicPrimes (N i)) f) ^ 50) ≤ K := by
  obtain ⟨K, hK, T₀, hmoment⟩ := exists_uniform_smallPrime_fiftieth_moment
  refine ⟨K, hK, T₀, ?_⟩
  intro T hT N hlow hhigh c h t ht hth
  apply primeTuple_expect_le_of_one_coordinate (k := 9)
    (fun i => dyadicPrimes (N i)) (fun v => normalizedSmallPrimeMass t T c h v ^ 50) hK.le
  intro v
  simp_rw [normalizedSmallPrimeMass_mul]
  exact hmoment T hT (N 0) (hlow 0) (hhigh 0) (c * v) h t ht hth

/-- The small-prime contribution over any nonempty finite collection of
signed shifts has a `U^(-50)` tail, uniformly on the original ten-prime
sample space. -/
theorem exists_uniform_smallPrime_shift_sum_tail :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ N : Fin 10 → ℕ,
      (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) →
      ∀ c : ℕ, ∀ J : Finset ℤ, J.Nonempty → ∀ t : ℤ → Finset ℕ,
      (∀ h ∈ J, t h ⊆ Nat.primesLE T) →
      (∀ h ∈ J, ∀ p ∈ t h, ¬ (p : ℤ) ∣ h) →
      ∀ U : ℝ, 0 < U →
      ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (N i) =>
        (J.card : ℝ) * U ≤ ∑ h ∈ J,
          normalizedSmallPrimeMass (t h) T c h
            (tupleNaturalProduct (fun i => dyadicPrimes (N i)) f)).card : ℝ) /
        (Fintype.card (∀ i, dyadicPrimes (N i)) : ℝ) ≤ K / U ^ 50 := by
  obtain ⟨K, hK, T₁, hm⟩ := exists_uniform_smallPrime_tuple_moment
  refine ⟨K, hK, max 2 T₁, ?_⟩
  intro T hT N hlow hhigh c J hJ t ht hth U hU
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hmoment := hm T ((le_max_right _ _).trans hT) N hlow hhigh c
  simpa only [Finset.card_univ] using finite_sum_fiftieth_tail_le J hJ Finset.univ
    (fun h f => normalizedSmallPrimeMass (t h) T c h
      (tupleNaturalProduct (fun i => dyadicPrimes (N i)) f)) K
    (fun h _ f _ => normalizedSmallPrimeMass_nonneg (t h) hT2 c h _)
    (fun h hh => hmoment h (t h) (ht h hh) (hth h hh)) hU

end Erdos380
